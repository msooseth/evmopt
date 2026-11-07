import EvmOpt.Peephole

/-! Untrusted peephole proposals. Every proposal is re-validated by `check` in `pass`. -/

namespace EvmOpt
open EvmSemantics EvmSemantics.EVM

/-- Minimal big-endian bytes of `n` (`[]` for 0). -/
partial def natBytes (n : Nat) : List UInt8 :=
  if n = 0 then [] else natBytes (n / 256) ++ [(n % 256).toUInt8]

def push0Ok (f : Fork) : Bool := (Instr.push []).toOp.availableInFork f

/-- Cheapest PUSH of `v` available in `f`. -/
def pushOf (f : Fork) (v : UInt256) : Instr :=
  let bs := natBytes v.toNat
  if bs.isEmpty && !push0Ok f then .push [0] else .push bs

def pushedVal : Instr → Option UInt256
  | .push bs => if bs.length ≤ 32 then some (pushVal bs) else none
  | _ => none

def isPushOf (i : Instr) (n : Nat) : Bool := (pushedVal i).any (·.toNat == n)

def maxWord : Nat := UInt256.size - 1

def commutative (o : ArithOp) : Bool :=
  match o with
  | .ADD | .MUL | .AND | .OR | .XOR | .EQ => true
  | _ => false

def flipCmp : ArithOp → Option ArithOp
  | .LT => some .GT | .GT => some .LT | .SLT => some .SGT | .SGT => some .SLT
  | _ => none

/-- `c op X` is `X` (with `c` pushed on top of `X`). -/
def leftIdentity (o : ArithOp) (c : UInt256) : Bool :=
  match o with
  | .ADD | .OR | .XOR => c.toNat == 0
  | .MUL => c.toNat == 1
  | .AND => c.toNat == maxWord
  | .SHL | .SHR | .SAR => c.toNat == 0
  | _ => false

/-- `c op X` is `0`. -/
def leftZero (o : ArithOp) (c : UInt256) : Bool :=
  match o with
  | .MUL | .AND => c.toNat == 0
  | .GT => c.toNat == 0
  | _ => false

/-- `X op c` is `X` (`c` below `X` after the SWAP1). -/
def rightIdentity (o : ArithOp) (c : UInt256) : Bool :=
  match o with
  | .SUB => c.toNat == 0
  | .DIV => c.toNat == 1
  | _ => leftIdentity o c && commutative o

def selfResult (o : ArithOp) : Option (Option Nat) :=
  match o with
  | .AND | .OR => some none
  | .SUB | .XOR | .LT | .GT | .SLT | .SGT | .MOD => some (some 0)
  | .EQ => some (some 1)
  | _ => none

def ruleRaw (f : Fork) (b : Block) : Option (Nat × Block) :=
  match b with
  | .swap n :: .swap m :: _ => if n = m then some (2, []) else none
  | .dup _ :: .pop :: _ => some (2, [])
  | .push _ :: .pop :: _ => some (2, [])
  | .op o :: .pop :: _ => some (2, List.replicate o.arity .pop)
  | .op .NOT :: .op .NOT :: _ => some (2, [])
  | .op .ISZERO :: .op .ISZERO :: .op .ISZERO :: _ => some (3, [.op .ISZERO])
  | .dup ⟨0, _⟩ :: .op o :: _ =>
    match selfResult o with
    | some none => some (2, [])
    | some (some v) => some (2, [.pop, pushOf f (UInt256.ofNat v)])
    | none => none
  | .swap ⟨0, _⟩ :: .op o :: _ =>
    if commutative o then some (2, [.op o])
    else (flipCmp o).map fun o' => (2, [.op o'])
  | p1 :: p2 :: p3 :: .op o :: _ =>
    match pushedVal p1, pushedVal p2, pushedVal p3 with
    | some a, some b, some c =>
      if o.arity = 3 then some (4, [pushOf f (o.eval [c, b, a])]) else none
    | _, _, _ => none
  | p1 :: p2 :: .op o :: _ =>
    match pushedVal p1, pushedVal p2, p2 with
    | some a, some b, _ => if o.arity = 2 then some (3, [pushOf f (o.eval [b, a])]) else none
    | some c, none, .swap ⟨0, _⟩ =>
      if rightIdentity o c then some (3, [])
      else if o = .LT && c.toNat == 0 then some (3, [.pop, pushOf f (UInt256.ofNat 0)])
      else if o = .LT && c.toNat == 1 then some (3, [.op .ISZERO])
      else none
    | _, _, _ => none
  | p :: .op o :: _ =>
    match pushedVal p with
    | some a =>
      if o.arity = 1 then some (2, [pushOf f (o.eval [a])])
      else if leftIdentity o a then some (2, [])
      else if leftZero o a then some (2, [.pop, pushOf f (UInt256.ofNat 0)])
      else if o = .EQ && a.toNat == 0 then some (2, [.op .ISZERO])
      else if o = .GT && a.toNat == 1 then some (2, [.op .ISZERO])
      else none
    | none => none
  | _ => none

def pushMin (f : Fork) (b : Block) : Option (Nat × Block) :=
  match b with
  | .push bs :: _ =>
    match pushedVal (.push bs) with
    | some v => let p := pushOf f v; if p ≠ .push bs then some (1, [p]) else none
    | none => none
  | _ => none

def blockSize (b : Block) : Nat := (encode b).length

/-- At most one extra byte per 3 gas saved: solc uses e.g. `PUSH 0 NOT` deliberately for
    size, and folding it into a PUSH32 would cost far more in deployment than it saves. -/
def sizeOk (f : Fork) (old new : Block) : Bool :=
  blockSize new ≤ blockSize old + (cost f old - cost f new) / 3

def rule (f : Fork) (b : Block) : Option (Nat × Block) :=
  let ok := fun (kw : Nat × Block) => sizeOk f (b.take kw.1) kw.2
  ((ruleRaw f b).filter ok).orElse fun _ => (pushMin f b).filter ok

def peephole (f : Fork) (b : Block) : Block := passes f rule (2 * b.length + 2) b

theorem peephole_sound (f : Fork) (σ : State) (b : Block) {stk r : List UInt256}
    (hl : stk.length ≤ 1024) (h : run f σ b stk = some r) :
    run f σ (peephole f b) stk = some r ∧ cost f (peephole f b) ≤ cost f b :=
  passes_sound f σ rule _ b hl h

end EvmOpt
