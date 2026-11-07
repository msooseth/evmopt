import EvmSemantics

theorem ByteArray.toList_loop_eq (bs : ByteArray) (i : Nat) (r : List UInt8) :
    ByteArray.toList.loop bs i r = r.reverse ++ bs.data.toList.drop i := by
  have hs : bs.data.toList.length = bs.size := Array.length_toList
  induction h : bs.size - i generalizing i r with
  | zero =>
    rw [ByteArray.toList.loop]
    have : ¬ i < bs.size := by omega
    simp only [this, if_false]
    rw [List.drop_eq_nil_of_le (by omega), List.append_nil]
  | succ n ih =>
    rw [ByteArray.toList.loop]
    have hi : i < bs.size := by omega
    simp only [hi, if_true]
    rw [ih (i + 1) _ (by omega)]
    rw [List.drop_eq_getElem_cons (show i < bs.data.toList.length by omega)]
    simp only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append]
    congr 2
    simp only [ByteArray.get!, Array.getElem_toList]
    exact getElem!_pos bs.data i hi

theorem ByteArray.toList_mk (l : List UInt8) : ByteArray.toList ⟨l.toArray⟩ = l := by
  simp [ByteArray.toList, ByteArray.toList_loop_eq]


namespace EvmOpt
open EvmSemantics EvmSemantics.EVM

/-- Pure word operations: pop `arity` words, push one result, no other effects.
    `EXP` is excluded because its gas depends on the exponent value. -/
inductive ArithOp
  | ADD | MUL | SUB | DIV | SDIV | MOD | SMOD | ADDMOD | MULMOD | SIGNEXTEND
  | LT | GT | SLT | SGT | EQ | ISZERO | AND | OR | XOR | NOT | BYTE | SHL | SHR | SAR | CLZ
  deriving DecidableEq, Repr, Inhabited, Ord, Hashable

namespace ArithOp

def toOp : ArithOp → Operation
  | ADD => .ADD | MUL => .MUL | SUB => .SUB | DIV => .DIV | SDIV => .SDIV | MOD => .MOD
  | SMOD => .SMOD | ADDMOD => .ADDMOD | MULMOD => .MULMOD | SIGNEXTEND => .SIGNEXTEND
  | LT => .LT | GT => .GT | SLT => .SLT | SGT => .SGT | EQ => .EQ | ISZERO => .ISZERO
  | AND => .AND | OR => .OR | XOR => .XOR | NOT => .NOT | BYTE => .BYTE | SHL => .SHL
  | SHR => .SHR | SAR => .SAR | CLZ => .CLZ

def byte : ArithOp → UInt8
  | ADD => 0x01 | MUL => 0x02 | SUB => 0x03 | DIV => 0x04 | SDIV => 0x05 | MOD => 0x06
  | SMOD => 0x07 | ADDMOD => 0x08 | MULMOD => 0x09 | SIGNEXTEND => 0x0b
  | LT => 0x10 | GT => 0x11 | SLT => 0x12 | SGT => 0x13 | EQ => 0x14 | ISZERO => 0x15
  | AND => 0x16 | OR => 0x17 | XOR => 0x18 | NOT => 0x19 | BYTE => 0x1a | SHL => 0x1b
  | SHR => 0x1c | SAR => 0x1d | CLZ => 0x1e

def arity : ArithOp → Nat
  | ISZERO | NOT | CLZ => 1
  | ADDMOD | MULMOD => 3
  | _ => 2

/-- Result on the popped arguments, top of stack first. Argument order follows the
    `StepRunning` rules (note SHL/SHR/SAR take the shift first). -/
def eval : ArithOp → List UInt256 → UInt256
  | ADD, a :: b :: _ => a + b
  | MUL, a :: b :: _ => a * b
  | SUB, a :: b :: _ => a - b
  | DIV, a :: b :: _ => a / b
  | SDIV, a :: b :: _ => UInt256.sdiv a b
  | MOD, a :: b :: _ => a % b
  | SMOD, a :: b :: _ => UInt256.smod a b
  | ADDMOD, a :: b :: n :: _ => UInt256.addMod a b n
  | MULMOD, a :: b :: n :: _ => UInt256.mulMod a b n
  | SIGNEXTEND, b :: x :: _ => UInt256.signExtend b x
  | LT, a :: b :: _ => UInt256.lt a b
  | GT, a :: b :: _ => UInt256.gt a b
  | SLT, a :: b :: _ => UInt256.slt a b
  | SGT, a :: b :: _ => UInt256.sgt a b
  | EQ, a :: b :: _ => UInt256.eq a b
  | ISZERO, a :: _ => UInt256.isZero a
  | AND, a :: b :: _ => UInt256.land a b
  | OR, a :: b :: _ => UInt256.lor a b
  | XOR, a :: b :: _ => UInt256.xor a b
  | NOT, a :: _ => UInt256.lnot a
  | BYTE, i :: x :: _ => UInt256.byteAt i x
  | SHL, sh :: v :: _ => UInt256.shiftLeft v sh
  | SHR, sh :: v :: _ => UInt256.shiftRight v sh
  | SAR, sh :: v :: _ => UInt256.sar v sh
  | CLZ, a :: _ => UInt256.clz a
  | _, _ => 0

end ArithOp

/-- A straight-line stack instruction. `push bs` is `PUSH{bs.length}` with immediate `bs`
    (big-endian); `push []` is `PUSH0`. -/
inductive Instr
  | push (bs : List UInt8)
  | dup (n : Fin 16)
  | swap (n : Fin 16)
  | pop
  | op (o : ArithOp)
  deriving DecidableEq, Repr, Inhabited

abbrev Block := List Instr

def pushVal (bs : List UInt8) : UInt256 :=
  UInt256.ofNat (Data.Bytes.bytesToBigEndianNat ⟨bs.toArray⟩)

theorem pushVal_eq (bs : List UInt8) :
    pushVal bs = UInt256.ofNat (bs.foldl (fun acc b => acc * 256 + b.toNat) 0) := by
  simp [pushVal, Data.Bytes.bytesToBigEndianNat, ByteArray.toList_mk]

namespace Instr

def toOp : Instr → Operation
  | push bs => .Push ⟨⟨min bs.length 32, by omega⟩⟩
  | dup n => .Dup ⟨n⟩
  | swap n => .Swap ⟨n⟩
  | pop => .POP
  | op o => o.toOp

def bytes : Instr → List UInt8
  | push bs => (0x5f + bs.length).toUInt8 :: bs
  | dup n => [(0x80 + n.val).toUInt8]
  | swap n => [(0x90 + n.val).toUInt8]
  | pop => [0x50]
  | op o => [o.byte]

def size (i : Instr) : Nat := i.bytes.length

/-- Stack effect ignoring the 1024-item limit and fork; `none` on underflow or an
    over-long PUSH. -/
def stackOp : Instr → List UInt256 → Option (List UInt256)
  | push bs, stk => if bs.length ≤ 32 then some (pushVal bs :: stk) else none
  | dup n, stk => stk[n.val]?.map (· :: stk)
  | swap n, stk => stk.exchange 0 (n.val + 1)
  | pop, stk => stk.tail?
  | op o, stk => if o.arity ≤ stk.length then some (o.eval stk :: stk.drop o.arity) else none

/-- Stack effect as the EVM executes it: also fails on overflow and on an opcode not yet
    active in `f`. -/
def exec (f : Fork) (i : Instr) (stk : List UInt256) : Option (List UInt256) :=
  if i.toOp.availableInFork f then
    (i.stackOp stk).bind fun stk' => if stk'.length ≤ 1024 then some stk' else none
  else none

theorem exec_eq_some {f : Fork} {i : Instr} {stk stk' : List UInt256} :
    i.exec f stk = some stk' ↔
      i.toOp.availableInFork f = true ∧ i.stackOp stk = some stk' ∧ stk'.length ≤ 1024 := by
  unfold exec
  split <;> simp_all [Option.bind_eq_some_iff]

def cost (f : Fork) (i : Instr) : Nat := Gas.baseCost f i.toOp

end Instr

def run (f : Fork) : Block → List UInt256 → Option (List UInt256)
  | [], stk => some stk
  | i :: b, stk => (i.exec f stk).bind (run f b)

def cost (f : Fork) : Block → Nat
  | [] => 0
  | i :: b => i.cost f + cost f b

def encode (b : Block) : List UInt8 := b.flatMap Instr.bytes

end EvmOpt
