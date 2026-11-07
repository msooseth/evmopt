import EvmOpt.Sound

namespace EvmOpt
open EvmSemantics EvmSemantics.EVM

/-- What a term is evaluated against: the frame, the block's input stack, and the results
    of the block's effects (loads, KECCAK) in order. -/
structure Ctx where
  σ : State
  stk : List UInt256
  effs : List UInt256 := []
  tags : Nat → UInt256 := fun _ => 0

/-- Symbolic word: `var i` is the `i`-th input stack item (0 = top); `eff i` is the result
    of the block's `i`-th effect. -/
inductive Term
  | var (i : Nat)
  | const (v : UInt256)
  | app1 (o : ArithOp) (a : Term)
  | app2 (o : ArithOp) (a b : Term)
  | app3 (o : ArithOp) (a b c : Term)
  | env0 (e : EnvOp)
  | env1 (e : EnvOp) (a : Term)
  | eff (i : Nat)
  | tag (k : Nat)
  deriving DecidableEq, Repr, Inhabited, Ord, Hashable

namespace Term

def eval (ρ : Ctx) : Term → UInt256
  | var i => ρ.stk.getD i 0
  | const v => v
  | app1 o a => o.eval [a.eval ρ]
  | app2 o a b => o.eval [a.eval ρ, b.eval ρ]
  | app3 o a b c => o.eval [a.eval ρ, b.eval ρ, c.eval ρ]
  | env0 e => e.eval ρ.σ []
  | env1 e a => e.eval ρ.σ [a.eval ρ]
  | eff i => ρ.effs.getD i 0
  | tag k => ρ.tags k

end Term

/-- Build the application of `o` to the top `o.arity` terms. -/
def mkApp (o : ArithOp) : List Term → Term
  | ts => match o.arity, ts with
    | 1, a :: _ => .app1 o a
    | 2, a :: b :: _ => .app2 o a b
    | 3, a :: b :: c :: _ => .app3 o a b c
    | _, _ => .const 0

theorem ArithOp.arity_cases (o : ArithOp) : o.arity = 1 ∨ o.arity = 2 ∨ o.arity = 3 := by
  cases o <;> simp [ArithOp.arity]

theorem ArithOp.eval_take (o : ArithOp) (l : List UInt256) :
    o.eval l = o.eval (l.take o.arity) := by
  cases o <;> rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> rfl

def mkEnv (e : EnvOp) : List Term → Term
  | ts => match e.arity, ts with
    | 0, _ => .env0 e
    | 1, a :: _ => .env1 e a
    | _, _ => .const 0

theorem EnvOp.eval_take (σ : State) (e : EnvOp) (l : List UInt256) :
    e.eval σ l = e.eval σ (l.take e.arity) := by
  cases e <;> rcases l with _ | ⟨a, l⟩ <;> rfl

theorem mkEnv_eval (e : EnvOp) (ts : List Term) (ρ : Ctx)
    (h : e.arity ≤ ts.length) : (mkEnv e ts).eval ρ = e.eval ρ.σ (ts.map (·.eval ρ)) := by
  rw [EnvOp.eval_take ρ.σ e (ts.map _)]
  have : e.arity = 0 ∨ e.arity = 1 := by cases e <;> simp [EnvOp.arity]
  rcases this with h1 | h1
  · simp [mkEnv, h1, Term.eval]
  · rcases ts with _ | ⟨a, ts⟩
    · simp [h1] at h
    · simp [mkEnv, h1, Term.eval]

theorem mkApp_eval (o : ArithOp) (ts : List Term) (ρ : Ctx)
    (h : o.arity ≤ ts.length) : (mkApp o ts).eval ρ = o.eval (ts.map (·.eval ρ)) := by
  rw [ArithOp.eval_take o (ts.map _)]
  rcases ArithOp.arity_cases o with h1 | h1 | h1 <;>
  · rcases ts with _ | ⟨a, _ | ⟨b, _ | ⟨c, ts⟩⟩⟩ <;> simp_all [mkApp, Term.eval] <;>
      rw [ArithOp.eval_take] <;> simp [h1]

/-- Symbolic stack: the concrete stack is `ts` evaluated over the input, followed by the
    input from depth `d` on. `slack` bounds the input height: every step so far stayed
    within 1024 items iff `input.length - d ≤ slack`. -/
structure SState where
  ts : List Term
  d : Nat
  slack : Int
  deriving Repr

def SState.init : SState := ⟨[], 0, 1024⟩

def conc (ρ : Ctx) (S : SState) : List UInt256 :=
  S.ts.map (·.eval ρ) ++ ρ.stk.drop S.d

def vars (a n : Nat) : List Term := (List.range n).map fun j => .var (a + j)

/-- Materialise input items until at least `k` symbolic items are on top. -/
def ensure (k : Nat) (S : SState) : SState :=
  let e := k - S.ts.length
  ⟨S.ts ++ vars S.d e, S.d + e, S.slack - e⟩

def Instr.need : Instr → Nat
  | .push _ => 0
  | .dup n => n.val + 1
  | .swap n => n.val + 2
  | .pop => 1
  | .op o => o.arity
  | .env e => e.arity

/-- Static validity: well-formed immediate and opcode active in the fork. -/
def Instr.static (f : Fork) (i : Instr) : Bool :=
  i.toOp.availableInFork f && match i with
    | .push bs => decide (bs.length ≤ 32)
    | _ => true

/-- Symbolic effect on the (already `ensure`d) term stack. -/
def Instr.sym : Instr → List Term → List Term
  | .push bs, ts => .const (pushVal bs) :: ts
  | .dup n, ts => ts.getD n.val (.const 0) :: ts
  | .swap n, ts => (ts.exchange 0 (n.val + 1)).getD ts
  | .pop, ts => ts.tail
  | .op o, ts => mkApp o ts :: ts.drop o.arity
  | .env e, ts => mkEnv e ts :: ts.drop e.arity

def sstep (i : Instr) (S : SState) : SState :=
  let S1 := ensure i.need S
  let ts := i.sym S1.ts
  ⟨ts, S1.d, min S1.slack (1024 - ts.length)⟩

def srun (f : Fork) : Block → SState → Option SState
  | [], S => some S
  | i :: b, S => if i.static f then srun f b (sstep i S) else none

def lift (f : Fork) (b : Block) : Option SState := srun f b SState.init

end EvmOpt
