import EvmOpt.Sound

namespace EvmOpt
open EvmSemantics EvmSemantics.EVM

/-- Symbolic word: `var i` is the `i`-th input stack item (0 = top). -/
inductive Term
  | var (i : Nat)
  | const (v : UInt256)
  | app1 (o : ArithOp) (a : Term)
  | app2 (o : ArithOp) (a b : Term)
  | app3 (o : ArithOp) (a b c : Term)
  deriving DecidableEq, Repr, Inhabited

namespace Term

def eval (stk : List UInt256) : Term → UInt256
  | var i => stk.getD i 0
  | const v => v
  | app1 o a => o.eval [a.eval stk]
  | app2 o a b => o.eval [a.eval stk, b.eval stk]
  | app3 o a b c => o.eval [a.eval stk, b.eval stk, c.eval stk]

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

theorem mkApp_eval (o : ArithOp) (ts : List Term) (stk : List UInt256)
    (h : o.arity ≤ ts.length) : (mkApp o ts).eval stk = o.eval (ts.map (·.eval stk)) := by
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

def conc (stk : List UInt256) (S : SState) : List UInt256 :=
  S.ts.map (·.eval stk) ++ stk.drop S.d

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

def sstep (i : Instr) (S : SState) : SState :=
  let S1 := ensure i.need S
  let ts := i.sym S1.ts
  ⟨ts, S1.d, min S1.slack (1024 - ts.length)⟩

def srun (f : Fork) : Block → SState → Option SState
  | [], S => some S
  | i :: b, S => if i.static f then srun f b (sstep i S) else none

def lift (f : Fork) (b : Block) : Option SState := srun f b SState.init

end EvmOpt
