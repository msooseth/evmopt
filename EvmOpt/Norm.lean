import EvmOpt.Term
import EvmOpt.U256

namespace EvmOpt
open EvmSemantics EvmSemantics.EVM UInt256

/-- `t` is the constant `n`. -/
def isC (t : Term) (n : Nat) : Bool :=
  match t with
  | .const v => v.toNat == n
  | _ => false

theorem isC_eval {t : Term} {n : Nat} (stk : List UInt256) (h : isC t n = true) :
    (t.eval stk).toNat = n := by
  cases t <;> simp_all [isC, Term.eval]

/-- Order the arguments of a commutative operation. -/
def comm (o : ArithOp) (a b : Term) : Term :=
  if compare b a == .lt then .app2 o b a else .app2 o a b

theorem comm_eval {o : ArithOp} (hc : ∀ x y, o.eval [x, y] = o.eval [y, x]) (a b : Term)
    (stk : List UInt256) : (comm o a b).eval stk = o.eval [a.eval stk, b.eval stk] := by
  unfold comm; split <;> simp [Term.eval, hc]

def c0 : Term := .const ⟨0⟩
def c1 : Term := .const (ofNat 1)

section rules
variable (stk : List UInt256)

def rADD (a b : Term) : Term := if isC a 0 then b else if isC b 0 then a else comm .ADD a b
theorem rADD_eval (a b : Term) : (rADD a b).eval stk = a.eval stk + b.eval stk := by
  unfold rADD
  split
  · next h => rw [add_comm', add_zero_of (isC_eval stk h)]
  split
  · next h => rw [add_zero_of (isC_eval stk h)]
  exact comm_eval (o := .ADD) (fun x y => add_comm' x y) a b stk

def rSUB (a b : Term) : Term := if isC b 0 then a else if a = b then c0 else .app2 .SUB a b
theorem rSUB_eval (a b : Term) : (rSUB a b).eval stk = a.eval stk - b.eval stk := by
  unfold rSUB
  split
  · next h => rw [sub_zero_of (isC_eval stk h)]
  split
  · next h => subst h; rw [sub_self']; rfl
  rfl

def rMUL (a b : Term) : Term :=
  if isC a 0 || isC b 0 then c0 else if isC a 1 then b else if isC b 1 then a
  else comm .MUL a b
theorem rMUL_eval (a b : Term) : (rMUL a b).eval stk = a.eval stk * b.eval stk := by
  unfold rMUL
  split
  · next h =>
    simp only [Bool.or_eq_true] at h
    rcases h with h | h
    · rw [mul_comm', mul_zero_of (isC_eval stk h)]; rfl
    · rw [mul_zero_of (isC_eval stk h)]; rfl
  split
  · next h => rw [mul_comm', mul_one_of (isC_eval stk h)]
  split
  · next h => rw [mul_one_of (isC_eval stk h)]
  exact comm_eval (o := .MUL) (fun x y => mul_comm' x y) a b stk

def rDIV (a b : Term) : Term := if isC b 1 then a else .app2 .DIV a b
theorem rDIV_eval (a b : Term) : (rDIV a b).eval stk = a.eval stk / b.eval stk := by
  unfold rDIV
  split
  · next h => rw [div_one_of (isC_eval stk h)]
  rfl

def rMOD (a b : Term) : Term :=
  if isC b 0 || isC b 1 || a = b then c0 else .app2 .MOD a b
theorem rMOD_eval (a b : Term) : (rMOD a b).eval stk = a.eval stk % b.eval stk := by
  unfold rMOD
  split
  · next h =>
    simp only [Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with (h | h) | h
    · rw [mod_zero_of (isC_eval stk h)]; rfl
    · rw [mod_one_of (isC_eval stk h)]; rfl
    · subst h; rw [mod_self']; rfl
  rfl

def isMax (t : Term) : Bool := isC t (UInt256.size - 1)

def rAND (a b : Term) : Term :=
  if isC a 0 || isC b 0 then c0 else if a = b then a else if isMax a then b
  else if isMax b then a else comm .AND a b
theorem rAND_eval (a b : Term) : (rAND a b).eval stk = land (a.eval stk) (b.eval stk) := by
  unfold rAND
  split
  · next h =>
    simp only [Bool.or_eq_true] at h
    rcases h with h | h
    · rw [land_comm', land_zero_of (isC_eval stk h)]; rfl
    · rw [land_zero_of (isC_eval stk h)]; rfl
  split
  · next h => subst h; rw [land_self']
  split
  · next h => rw [land_comm', land_max_of (isC_eval stk h)]
  split
  · next h => rw [land_max_of (isC_eval stk h)]
  exact comm_eval (o := .AND) (fun x y => land_comm' x y) a b stk

def rOR (a b : Term) : Term :=
  if a = b then a else if isC a 0 then b else if isC b 0 then a else comm .OR a b
theorem rOR_eval (a b : Term) : (rOR a b).eval stk = lor (a.eval stk) (b.eval stk) := by
  unfold rOR
  split
  · next h => subst h; rw [lor_self']
  split
  · next h => rw [lor_comm', lor_zero_of (isC_eval stk h)]
  split
  · next h => rw [lor_zero_of (isC_eval stk h)]
  exact comm_eval (o := .OR) (fun x y => lor_comm' x y) a b stk

def rXOR (a b : Term) : Term :=
  if a = b then c0 else if isC a 0 then b else if isC b 0 then a else comm .XOR a b
theorem rXOR_eval (a b : Term) : (rXOR a b).eval stk = xor (a.eval stk) (b.eval stk) := by
  unfold rXOR
  split
  · next h => subst h; rw [xor_self']; rfl
  split
  · next h => rw [xor_comm', xor_zero_of (isC_eval stk h)]
  split
  · next h => rw [xor_zero_of (isC_eval stk h)]
  exact comm_eval (o := .XOR) (fun x y => xor_comm' x y) a b stk

def rEQ (a b : Term) : Term := if a = b then c1 else comm .EQ a b
theorem rEQ_eval (a b : Term) : (rEQ a b).eval stk = UInt256.eq (a.eval stk) (b.eval stk) := by
  unfold rEQ
  split
  · next h => subst h; rw [eq_self']; rfl
  exact comm_eval (o := .EQ) (fun x y => eq_comm' x y) a b stk

def rLT (a b : Term) : Term := if isC b 0 || a = b then .const (ofNat 0) else .app2 .LT a b
theorem rLT_eval (a b : Term) : (rLT a b).eval stk = UInt256.lt (a.eval stk) (b.eval stk) := by
  unfold rLT
  split
  · next h =>
    simp only [Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with h | h
    · rw [lt_zero_of (isC_eval stk h)]; rfl
    · subst h; rw [lt_self']; rfl
  rfl

def rSLT (a b : Term) : Term := if a = b then .const (ofNat 0) else .app2 .SLT a b
theorem rSLT_eval (a b : Term) : (rSLT a b).eval stk = UInt256.slt (a.eval stk) (b.eval stk) := by
  unfold rSLT
  split
  · next h => subst h; rw [slt_self']; rfl
  rfl

end rules

def simp1 (o : ArithOp) (a : Term) : Term :=
  match a with
  | .const c => .const (o.eval [c])
  | a => match o, a with
    | .ISZERO, .app1 .ISZERO (.app1 .ISZERO x) => .app1 .ISZERO x
    | .NOT, .app1 .NOT x => x
    | o, a => .app1 o a

theorem simp1_eval (o : ArithOp) (a : Term) (stk : List UInt256) :
    (simp1 o a).eval stk = o.eval [a.eval stk] := by
  unfold simp1
  split
  · rfl
  · split
    · simp only [Term.eval, ArithOp.eval]; rw [isZero_isZero_isZero]
    · simp only [Term.eval, ArithOp.eval]; rw [lnot_lnot]
    · rfl

def rules2 (o : ArithOp) (a b : Term) : Term :=
  match o with
  | .ADD => rADD a b
  | .SUB => rSUB a b
  | .MUL => rMUL a b
  | .DIV => rDIV a b
  | .MOD => rMOD a b
  | .AND => rAND a b
  | .OR => rOR a b
  | .XOR => rXOR a b
  | .EQ => rEQ a b
  | .LT => rLT a b
  | .GT => rLT b a
  | .SLT => rSLT a b
  | .SGT => rSLT b a
  | o => .app2 o a b

theorem rules2_eval (o : ArithOp) (a b : Term) (stk : List UInt256) :
    (rules2 o a b).eval stk = o.eval [a.eval stk, b.eval stk] := by
  cases o <;> simp only [rules2]
  all_goals first
    | rfl
    | exact rADD_eval stk a b
    | exact rSUB_eval stk a b
    | exact rMUL_eval stk a b
    | exact rDIV_eval stk a b
    | exact rMOD_eval stk a b
    | exact rAND_eval stk a b
    | exact rOR_eval stk a b
    | exact rXOR_eval stk a b
    | exact rEQ_eval stk a b
    | exact rLT_eval stk a b
    | exact rLT_eval stk b a
    | exact rSLT_eval stk a b
    | exact rSLT_eval stk b a

def simp2 (o : ArithOp) (a b : Term) : Term :=
  match a, b with
  | .const x, .const y => .const (o.eval [x, y])
  | a, b => rules2 o a b

theorem simp2_eval (o : ArithOp) (a b : Term) (stk : List UInt256) :
    (simp2 o a b).eval stk = o.eval [a.eval stk, b.eval stk] := by
  unfold simp2
  split
  · rfl
  · exact rules2_eval o a b stk

def simp3 (o : ArithOp) (a b c : Term) : Term :=
  match a, b, c with
  | .const x, .const y, .const z => .const (o.eval [x, y, z])
  | a, b, c => .app3 o a b c

theorem simp3_eval (o : ArithOp) (a b c : Term) (stk : List UInt256) :
    (simp3 o a b c).eval stk = o.eval [a.eval stk, b.eval stk, c.eval stk] := by
  unfold simp3; split <;> rfl

def norm : Term → Term
  | .var i => .var i
  | .const v => .const v
  | .app1 o a => simp1 o (norm a)
  | .app2 o a b => simp2 o (norm a) (norm b)
  | .app3 o a b c => simp3 o (norm a) (norm b) (norm c)

theorem norm_eval (stk : List UInt256) : ∀ t : Term, (norm t).eval stk = t.eval stk
  | .var _ => rfl
  | .const _ => rfl
  | .app1 o a => by rw [norm, simp1_eval, norm_eval stk a]; rfl
  | .app2 o a b => by rw [norm, simp2_eval, norm_eval stk a, norm_eval stk b]; rfl
  | .app3 o a b c => by
    rw [norm, simp3_eval, norm_eval stk a, norm_eval stk b, norm_eval stk c]; rfl

end EvmOpt
