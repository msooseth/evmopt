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

/-- `t = o(x, y)` with `z ∈ {x, y}`. -/
def hasArg (o : ArithOp) (t z : Term) : Bool :=
  match t with
  | .app2 o' x y => o' == o && (z == x || z == y)
  | _ => false

/-- `t = XOR(x, y)` and `z` is one of them: the other one. -/
def xorOther (t z : Term) : Option Term :=
  match t with
  | .app2 .XOR x y => if z = x then some y else if z = y then some x else none
  | _ => none

theorem hasArg_spec {o : ArithOp} {t z : Term} (h : hasArg o t z = true) :
    ∃ x y, t = .app2 o x y ∧ (z = x ∨ z = y) := by
  unfold hasArg at h
  split at h
  · next o' x y =>
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at h
    obtain ⟨rfl, h⟩ := h
    exact ⟨x, y, rfl, h⟩
  · contradiction

def c0 : Term := .const ⟨0⟩
def c1 : Term := .const (ofNat 1)

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
  if hasArg .AND a b || hasArg .OR b a then a else if hasArg .AND b a || hasArg .OR a b then b
  else if isC a 0 || isC b 0 then c0 else if a = b then a else if isMax a then b
  else if isMax b then a else comm .AND a b
theorem rAND_eval (a b : Term) : (rAND a b).eval stk = land (a.eval stk) (b.eval stk) := by
  unfold rAND
  split
  · next h =>
    simp only [Bool.or_eq_true] at h
    rcases h with h | h <;> obtain ⟨x, y, rfl, hz | hz⟩ := hasArg_spec h <;> subst hz <;>
      simp only [Term.eval, ArithOp.eval]
    · rw [land_absorb_left]
    · rw [land_absorb_right]
    · rw [land_lor_absorb_left]
    · rw [land_lor_absorb_right]
  split
  · next h =>
    simp only [Bool.or_eq_true] at h
    rcases h with h | h <;> obtain ⟨x, y, rfl, hz | hz⟩ := hasArg_spec h <;> subst hz <;>
      simp only [Term.eval, ArithOp.eval]
    all_goals first
      | exact (land_absorb_in_left _ _).symm | exact (land_absorb_in_right _ _).symm
      | exact (land_lor_absorb_in_left _ _).symm | exact (land_lor_absorb_in_right _ _).symm
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
  if hasArg .OR a b || hasArg .AND b a then a else if hasArg .OR b a || hasArg .AND a b then b
  else if a = b then a else if isC a 0 then b else if isC b 0 then a else comm .OR a b
theorem rOR_eval (a b : Term) : (rOR a b).eval stk = lor (a.eval stk) (b.eval stk) := by
  unfold rOR
  split
  · next h =>
    simp only [Bool.or_eq_true] at h
    rcases h with h | h <;> obtain ⟨x, y, rfl, hz | hz⟩ := hasArg_spec h <;> subst hz <;>
      simp only [Term.eval, ArithOp.eval]
    · rw [lor_absorb_left]
    · rw [lor_absorb_right]
    · rw [lor_land_absorb_left]
    · rw [lor_land_absorb_right]
  split
  · next h =>
    simp only [Bool.or_eq_true] at h
    rcases h with h | h <;> obtain ⟨x, y, rfl, hz | hz⟩ := hasArg_spec h <;> subst hz <;>
      simp only [Term.eval, ArithOp.eval]
    all_goals first
      | exact (lor_absorb_in_left _ _).symm | exact (lor_absorb_in_right _ _).symm
      | exact (lor_land_absorb_in_left _ _).symm | exact (lor_land_absorb_in_right _ _).symm
  split
  · next h => subst h; rw [lor_self']
  split
  · next h => rw [lor_comm', lor_zero_of (isC_eval stk h)]
  split
  · next h => rw [lor_zero_of (isC_eval stk h)]
  exact comm_eval (o := .OR) (fun x y => lor_comm' x y) a b stk

def rXOR (a b : Term) : Term :=
  match xorOther a b, xorOther b a with
  | some r, _ => r
  | none, some r => r
  | none, none =>
    if a = b then c0 else if isC a 0 then b else if isC b 0 then a else comm .XOR a b

theorem xorOther_eval {t z r : Term} (h : xorOther t z = some r) (stk : List UInt256) :
    xor (t.eval stk) (z.eval stk) = r.eval stk := by
  unfold xorOther at h
  split at h
  · next x y =>
    split at h
    · next hz => simp only [Option.some.injEq] at h; subst h hz; exact xor_cancel_left _ _
    split at h
    · next hz => simp only [Option.some.injEq] at h; subst h hz; exact xor_cancel_right _ _
    contradiction
  · contradiction

theorem rXOR_eval (a b : Term) : (rXOR a b).eval stk = xor (a.eval stk) (b.eval stk) := by
  cases h1 : xorOther a b with
  | some r => simp only [rXOR, h1]; exact (xorOther_eval h1 stk).symm
  | none =>
  cases h2 : xorOther b a with
  | some r => simp only [rXOR, h1, h2]; rw [xor_comm']; exact (xorOther_eval h2 stk).symm
  | none =>
  simp only [rXOR, h1, h2]
  split
  · next h => subst h; rw [xor_self']; rfl
  split
  · next h => rw [xor_comm', xor_zero_of (isC_eval stk h)]
  split
  · next h => rw [xor_zero_of (isC_eval stk h)]
  exact comm_eval (o := .XOR) (fun x y => xor_comm' x y) a b stk

def rEQ (iz : Term → Term) (a b : Term) : Term :=
  if a = b then c1 else if isC a 0 then iz b else if isC b 0 then iz a else comm .EQ a b
theorem rEQ_eval (iz : Term → Term) (hiz : ∀ t, (iz t).eval stk = isZero (t.eval stk))
    (a b : Term) : (rEQ iz a b).eval stk = UInt256.eq (a.eval stk) (b.eval stk) := by
  unfold rEQ
  split
  · next h => subst h; rw [eq_self']; rfl
  split
  · next h => rw [hiz, eq_zero_left (isC_eval stk h)]
  split
  · next h => rw [hiz, eq_comm', eq_zero_left (isC_eval stk h)]
  exact comm_eval (o := .EQ) (fun x y => eq_comm' x y) a b stk

def rSHL (a b : Term) : Term := if isC a 0 then b else if isC b 0 then c0 else .app2 .SHL a b
theorem rSHL_eval (a b : Term) :
    (rSHL a b).eval stk = shiftLeft (b.eval stk) (a.eval stk) := by
  unfold rSHL
  split
  · next h => rw [shiftLeft_zero_shift (isC_eval stk h)]
  split
  · next h => rw [shiftLeft_zero_val (isC_eval stk h)]; rfl
  rfl

def rSHR (a b : Term) : Term := if isC a 0 then b else if isC b 0 then c0 else .app2 .SHR a b
theorem rSHR_eval (a b : Term) :
    (rSHR a b).eval stk = shiftRight (b.eval stk) (a.eval stk) := by
  unfold rSHR
  split
  · next h => rw [shiftRight_zero_shift (isC_eval stk h)]
  split
  · next h => rw [shiftRight_zero_val (isC_eval stk h)]; rfl
  rfl

def rLT (iz : Term → Term) (a b : Term) : Term :=
  if isC b 0 || a = b then .const (ofNat 0) else if isC b 1 then iz a else .app2 .LT a b
theorem rLT_eval (iz : Term → Term) (hiz : ∀ t, (iz t).eval stk = isZero (t.eval stk))
    (a b : Term) : (rLT iz a b).eval stk = UInt256.lt (a.eval stk) (b.eval stk) := by
  unfold rLT
  split
  · next h =>
    simp only [Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with h | h
    · rw [lt_zero_of (isC_eval stk h)]; rfl
    · subst h; rw [lt_self']; rfl
  split
  · next h => rw [hiz, lt_one_right (isC_eval stk h)]
  rfl

def rSLT (a b : Term) : Term := if a = b then .const (ofNat 0) else .app2 .SLT a b
theorem rSLT_eval (a b : Term) : (rSLT a b).eval stk = UInt256.slt (a.eval stk) (b.eval stk) := by
  unfold rSLT
  split
  · next h => subst h; rw [slt_self']; rfl
  rfl

end rules

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
  | .EQ => rEQ (simp1 .ISZERO) a b
  | .LT => rLT (simp1 .ISZERO) a b
  | .GT => rLT (simp1 .ISZERO) b a
  | .SHL => rSHL a b
  | .SHR => rSHR a b
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
    | exact rEQ_eval stk _ (fun t => simp1_eval .ISZERO t stk) a b
    | exact rLT_eval stk _ (fun t => simp1_eval .ISZERO t stk) a b
    | exact rLT_eval stk _ (fun t => simp1_eval .ISZERO t stk) b a
    | exact rSHL_eval stk a b
    | exact rSHR_eval stk a b
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
