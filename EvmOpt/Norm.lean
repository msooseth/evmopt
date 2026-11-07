import EvmOpt.Term
import EvmOpt.U256

namespace EvmOpt
open EvmSemantics EvmSemantics.EVM UInt256

/-- `t` is the constant `n`. -/
def isC (t : Term) (n : Nat) : Bool :=
  match t with
  | .const v => v.toNat == n
  | _ => false

theorem isC_eval {t : Term} {n : Nat} (σ : State) (stk : List UInt256) (h : isC t n = true) :
    (t.eval σ stk).toNat = n := by
  cases t <;> simp_all [isC, Term.eval]

/-- Order the arguments of a commutative operation. -/
def comm (o : ArithOp) (a b : Term) : Term :=
  if compare b a == .lt then .app2 o b a else .app2 o a b

theorem comm_eval {o : ArithOp} (hc : ∀ x y, o.eval [x, y] = o.eval [y, x]) (a b : Term)
    (σ : State) (stk : List UInt256) : (comm o a b).eval σ stk = o.eval [a.eval σ stk, b.eval σ stk] := by
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

/-- Terms known to be addresses (< 2^160). -/
def isAddr (t : Term) : Bool :=
  match t with
  | .env0 .ADDRESS | .env0 .ORIGIN | .env0 .CALLER | .env0 .COINBASE => true
  | _ => false

theorem isAddr_lt {t : Term} (σ : State) (stk : List UInt256) (h : isAddr t = true) :
    (t.eval σ stk).toNat < 2 ^ 160 := by
  cases t <;> try simp [isAddr] at h
  rename_i e
  cases e <;> simp at h <;> exact toNat_addr_lt _

def mask160 : Nat := 2 ^ 160 - 1

def c0 : Term := .const ⟨0⟩
def c1 : Term := .const (ofNat 1)

/-- Terms whose value is 0 or 1. -/
def isBoolT (t : Term) : Bool :=
  match t with
  | .app2 .LT _ _ | .app2 .GT _ _ | .app2 .SLT _ _ | .app2 .SGT _ _ | .app2 .EQ _ _ => true
  | .app1 .ISZERO _ => true
  | .const v => decide (v.toNat ≤ 1)
  | _ => false

theorem isBoolT_eval {t : Term} (σ : State) (stk : List UInt256) (h : isBoolT t = true) :
    IsBool (t.eval σ stk) := by
  cases t with
  | app2 o a b => cases o <;> simp [isBoolT] at h <;> exact isBool_ofNat01 _
  | app1 o a => cases o <;> simp [isBoolT] at h <;> exact isBool_ofNat01 _
  | const v => simpa [isBoolT, IsBool, Term.eval] using h
  | _ => simp [isBoolT] at h

/-- ISZERO of an already-normalised term. -/
def izRule (a : Term) : Term :=
  match a with
  | .app1 .ISZERO x => if isBoolT x then x else .app1 .ISZERO a
  | .app2 .LT z x => if isC z 0 then .app1 .ISZERO x else .app1 .ISZERO a
  | .app2 .XOR x y => comm .EQ x y
  | .app2 .SUB x y => comm .EQ x y
  | a => .app1 .ISZERO a

theorem izRule_eval (a : Term) (σ : State) (stk : List UInt256) :
    (izRule a).eval σ stk = isZero (a.eval σ stk) := by
  unfold izRule
  split
  · next x =>
    split
    · next h =>
      simp only [Term.eval, ArithOp.eval]
      exact (isZero_isZero_of_bool (isBoolT_eval σ stk h)).symm
    · rfl
  · next z x =>
    split
    · next h => simp only [Term.eval, ArithOp.eval]; rw [isZero_lt_zero_left (isC_eval σ stk h)]
    · rfl
  · next x y =>
    rw [comm_eval (o := .EQ) (fun x y => eq_comm' x y)]
    simp only [Term.eval, ArithOp.eval]; rw [isZero_xor]
  · next x y =>
    rw [comm_eval (o := .EQ) (fun x y => eq_comm' x y)]
    simp only [Term.eval, ArithOp.eval]; rw [isZero_sub]
  · rfl

def simp1 (o : ArithOp) (a : Term) : Term :=
  match a with
  | .const c => .const (o.eval [c])
  | a => match o, a with
    | .ISZERO, a => izRule a
    | .NOT, .app1 .NOT x => x
    | o, a => .app1 o a

theorem simp1_eval (o : ArithOp) (a : Term) (σ : State) (stk : List UInt256) :
    (simp1 o a).eval σ stk = o.eval [a.eval σ stk] := by
  unfold simp1
  split
  · rfl
  · split
    · exact izRule_eval _ σ stk
    · simp only [Term.eval, ArithOp.eval]; rw [lnot_lnot]
    · rfl

/-- `t = SHL(y, 1)`: the `y`. -/
def shlOne? (t : Term) : Option Term :=
  match t with
  | .app2 .SHL y one => if isC one 1 then some y else none
  | _ => none

theorem shlOne_eval {t y : Term} (h : shlOne? t = some y) (σ : State) (stk : List UInt256) :
    ∃ one : UInt256, one.toNat = 1 ∧ t.eval σ stk = shiftLeft one (y.eval σ stk) := by
  unfold shlOne? at h
  split at h
  · next y' one =>
    split at h
    · next h1 =>
      simp only [Option.some.injEq] at h; subst h
      exact ⟨_, isC_eval σ stk h1, rfl⟩
    · contradiction
  · contradiction

section rules
variable (σ : State) (stk : List UInt256)

def rADD (a b : Term) : Term := if isC a 0 then b else if isC b 0 then a else comm .ADD a b
theorem rADD_eval (a b : Term) : (rADD a b).eval σ stk = a.eval σ stk + b.eval σ stk := by
  unfold rADD
  split
  · next h => rw [add_comm', add_zero_of (isC_eval σ stk h)]
  split
  · next h => rw [add_zero_of (isC_eval σ stk h)]
  exact comm_eval (o := .ADD) (fun x y => add_comm' x y) a b σ stk

def rSUB (a b : Term) : Term := if isC b 0 then a else if a = b then c0 else .app2 .SUB a b
theorem rSUB_eval (a b : Term) : (rSUB a b).eval σ stk = a.eval σ stk - b.eval σ stk := by
  unfold rSUB
  split
  · next h => rw [sub_zero_of (isC_eval σ stk h)]
  split
  · next h => subst h; rw [sub_self']; rfl
  rfl

def rMUL (a b : Term) : Term :=
  if isC a 0 || isC b 0 then c0 else if isC a 1 then b else if isC b 1 then a
  else match shlOne? b, shlOne? a with
    | some y, _ => .app2 .SHL y a
    | none, some y => .app2 .SHL y b
    | none, none => comm .MUL a b
theorem rMUL_eval (a b : Term) : (rMUL a b).eval σ stk = a.eval σ stk * b.eval σ stk := by
  unfold rMUL
  split
  · next h =>
    simp only [Bool.or_eq_true] at h
    rcases h with h | h
    · rw [mul_comm', mul_zero_of (isC_eval σ stk h)]; rfl
    · rw [mul_zero_of (isC_eval σ stk h)]; rfl
  split
  · next h => rw [mul_comm', mul_one_of (isC_eval σ stk h)]
  split
  · next h => rw [mul_one_of (isC_eval σ stk h)]
  cases hb : shlOne? b with
  | some y =>
    obtain ⟨one, h1, he⟩ := shlOne_eval hb σ stk
    show shiftLeft (a.eval σ stk) (y.eval σ stk) = a.eval σ stk * b.eval σ stk
    rw [he, mul_shl_one h1]
  | none =>
  cases ha : shlOne? a with
  | some y =>
    obtain ⟨one, h1, he⟩ := shlOne_eval ha σ stk
    show shiftLeft (b.eval σ stk) (y.eval σ stk) = a.eval σ stk * b.eval σ stk
    rw [he, mul_comm', mul_shl_one h1]
  | none => exact comm_eval (o := .MUL) (fun x y => mul_comm' x y) a b σ stk

def rDIV (a b : Term) : Term :=
  if isC b 1 then a else match shlOne? b with
    | some y => .app2 .SHR y a
    | none => .app2 .DIV a b
theorem rDIV_eval (a b : Term) : (rDIV a b).eval σ stk = a.eval σ stk / b.eval σ stk := by
  unfold rDIV
  split
  · next h => rw [div_one_of (isC_eval σ stk h)]
  cases hb : shlOne? b with
  | some y =>
    obtain ⟨one, h1, he⟩ := shlOne_eval hb σ stk
    show shiftRight (a.eval σ stk) (y.eval σ stk) = a.eval σ stk / b.eval σ stk
    rw [he, div_shl_one h1]
  | none => rfl

def rMOD (a b : Term) : Term :=
  if isC b 0 || isC b 1 || a = b then c0 else .app2 .MOD a b
theorem rMOD_eval (a b : Term) : (rMOD a b).eval σ stk = a.eval σ stk % b.eval σ stk := by
  unfold rMOD
  split
  · next h =>
    simp only [Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with (h | h) | h
    · rw [mod_zero_of (isC_eval σ stk h)]; rfl
    · rw [mod_one_of (isC_eval σ stk h)]; rfl
    · subst h; rw [mod_self']; rfl
  rfl

def isMax (t : Term) : Bool := isC t (UInt256.size - 1)

def rAND (a b : Term) : Term :=
  if hasArg .AND a b || hasArg .OR b a then a else if hasArg .AND b a || hasArg .OR a b then b
  else if isC a 0 || isC b 0 then c0 else if a = b then a else if isMax a then b
  else if isMax b then a else if isAddr a && isC b mask160 then a
  else if isAddr b && isC a mask160 then b else comm .AND a b
theorem rAND_eval (a b : Term) : (rAND a b).eval σ stk = land (a.eval σ stk) (b.eval σ stk) := by
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
    · rw [land_comm', land_zero_of (isC_eval σ stk h)]; rfl
    · rw [land_zero_of (isC_eval σ stk h)]; rfl
  split
  · next h => subst h; rw [land_self']
  split
  · next h => rw [land_comm', land_max_of (isC_eval σ stk h)]
  split
  · next h => rw [land_max_of (isC_eval σ stk h)]
  split
  · next h =>
    simp only [Bool.and_eq_true] at h
    exact (land_mask_of_lt (isAddr_lt σ stk h.1) (isC_eval σ stk h.2)).symm
  split
  · next h =>
    simp only [Bool.and_eq_true] at h
    rw [land_comm']; exact (land_mask_of_lt (isAddr_lt σ stk h.1) (isC_eval σ stk h.2)).symm
  exact comm_eval (o := .AND) (fun x y => land_comm' x y) a b σ stk

def rOR (a b : Term) : Term :=
  if hasArg .OR a b || hasArg .AND b a then a else if hasArg .OR b a || hasArg .AND a b then b
  else if a = b then a else if isC a 0 then b else if isC b 0 then a else comm .OR a b
theorem rOR_eval (a b : Term) : (rOR a b).eval σ stk = lor (a.eval σ stk) (b.eval σ stk) := by
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
  · next h => rw [lor_comm', lor_zero_of (isC_eval σ stk h)]
  split
  · next h => rw [lor_zero_of (isC_eval σ stk h)]
  exact comm_eval (o := .OR) (fun x y => lor_comm' x y) a b σ stk

def rXOR (a b : Term) : Term :=
  match xorOther a b, xorOther b a with
  | some r, _ => r
  | none, some r => r
  | none, none =>
    if a = b then c0 else if isC a 0 then b else if isC b 0 then a else comm .XOR a b

theorem xorOther_eval {t z r : Term} (h : xorOther t z = some r) (σ : State) (stk : List UInt256) :
    xor (t.eval σ stk) (z.eval σ stk) = r.eval σ stk := by
  unfold xorOther at h
  split at h
  · next x y =>
    split at h
    · next hz => simp only [Option.some.injEq] at h; subst h hz; exact xor_cancel_left _ _
    split at h
    · next hz => simp only [Option.some.injEq] at h; subst h hz; exact xor_cancel_right _ _
    contradiction
  · contradiction

theorem rXOR_eval (a b : Term) : (rXOR a b).eval σ stk = xor (a.eval σ stk) (b.eval σ stk) := by
  cases h1 : xorOther a b with
  | some r => simp only [rXOR, h1]; exact (xorOther_eval h1 σ stk).symm
  | none =>
  cases h2 : xorOther b a with
  | some r => simp only [rXOR, h1, h2]; rw [xor_comm']; exact (xorOther_eval h2 σ stk).symm
  | none =>
  simp only [rXOR, h1, h2]
  split
  · next h => subst h; rw [xor_self']; rfl
  split
  · next h => rw [xor_comm', xor_zero_of (isC_eval σ stk h)]
  split
  · next h => rw [xor_zero_of (isC_eval σ stk h)]
  exact comm_eval (o := .XOR) (fun x y => xor_comm' x y) a b σ stk

def rEQ (iz : Term → Term) (a b : Term) : Term :=
  if a = b then c1 else if isC a 0 then iz b else if isC b 0 then iz a
  else if isC a 1 && isBoolT b then b else if isC b 1 && isBoolT a then a else comm .EQ a b
theorem rEQ_eval (iz : Term → Term) (hiz : ∀ t, (iz t).eval σ stk = isZero (t.eval σ stk))
    (a b : Term) : (rEQ iz a b).eval σ stk = UInt256.eq (a.eval σ stk) (b.eval σ stk) := by
  unfold rEQ
  split
  · next h => subst h; rw [eq_self']; rfl
  split
  · next h => rw [hiz, eq_zero_left (isC_eval σ stk h)]
  split
  · next h => rw [hiz, eq_comm', eq_zero_left (isC_eval σ stk h)]
  split
  · next h =>
    simp only [Bool.and_eq_true] at h
    exact (eq_one_of_bool (isC_eval σ stk h.1) (isBoolT_eval σ stk h.2)).symm
  split
  · next h =>
    simp only [Bool.and_eq_true] at h
    rw [eq_comm']; exact (eq_one_of_bool (isC_eval σ stk h.1) (isBoolT_eval σ stk h.2)).symm
  exact comm_eval (o := .EQ) (fun x y => eq_comm' x y) a b σ stk

def rSHL (a b : Term) : Term := if isC a 0 then b else if isC b 0 then c0 else .app2 .SHL a b
theorem rSHL_eval (a b : Term) :
    (rSHL a b).eval σ stk = shiftLeft (b.eval σ stk) (a.eval σ stk) := by
  unfold rSHL
  split
  · next h => rw [shiftLeft_zero_shift (isC_eval σ stk h)]
  split
  · next h => rw [shiftLeft_zero_val (isC_eval σ stk h)]; rfl
  rfl

def rSHR (a b : Term) : Term := if isC a 0 then b else if isC b 0 then c0 else .app2 .SHR a b
theorem rSHR_eval (a b : Term) :
    (rSHR a b).eval σ stk = shiftRight (b.eval σ stk) (a.eval σ stk) := by
  unfold rSHR
  split
  · next h => rw [shiftRight_zero_shift (isC_eval σ stk h)]
  split
  · next h => rw [shiftRight_zero_val (isC_eval σ stk h)]; rfl
  rfl

def rLT (iz : Term → Term) (a b : Term) : Term :=
  if isC b 0 || a = b then .const (ofNat 0) else if isC b 1 then iz a else .app2 .LT a b
theorem rLT_eval (iz : Term → Term) (hiz : ∀ t, (iz t).eval σ stk = isZero (t.eval σ stk))
    (a b : Term) : (rLT iz a b).eval σ stk = UInt256.lt (a.eval σ stk) (b.eval σ stk) := by
  unfold rLT
  split
  · next h =>
    simp only [Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with h | h
    · rw [lt_zero_of (isC_eval σ stk h)]; rfl
    · subst h; rw [lt_self']; rfl
  split
  · next h => rw [hiz, lt_one_right (isC_eval σ stk h)]
  rfl

def rSLT (a b : Term) : Term := if a = b then .const (ofNat 0) else .app2 .SLT a b
theorem rSLT_eval (a b : Term) : (rSLT a b).eval σ stk = UInt256.slt (a.eval σ stk) (b.eval σ stk) := by
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

theorem rules2_eval (o : ArithOp) (a b : Term) (σ : State) (stk : List UInt256) :
    (rules2 o a b).eval σ stk = o.eval [a.eval σ stk, b.eval σ stk] := by
  cases o <;> simp only [rules2]
  all_goals first
    | rfl
    | exact rADD_eval σ stk a b
    | exact rSUB_eval σ stk a b
    | exact rMUL_eval σ stk a b
    | exact rDIV_eval σ stk a b
    | exact rMOD_eval σ stk a b
    | exact rAND_eval σ stk a b
    | exact rOR_eval σ stk a b
    | exact rXOR_eval σ stk a b
    | exact rEQ_eval σ stk _ (fun t => simp1_eval .ISZERO t σ stk) a b
    | exact rLT_eval σ stk _ (fun t => simp1_eval .ISZERO t σ stk) a b
    | exact rLT_eval σ stk _ (fun t => simp1_eval .ISZERO t σ stk) b a
    | exact rSHL_eval σ stk a b
    | exact rSHR_eval σ stk a b
    | exact rSLT_eval σ stk a b
    | exact rSLT_eval σ stk b a

def simp2 (o : ArithOp) (a b : Term) : Term :=
  match a, b with
  | .const x, .const y => .const (o.eval [x, y])
  | a, b => rules2 o a b

theorem simp2_eval (o : ArithOp) (a b : Term) (σ : State) (stk : List UInt256) :
    (simp2 o a b).eval σ stk = o.eval [a.eval σ stk, b.eval σ stk] := by
  unfold simp2
  split
  · rfl
  · exact rules2_eval o a b σ stk

def simp3 (o : ArithOp) (a b c : Term) : Term :=
  match a, b, c with
  | .const x, .const y, .const z => .const (o.eval [x, y, z])
  | a, b, c => .app3 o a b c

theorem simp3_eval (o : ArithOp) (a b c : Term) (σ : State) (stk : List UInt256) :
    (simp3 o a b c).eval σ stk = o.eval [a.eval σ stk, b.eval σ stk, c.eval σ stk] := by
  unfold simp3; split <;> rfl

def norm : Term → Term
  | .var i => .var i
  | .const v => .const v
  | .app1 o a => simp1 o (norm a)
  | .app2 o a b => simp2 o (norm a) (norm b)
  | .app3 o a b c => simp3 o (norm a) (norm b) (norm c)
  | .env0 e => .env0 e
  | .env1 e a => .env1 e (norm a)

theorem norm_eval (σ : State) (stk : List UInt256) : ∀ t : Term, (norm t).eval σ stk = t.eval σ stk
  | .var _ => rfl
  | .const _ => rfl
  | .app1 o a => by rw [norm, simp1_eval, norm_eval σ stk a]; rfl
  | .app2 o a b => by rw [norm, simp2_eval, norm_eval σ stk a, norm_eval σ stk b]; rfl
  | .app3 o a b c => by
    rw [norm, simp3_eval, norm_eval σ stk a, norm_eval σ stk b, norm_eval σ stk c]; rfl
  | .env0 _ => rfl
  | .env1 e a => by rw [norm]; simp only [Term.eval, norm_eval σ stk a]

end EvmOpt
