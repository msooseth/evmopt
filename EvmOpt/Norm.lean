import EvmOpt.Term
import EvmOpt.U256

namespace EvmOpt
open EvmSemantics EvmSemantics.EVM UInt256

/-- `t` is the constant `n`. -/
def isC (t : Term) (n : Nat) : Bool :=
  match t with
  | .const v => v.toNat == n
  | _ => false

theorem isC_eval {t : Term} {n : Nat} (ρ : Ctx) (h : isC t n = true) :
    (t.eval ρ).toNat = n := by
  cases t <;> simp_all [isC, Term.eval]

/-- Order the arguments of a commutative operation. -/
def comm (o : ArithOp) (a b : Term) : Term :=
  if compare b a == .lt then .app2 o b a else .app2 o a b

theorem comm_eval {o : ArithOp} (hc : ∀ x y, o.eval [x, y] = o.eval [y, x]) (a b : Term)
    (ρ : Ctx) : (comm o a b).eval ρ = o.eval [a.eval ρ, b.eval ρ] := by
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

theorem isAddr_lt {t : Term} (ρ : Ctx) (h : isAddr t = true) :
    (t.eval ρ).toNat < 2 ^ 160 := by
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

theorem isBoolT_eval {t : Term} (ρ : Ctx) (h : isBoolT t = true) :
    IsBool (t.eval ρ) := by
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

theorem izRule_eval (a : Term) (ρ : Ctx) :
    (izRule a).eval ρ = isZero (a.eval ρ) := by
  unfold izRule
  split
  · next x =>
    split
    · next h =>
      simp only [Term.eval, ArithOp.eval]
      exact (isZero_isZero_of_bool (isBoolT_eval ρ h)).symm
    · rfl
  · next z x =>
    split
    · next h => simp only [Term.eval, ArithOp.eval]; rw [isZero_lt_zero_left (isC_eval ρ h)]
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

theorem simp1_eval (o : ArithOp) (a : Term) (ρ : Ctx) :
    (simp1 o a).eval ρ = o.eval [a.eval ρ] := by
  unfold simp1
  split
  · rfl
  · split
    · exact izRule_eval _ ρ
    · simp only [Term.eval, ArithOp.eval]; rw [lnot_lnot]
    · rfl

/-- `t` is the constant `2^k` with `k ≥ 1`: the `k`. -/
def pow2? (t : Term) : Option Nat :=
  match t with
  | .const v => if 2 ≤ v.toNat ∧ 2 ^ Nat.log2 v.toNat = v.toNat then some (Nat.log2 v.toNat) else none
  | _ => none

theorem pow2_eval {t : Term} {k : Nat} (h : pow2? t = some k) (ρ : Ctx) :
    t.eval ρ = shiftLeft (ofNat 1) (ofNat k) := by
  unfold pow2? at h
  split at h
  · next v =>
    split at h
    · next hc =>
      simp only [Option.some.injEq] at h; subst h
      exact eq_shl_one_of_pow hc.2.symm (pow_log_lt hc.2 (toNat_lt v))
    · contradiction
  · contradiction

/-- `t = SHL(y, 1)`: the `y`. -/
def shlOne? (t : Term) : Option Term :=
  match t with
  | .app2 .SHL y one => if isC one 1 then some y else none
  | _ => none

theorem shlOne_eval {t y : Term} (h : shlOne? t = some y) (ρ : Ctx) :
    ∃ one : UInt256, one.toNat = 1 ∧ t.eval ρ = shiftLeft one (y.eval ρ) := by
  unfold shlOne? at h
  split at h
  · next y' one =>
    split at h
    · next h1 =>
      simp only [Option.some.injEq] at h; subst h
      exact ⟨_, isC_eval ρ h1, rfl⟩
    · contradiction
  · contradiction

section rules
variable (ρ : Ctx)

def rADD (a b : Term) : Term := if isC a 0 then b else if isC b 0 then a else comm .ADD a b
theorem rADD_eval (a b : Term) : (rADD a b).eval ρ = a.eval ρ + b.eval ρ := by
  unfold rADD
  split
  · next h => rw [add_comm', add_zero_of (isC_eval ρ h)]
  split
  · next h => rw [add_zero_of (isC_eval ρ h)]
  exact comm_eval (o := .ADD) (fun x y => add_comm' x y) a b ρ

def rSUB (a b : Term) : Term := if isC b 0 then a else if a = b then c0 else .app2 .SUB a b
theorem rSUB_eval (a b : Term) : (rSUB a b).eval ρ = a.eval ρ - b.eval ρ := by
  unfold rSUB
  split
  · next h => rw [sub_zero_of (isC_eval ρ h)]
  split
  · next h => subst h; rw [sub_self']; rfl
  rfl

def rMUL (a b : Term) : Term :=
  if isC a 0 || isC b 0 then c0 else if isC a 1 then b else if isC b 1 then a
  else match shlOne? b, shlOne? a with
    | some y, _ => .app2 .SHL y a
    | none, some y => .app2 .SHL y b
    | none, none => match pow2? b, pow2? a with
      | some k, _ => .app2 .SHL (.const (ofNat k)) a
      | none, some k => .app2 .SHL (.const (ofNat k)) b
      | none, none => comm .MUL a b
theorem rMUL_eval (a b : Term) : (rMUL a b).eval ρ = a.eval ρ * b.eval ρ := by
  unfold rMUL
  split
  · next h =>
    simp only [Bool.or_eq_true] at h
    rcases h with h | h
    · rw [mul_comm', mul_zero_of (isC_eval ρ h)]; rfl
    · rw [mul_zero_of (isC_eval ρ h)]; rfl
  split
  · next h => rw [mul_comm', mul_one_of (isC_eval ρ h)]
  split
  · next h => rw [mul_one_of (isC_eval ρ h)]
  cases hb : shlOne? b with
  | some y =>
    obtain ⟨one, h1, he⟩ := shlOne_eval hb ρ
    show shiftLeft (a.eval ρ) (y.eval ρ) = a.eval ρ * b.eval ρ
    rw [he, mul_shl_one h1]
  | none =>
  cases ha : shlOne? a with
  | some y =>
    obtain ⟨one, h1, he⟩ := shlOne_eval ha ρ
    show shiftLeft (b.eval ρ) (y.eval ρ) = a.eval ρ * b.eval ρ
    rw [he, mul_comm', mul_shl_one h1]
  | none =>
  cases hpb : pow2? b with
  | some k =>
    show shiftLeft (a.eval ρ) (ofNat k) = a.eval ρ * b.eval ρ
    rw [pow2_eval hpb ρ, mul_shl_one toNat_ofNat_one]
  | none =>
  cases hpa : pow2? a with
  | some k =>
    show shiftLeft (b.eval ρ) (ofNat k) = a.eval ρ * b.eval ρ
    rw [pow2_eval hpa ρ, mul_comm', mul_shl_one toNat_ofNat_one]
  | none => exact comm_eval (o := .MUL) (fun x y => mul_comm' x y) a b ρ

def rDIV (a b : Term) : Term :=
  if isC b 1 then a else match shlOne? b with
    | some y => .app2 .SHR y a
    | none => match pow2? b with
      | some k => .app2 .SHR (.const (ofNat k)) a
      | none => .app2 .DIV a b
theorem rDIV_eval (a b : Term) : (rDIV a b).eval ρ = a.eval ρ / b.eval ρ := by
  unfold rDIV
  split
  · next h => rw [div_one_of (isC_eval ρ h)]
  cases hb : shlOne? b with
  | some y =>
    obtain ⟨one, h1, he⟩ := shlOne_eval hb ρ
    show shiftRight (a.eval ρ) (y.eval ρ) = a.eval ρ / b.eval ρ
    rw [he, div_shl_one h1]
  | none =>
  cases hpb : pow2? b with
  | some k =>
    show shiftRight (a.eval ρ) (ofNat k) = a.eval ρ / b.eval ρ
    rw [pow2_eval hpb ρ, div_shl_one toNat_ofNat_one]
  | none => rfl

def rMOD (a b : Term) : Term :=
  if isC b 0 || isC b 1 || a = b then c0 else .app2 .MOD a b
theorem rMOD_eval (a b : Term) : (rMOD a b).eval ρ = a.eval ρ % b.eval ρ := by
  unfold rMOD
  split
  · next h =>
    simp only [Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with (h | h) | h
    · rw [mod_zero_of (isC_eval ρ h)]; rfl
    · rw [mod_one_of (isC_eval ρ h)]; rfl
    · subst h; rw [mod_self']; rfl
  rfl

def isMax (t : Term) : Bool := isC t (UInt256.size - 1)

def rAND (a b : Term) : Term :=
  if hasArg .AND a b || hasArg .OR b a then a else if hasArg .AND b a || hasArg .OR a b then b
  else if isC a 0 || isC b 0 then c0 else if a = b then a else if isMax a then b
  else if isMax b then a else if isAddr a && isC b mask160 then a
  else if isAddr b && isC a mask160 then b else comm .AND a b
theorem rAND_eval (a b : Term) : (rAND a b).eval ρ = land (a.eval ρ) (b.eval ρ) := by
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
    · rw [land_comm', land_zero_of (isC_eval ρ h)]; rfl
    · rw [land_zero_of (isC_eval ρ h)]; rfl
  split
  · next h => subst h; rw [land_self']
  split
  · next h => rw [land_comm', land_max_of (isC_eval ρ h)]
  split
  · next h => rw [land_max_of (isC_eval ρ h)]
  split
  · next h =>
    simp only [Bool.and_eq_true] at h
    exact (land_mask_of_lt (isAddr_lt ρ h.1) (isC_eval ρ h.2)).symm
  split
  · next h =>
    simp only [Bool.and_eq_true] at h
    rw [land_comm']; exact (land_mask_of_lt (isAddr_lt ρ h.1) (isC_eval ρ h.2)).symm
  exact comm_eval (o := .AND) (fun x y => land_comm' x y) a b ρ

def rOR (a b : Term) : Term :=
  if hasArg .OR a b || hasArg .AND b a then a else if hasArg .OR b a || hasArg .AND a b then b
  else if a = b then a else if isC a 0 then b else if isC b 0 then a else comm .OR a b
theorem rOR_eval (a b : Term) : (rOR a b).eval ρ = lor (a.eval ρ) (b.eval ρ) := by
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
  · next h => rw [lor_comm', lor_zero_of (isC_eval ρ h)]
  split
  · next h => rw [lor_zero_of (isC_eval ρ h)]
  exact comm_eval (o := .OR) (fun x y => lor_comm' x y) a b ρ

def rXOR (a b : Term) : Term :=
  match xorOther a b, xorOther b a with
  | some r, _ => r
  | none, some r => r
  | none, none =>
    if a = b then c0 else if isC a 0 then b else if isC b 0 then a else comm .XOR a b

theorem xorOther_eval {t z r : Term} (h : xorOther t z = some r) (ρ : Ctx) :
    xor (t.eval ρ) (z.eval ρ) = r.eval ρ := by
  unfold xorOther at h
  split at h
  · next x y =>
    split at h
    · next hz => simp only [Option.some.injEq] at h; subst h hz; exact xor_cancel_left _ _
    split at h
    · next hz => simp only [Option.some.injEq] at h; subst h hz; exact xor_cancel_right _ _
    contradiction
  · contradiction

theorem rXOR_eval (a b : Term) : (rXOR a b).eval ρ = xor (a.eval ρ) (b.eval ρ) := by
  cases h1 : xorOther a b with
  | some r => simp only [rXOR, h1]; exact (xorOther_eval h1 ρ).symm
  | none =>
  cases h2 : xorOther b a with
  | some r => simp only [rXOR, h1, h2]; rw [xor_comm']; exact (xorOther_eval h2 ρ).symm
  | none =>
  simp only [rXOR, h1, h2]
  split
  · next h => subst h; rw [xor_self']; rfl
  split
  · next h => rw [xor_comm', xor_zero_of (isC_eval ρ h)]
  split
  · next h => rw [xor_zero_of (isC_eval ρ h)]
  exact comm_eval (o := .XOR) (fun x y => xor_comm' x y) a b ρ

def rEQ (iz : Term → Term) (a b : Term) : Term :=
  if a = b then c1 else if isC a 0 then iz b else if isC b 0 then iz a
  else if isC a 1 && isBoolT b then b else if isC b 1 && isBoolT a then a else comm .EQ a b
theorem rEQ_eval (iz : Term → Term) (hiz : ∀ t, (iz t).eval ρ = isZero (t.eval ρ))
    (a b : Term) : (rEQ iz a b).eval ρ = UInt256.eq (a.eval ρ) (b.eval ρ) := by
  unfold rEQ
  split
  · next h => subst h; rw [eq_self']; rfl
  split
  · next h => rw [hiz, eq_zero_left (isC_eval ρ h)]
  split
  · next h => rw [hiz, eq_comm', eq_zero_left (isC_eval ρ h)]
  split
  · next h =>
    simp only [Bool.and_eq_true] at h
    exact (eq_one_of_bool (isC_eval ρ h.1) (isBoolT_eval ρ h.2)).symm
  split
  · next h =>
    simp only [Bool.and_eq_true] at h
    rw [eq_comm']; exact (eq_one_of_bool (isC_eval ρ h.1) (isBoolT_eval ρ h.2)).symm
  exact comm_eval (o := .EQ) (fun x y => eq_comm' x y) a b ρ

def rSHL (a b : Term) : Term := if isC a 0 then b else if isC b 0 then c0 else .app2 .SHL a b
theorem rSHL_eval (a b : Term) :
    (rSHL a b).eval ρ = shiftLeft (b.eval ρ) (a.eval ρ) := by
  unfold rSHL
  split
  · next h => rw [shiftLeft_zero_shift (isC_eval ρ h)]
  split
  · next h => rw [shiftLeft_zero_val (isC_eval ρ h)]; rfl
  rfl

def rSHR (a b : Term) : Term := if isC a 0 then b else if isC b 0 then c0 else .app2 .SHR a b
theorem rSHR_eval (a b : Term) :
    (rSHR a b).eval ρ = shiftRight (b.eval ρ) (a.eval ρ) := by
  unfold rSHR
  split
  · next h => rw [shiftRight_zero_shift (isC_eval ρ h)]
  split
  · next h => rw [shiftRight_zero_val (isC_eval ρ h)]; rfl
  rfl

def rLT (iz : Term → Term) (a b : Term) : Term :=
  if isC b 0 || a = b then .const (ofNat 0) else if isC b 1 then iz a else .app2 .LT a b
theorem rLT_eval (iz : Term → Term) (hiz : ∀ t, (iz t).eval ρ = isZero (t.eval ρ))
    (a b : Term) : (rLT iz a b).eval ρ = UInt256.lt (a.eval ρ) (b.eval ρ) := by
  unfold rLT
  split
  · next h =>
    simp only [Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with h | h
    · rw [lt_zero_of (isC_eval ρ h)]; rfl
    · subst h; rw [lt_self']; rfl
  split
  · next h => rw [hiz, lt_one_right (isC_eval ρ h)]
  rfl

def rSLT (a b : Term) : Term := if a = b then .const (ofNat 0) else .app2 .SLT a b
theorem rSLT_eval (a b : Term) : (rSLT a b).eval ρ = UInt256.slt (a.eval ρ) (b.eval ρ) := by
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

theorem rules2_eval (o : ArithOp) (a b : Term) (ρ : Ctx) :
    (rules2 o a b).eval ρ = o.eval [a.eval ρ, b.eval ρ] := by
  cases o <;> simp only [rules2]
  all_goals first
    | rfl
    | exact rADD_eval ρ a b
    | exact rSUB_eval ρ a b
    | exact rMUL_eval ρ a b
    | exact rDIV_eval ρ a b
    | exact rMOD_eval ρ a b
    | exact rAND_eval ρ a b
    | exact rOR_eval ρ a b
    | exact rXOR_eval ρ a b
    | exact rEQ_eval ρ _ (fun t => simp1_eval .ISZERO t ρ) a b
    | exact rLT_eval ρ _ (fun t => simp1_eval .ISZERO t ρ) a b
    | exact rLT_eval ρ _ (fun t => simp1_eval .ISZERO t ρ) b a
    | exact rSHL_eval ρ a b
    | exact rSHR_eval ρ a b
    | exact rSLT_eval ρ a b
    | exact rSLT_eval ρ b a

def simp2 (o : ArithOp) (a b : Term) : Term :=
  match a, b with
  | .const x, .const y => .const (o.eval [x, y])
  | a, b => rules2 o a b

theorem simp2_eval (o : ArithOp) (a b : Term) (ρ : Ctx) :
    (simp2 o a b).eval ρ = o.eval [a.eval ρ, b.eval ρ] := by
  unfold simp2
  split
  · rfl
  · exact rules2_eval o a b ρ

def simp3 (o : ArithOp) (a b c : Term) : Term :=
  match a, b, c with
  | .const x, .const y, .const z => .const (o.eval [x, y, z])
  | a, b, c => .app3 o a b c

theorem simp3_eval (o : ArithOp) (a b c : Term) (ρ : Ctx) :
    (simp3 o a b c).eval ρ = o.eval [a.eval ρ, b.eval ρ, c.eval ρ] := by
  unfold simp3; split <;> rfl

def norm : Term → Term
  | .var i => .var i
  | .const v => .const v
  | .app1 o a => simp1 o (norm a)
  | .app2 o a b => simp2 o (norm a) (norm b)
  | .app3 o a b c => simp3 o (norm a) (norm b) (norm c)
  | .env0 e => .env0 e
  | .env1 e a => .env1 e (norm a)
  | .eff i => .eff i
  | .tag k => .tag k

theorem norm_eval (ρ : Ctx) : ∀ t : Term, (norm t).eval ρ = t.eval ρ
  | .var _ => rfl
  | .const _ => rfl
  | .app1 o a => by rw [norm, simp1_eval, norm_eval ρ a]; rfl
  | .app2 o a b => by rw [norm, simp2_eval, norm_eval ρ a, norm_eval ρ b]; rfl
  | .app3 o a b c => by
    rw [norm, simp3_eval, norm_eval ρ a, norm_eval ρ b, norm_eval ρ c]; rfl
  | .env0 _ => rfl
  | .env1 e a => by rw [norm]; simp only [Term.eval, norm_eval ρ a]
  | .eff _ => rfl
  | .tag _ => rfl

end EvmOpt
