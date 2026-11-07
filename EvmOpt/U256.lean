import EvmOpt.Sound

namespace EvmSemantics.UInt256

theorem ext_toNat {a b : UInt256} (h : a.toNat = b.toNat) : a = b := EvmOpt.UInt256.ext' h

theorem toNat_lt (a : UInt256) : a.toNat < size := a.val.isLt

theorem size_eq : size = 2 ^ 256 := rfl

@[simp] theorem toNat_mk0 : (⟨0⟩ : UInt256).toNat = 0 := rfl

theorem toNat_ofNat' (n : Nat) : (ofNat n).toNat = n % size := rfl

theorem toNat_ofNat_small {n : Nat} (h : n < size) : (ofNat n).toNat = n := by
  rw [toNat_ofNat']; exact Nat.mod_eq_of_lt h

@[simp] theorem toNat_ofNat_zero : (ofNat 0).toNat = 0 := rfl
@[simp] theorem toNat_ofNat_one : (ofNat 1).toNat = 1 := rfl

theorem toNat_add' (a b : UInt256) : (a + b).toNat = (a.toNat + b.toNat) % size := rfl
theorem toNat_sub' (a b : UInt256) : (a - b).toNat = (size - b.toNat + a.toNat) % size := rfl
theorem toNat_mul' (a b : UInt256) : (a * b).toNat = (a.toNat * b.toNat) % size := rfl
theorem toNat_land (a b : UInt256) : (land a b).toNat = (a.toNat &&& b.toNat) % size := rfl
theorem toNat_lor (a b : UInt256) : (lor a b).toNat = (a.toNat ||| b.toNat) % size := rfl
theorem toNat_xor (a b : UInt256) : (xor a b).toNat = (a.toNat ^^^ b.toNat) % size := rfl

theorem add_zero_of {a b : UInt256} (h : b.toNat = 0) : a + b = a := by
  apply ext_toNat; rw [toNat_add', h, Nat.add_zero, Nat.mod_eq_of_lt (toNat_lt a)]

theorem add_comm' (a b : UInt256) : a + b = b + a := by
  apply ext_toNat; rw [toNat_add', toNat_add', Nat.add_comm]

theorem sub_zero_of {a b : UInt256} (h : b.toNat = 0) : a - b = a := by
  apply ext_toNat
  rw [toNat_sub', h, Nat.sub_zero, Nat.add_comm, Nat.add_mod_right,
    Nat.mod_eq_of_lt (toNat_lt a)]

theorem sub_self' (a : UInt256) : a - a = ⟨0⟩ := by
  apply ext_toNat
  have := toNat_lt a
  rw [toNat_sub', toNat_mk0, Nat.sub_add_cancel (by omega), Nat.mod_self]

theorem mul_one_of {a b : UInt256} (h : b.toNat = 1) : a * b = a := by
  apply ext_toNat; rw [toNat_mul', h, Nat.mul_one, Nat.mod_eq_of_lt (toNat_lt a)]

theorem mul_zero_of {a b : UInt256} (h : b.toNat = 0) : a * b = ⟨0⟩ := by
  apply ext_toNat; rw [toNat_mul', h, Nat.mul_zero, Nat.zero_mod]; rfl

theorem mul_comm' (a b : UInt256) : a * b = b * a := by
  apply ext_toNat; rw [toNat_mul', toNat_mul', Nat.mul_comm]

theorem div_one_of {a b : UInt256} (h : b.toNat = 1) : a / b = a := by
  show div a b = a
  unfold div
  have h' : b.val.val = 1 := h
  rw [if_neg (by omega)]
  apply ext_toNat
  show (a.val / b.val).val = a.toNat
  rw [Fin.div_val, h']; exact Nat.div_one _

theorem mod_self' (a : UInt256) : a % a = ⟨0⟩ := by
  show mod a a = _
  unfold mod
  split
  · rfl
  · apply ext_toNat; show (a.val % a.val).val = 0; rw [Fin.mod_val, Nat.mod_self]

theorem mod_one_of {a b : UInt256} (h : b.toNat = 1) : a % b = ⟨0⟩ := by
  show mod a b = _
  unfold mod
  have h' : b.val.val = 1 := h
  rw [if_neg (by omega)]
  apply ext_toNat; show (a.val % b.val).val = 0; rw [Fin.mod_val, h', Nat.mod_one]

theorem mod_zero_of {a b : UInt256} (h : b.toNat = 0) : a % b = ⟨0⟩ := by
  show mod a b = _
  unfold mod
  have h' : b.val.val = 0 := h
  rw [if_pos h']

theorem land_self' (a : UInt256) : land a a = a := by
  apply ext_toNat; rw [toNat_land, Nat.and_self, Nat.mod_eq_of_lt (toNat_lt a)]

theorem land_zero_of {a b : UInt256} (h : b.toNat = 0) : land a b = ⟨0⟩ := by
  apply ext_toNat; rw [toNat_land, h, Nat.and_zero, Nat.zero_mod]; rfl

theorem land_max_of {a b : UInt256} (h : b.toNat = size - 1) : land a b = a := by
  apply ext_toNat
  rw [toNat_land, h, size_eq, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod]
  exact Nat.mod_eq_of_lt (toNat_lt a)

theorem land_comm' (a b : UInt256) : land a b = land b a := by
  apply ext_toNat; rw [toNat_land, toNat_land, Nat.and_comm]

theorem lor_self' (a : UInt256) : lor a a = a := by
  apply ext_toNat; rw [toNat_lor, Nat.or_self, Nat.mod_eq_of_lt (toNat_lt a)]

theorem lor_zero_of {a b : UInt256} (h : b.toNat = 0) : lor a b = a := by
  apply ext_toNat; rw [toNat_lor, h, Nat.or_zero, Nat.mod_eq_of_lt (toNat_lt a)]

theorem lor_comm' (a b : UInt256) : lor a b = lor b a := by
  apply ext_toNat; rw [toNat_lor, toNat_lor, Nat.or_comm]

theorem xor_self' (a : UInt256) : xor a a = ⟨0⟩ := by
  apply ext_toNat; rw [toNat_xor, Nat.xor_self, Nat.zero_mod]; rfl

theorem xor_zero_of {a b : UInt256} (h : b.toNat = 0) : xor a b = a := by
  apply ext_toNat; rw [toNat_xor, h, Nat.xor_zero, Nat.mod_eq_of_lt (toNat_lt a)]

theorem xor_comm' (a b : UInt256) : xor a b = xor b a := by
  apply ext_toNat; rw [toNat_xor, toNat_xor, Nat.xor_comm]

theorem eq_self' (a : UInt256) : eq a a = ofNat 1 := by simp [eq]

theorem eq_comm' (a b : UInt256) : eq a b = eq b a := by
  unfold eq; by_cases h : a.toNat = b.toNat <;> simp [h, Eq.comm]

theorem lt_zero_of {a b : UInt256} (h : b.toNat = 0) : lt a b = ofNat 0 := by
  simp [lt, h]

theorem lt_self' (a : UInt256) : lt a a = ofNat 0 := by simp [lt]

theorem gt_eq_lt (a b : UInt256) : gt a b = lt b a := rfl

theorem sgt_eq_slt (a b : UInt256) : sgt a b = slt b a := rfl

theorem slt_self' (a : UInt256) : slt a a = ofNat 0 := by simp [slt]

theorem isZero_isZero_isZero (a : UInt256) : isZero (isZero (isZero a)) = isZero a := by
  unfold isZero
  by_cases h : a.toNat = 0 <;> simp [h]

theorem lnot_lnot (a : UInt256) : lnot (lnot a) = a := by
  apply ext_toNat
  have := toNat_lt a
  unfold lnot
  rw [toNat_ofNat_small (by omega), toNat_ofNat_small (by omega)]
  omega

end EvmSemantics.UInt256
