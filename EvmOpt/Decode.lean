import EvmOpt.Instr

namespace EvmOpt
open EvmSemantics EvmSemantics.EVM

/-- `code` holds `bs` starting at offset `pc`. -/
def CodeAt (code : ByteArray) (pc : Nat) (bs : List UInt8) : Prop :=
  ∀ i (h : i < bs.length), ∃ h' : pc + i < code.size, code[pc + i] = bs[i]

theorem CodeAt.append {code : ByteArray} {pc : Nat} {xs ys : List UInt8} :
    CodeAt code pc (xs ++ ys) ↔ CodeAt code pc xs ∧ CodeAt code (pc + xs.length) ys := by
  constructor
  · intro h
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · obtain ⟨h1, h2⟩ := h i (by simp; omega)
      exact ⟨h1, by rw [h2, List.getElem_append_left]⟩
    · obtain ⟨h1, h2⟩ := h (xs.length + i) (by simp; omega)
      refine ⟨by omega, ?_⟩
      simp only [Nat.add_assoc] at h1 h2 ⊢
      rw [h2, List.getElem_append_right (by omega)]
      simp
  · rintro ⟨hx, hy⟩ i hi
    by_cases hlt : i < xs.length
    · obtain ⟨h1, h2⟩ := hx i hlt
      exact ⟨h1, by rw [h2, List.getElem_append_left]⟩
    · obtain ⟨h1, h2⟩ := hy (i - xs.length) (by simp at hi; omega)
      have e : pc + xs.length + (i - xs.length) = pc + i := by omega
      refine ⟨by omega, ?_⟩
      simp only [e] at h2
      rw [h2, List.getElem_append_right (by omega)]

theorem opcodeOf_arith (o : ArithOp) : Decode.opcodeOf o.byte = some o.toOp := by
  cases o <;> rfl

theorem opcodeOf_dup : ∀ n : Fin 16,
    Decode.opcodeOf (0x80 + n.val).toUInt8 = some (.Dup ⟨n⟩) := by decide

theorem opcodeOf_swap : ∀ n : Fin 16,
    Decode.opcodeOf (0x90 + n.val).toUInt8 = some (.Swap ⟨n⟩) := by decide

theorem opcodeOf_push : ∀ k : Fin 33,
    Decode.opcodeOf (0x5f + k.val).toUInt8 = some (.Push ⟨k⟩) := by decide

theorem extract_of_codeAt {code : ByteArray} {pc : Nat} {bs : List UInt8}
    (h : CodeAt code pc bs) : code.extract pc (pc + bs.length) = ⟨bs.toArray⟩ := by
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  apply Array.ext
  · have := h (bs.length - 1)
    have hs : code.size = code.data.size := rfl
    rcases bs with _ | ⟨b, bs⟩
    · simp; omega
    · obtain ⟨h1, -⟩ := this (by simp)
      simp only [Array.size_extract, List.size_toArray, List.length_cons] at h1 ⊢
      omega
  · intro i h1 h2
    simp only [Array.getElem_extract, List.getElem_toArray]
    simp at h2
    obtain ⟨h3, h4⟩ := h i h2
    rw [← h4, ByteArray.getElem_eq_getElem_data]

/-- What `decodeAt` returns for each instruction kind. -/
def Instr.decoded : Instr → Operation × Option (UInt256 × Nat)
  | .push bs => (.Push ⟨⟨min bs.length 32, by omega⟩⟩, some (pushVal bs, bs.length))
  | i => (i.toOp, none)

theorem decodeAt_of_codeAt {code : ByteArray} {pc : Nat} {i : Instr}
    (h : CodeAt code pc i.bytes) (hw : ∀ bs, i = .push bs → bs.length ≤ 32) :
    Decode.decodeAt code pc = some i.decoded := by
  obtain ⟨hpc, h0⟩ := h 0 (by cases i <;> simp [Instr.bytes])
  simp only [Nat.add_zero] at hpc h0
  unfold Decode.decodeAt
  rw [dif_pos hpc]
  cases i with
  | push bs =>
    have hl := hw bs rfl
    have hc : CodeAt code (pc + 1) bs := by
      have := (CodeAt.append (xs := [(0x5f + bs.length).toUInt8]) (ys := bs)).1 h
      simpa using this.2
    have hb : code[pc] = (0x5f + bs.length).toUInt8 := by simpa [Instr.bytes] using h0
    have hop : Decode.opcodeOf (0x5f + bs.length).toUInt8 = some (.Push ⟨⟨bs.length, by omega⟩⟩) :=
      opcodeOf_push ⟨bs.length, by omega⟩
    have hm : min bs.length 32 = bs.length := by omega
    rw [hb, hop]
    simp [extract_of_codeAt hc, Instr.decoded, hm, pushVal]
  | dup n =>
    have hb : code[pc] = (0x80 + n.val).toUInt8 := by simpa [Instr.bytes] using h0
    rw [hb, opcodeOf_dup]
    simp [Instr.decoded, Instr.toOp]
  | swap n =>
    have hb : code[pc] = (0x90 + n.val).toUInt8 := by simpa [Instr.bytes] using h0
    rw [hb, opcodeOf_swap]
    simp [Instr.decoded, Instr.toOp]
  | pop =>
    have hb : code[pc] = 0x50 := by simpa [Instr.bytes] using h0
    simp [hb, Instr.decoded, Instr.toOp]
    rfl
  | op o =>
    have hb : code[pc] = o.byte := by simpa [Instr.bytes] using h0
    simp only [hb, opcodeOf_arith, Instr.decoded, Instr.toOp]
    cases o <;> rfl

end EvmOpt
