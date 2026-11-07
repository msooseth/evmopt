import EvmOpt.Check

namespace EvmOpt
open EvmSemantics EvmSemantics.EVM

theorem run_append (f : Fork) (p q : Block) (stk : List UInt256) :
    run f (p ++ q) stk = (run f p stk).bind (run f q) := by
  induction p generalizing stk with
  | nil => simp [run]
  | cons i p ih =>
    simp only [List.cons_append, run]
    cases i.exec f stk <;> simp [ih]

theorem cost_append (f : Fork) (p q : Block) : cost f (p ++ q) = cost f p + cost f q := by
  induction p with
  | nil => simp [cost]
  | cons i p ih => simp [cost, ih, Nat.add_assoc]

theorem run_length_le {f : Fork} {b : Block} {stk r : List UInt256}
    (h : run f b stk = some r) (hl : stk.length ≤ 1024) : r.length ≤ 1024 := by
  induction b generalizing stk with
  | nil => simp [run] at h; subst h; exact hl
  | cons i b ih =>
    simp only [run, Option.bind_eq_some_iff] at h
    obtain ⟨m, hm, hr⟩ := h
    exact ih hr (Instr.exec_eq_some.1 hm).2.2

/-- A local rewrite proposal at the head of a block: replace the first `k` instructions. -/
abbrev Rule := Fork → Block → Option (Nat × Block)

/-- One left-to-right pass; each proposal is kept only if `check` accepts the window. -/
def pass (f : Fork) (rule : Rule) (b : Block) : Block :=
  match b with
  | [] => []
  | i :: rest =>
    match rule f (i :: rest) with
    | some (k, w') =>
      if 0 < k ∧ check f ((i :: rest).take k) w' then w' ++ pass f rule ((i :: rest).drop k)
      else i :: pass f rule rest
    | none => i :: pass f rule rest
termination_by b.length
decreasing_by all_goals simp_wf; all_goals omega

theorem pass_sound (f : Fork) (rule : Rule) (b : Block) : ∀ {stk r : List UInt256},
    stk.length ≤ 1024 → run f b stk = some r →
    run f (pass f rule b) stk = some r ∧ cost f (pass f rule b) ≤ cost f b := by
  induction b using pass.induct (f := f) (rule := rule) with
  | case1 => intro stk r _ h; simpa [pass] using h
  | case2 i rest k w' hrule hk ih =>
    intro stk r hl h
    rw [pass, hrule]
    simp only [if_pos hk]
    have hsplit : i :: rest = (i :: rest).take k ++ (i :: rest).drop k := (List.take_append_drop _ _).symm
    rw [hsplit, run_append] at h
    obtain ⟨mid, hmid, hrest⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨hw, hcw⟩ := check_sound hk.2 hl hmid
    have hml : mid.length ≤ 1024 := run_length_le hmid hl
    obtain ⟨h1, h2⟩ := ih hml hrest
    refine ⟨by rw [run_append, hw, Option.bind_some, h1], ?_⟩
    rw [cost_append]
    conv => rhs; rw [hsplit, cost_append]
    omega
  | case3 i rest k w' hrule hk ih =>
    intro stk r hl h
    rw [pass, hrule]
    simp only [if_neg hk]
    simp only [run, Option.bind_eq_some_iff] at h
    obtain ⟨m, hm, hr⟩ := h
    obtain ⟨h1, h2⟩ := ih (Instr.exec_eq_some.1 hm).2.2 hr
    exact ⟨by simp [run, hm, h1], by simp only [cost]; omega⟩
  | case4 i rest hrule ih =>
    intro stk r hl h
    rw [pass, hrule]
    simp only [run, Option.bind_eq_some_iff] at h
    obtain ⟨m, hm, hr⟩ := h
    obtain ⟨h1, h2⟩ := ih (Instr.exec_eq_some.1 hm).2.2 hr
    exact ⟨by simp [run, hm, h1], by simp only [cost]; omega⟩

def passes (f : Fork) (rule : Rule) : Nat → Block → Block
  | 0, b => b
  | n + 1, b => passes f rule n (pass f rule b)

theorem passes_sound (f : Fork) (rule : Rule) (n : Nat) (b : Block) {stk r : List UInt256}
    (hl : stk.length ≤ 1024) (h : run f b stk = some r) :
    run f (passes f rule n b) stk = some r ∧ cost f (passes f rule n b) ≤ cost f b := by
  induction n generalizing b with
  | zero => exact ⟨h, Nat.le_refl _⟩
  | succ n ih =>
    obtain ⟨h1, h2⟩ := pass_sound f rule b hl h
    obtain ⟨h3, h4⟩ := ih _ h1
    exact ⟨h3, by simp only [passes]; omega⟩

end EvmOpt
