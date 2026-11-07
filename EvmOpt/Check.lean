import EvmOpt.Lift
import EvmOpt.Norm

namespace EvmOpt
open EvmSemantics EvmSemantics.EVM

/-- Translation validation: `b'` computes the same stack as `b` from every input on which
    `b` succeeds, at no higher gas. -/
def check (f : Fork) (b b' : Block) : Bool :=
  match lift f b, lift f b' with
  | some S, some S' =>
    decide (S'.d ≤ S.d) && decide (S.slack + ((S.d : Int) - S'.d) ≤ S'.slack) &&
    decide (cost f b' ≤ cost f b) &&
    (S.ts.map norm == (S'.ts ++ vars S'.d (S.d - S'.d)).map norm)
  | _, _ => false

theorem conc_init (ρ : Ctx) : conc ρ SState.init = ρ.stk := by
  simp [conc, SState.init]

theorem run_lift {f : Fork} {σ : State} {b : Block} {stk : List UInt256} (hl : stk.length ≤ 1024) :
    run f σ b stk = match lift f b with
      | none => none
      | some S => if S.d ≤ stk.length ∧ (stk.length : Int) - S.d ≤ S.slack
                  then some (conc ⟨σ, stk, [], fun _ => 0⟩ S) else none := by
  have := srun_run f ⟨σ, stk, [], fun _ => 0⟩ b SState.init (by simp [SState.init])
    (by simp [SState.init]; omega)
  rwa [conc_init] at this

theorem map_eval_of_norm {ρ : Ctx} {l1 l2 : List Term}
    (h : l1.map norm = l2.map norm) : l1.map (·.eval ρ) = l2.map (·.eval ρ) := by
  have e : ∀ l : List Term, l.map (·.eval ρ) = (l.map norm).map (·.eval ρ) := by
    intro l; simp [norm_eval]
  rw [e l1, e l2, h]

theorem check_sound {f : Fork} {σ : State} {b b' : Block} {stk r : List UInt256}
    (hc : check f b b' = true) (hl : stk.length ≤ 1024) (hr : run f σ b stk = some r) :
    run f σ b' stk = some r ∧ cost f b' ≤ cost f b := by
  unfold check at hc
  split at hc <;> try contradiction
  next S S' hS hS' =>
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
  obtain ⟨⟨⟨hd, hsl⟩, hcost⟩, hts⟩ := hc
  rw [run_lift hl, hS] at hr
  simp only at hr
  split at hr <;> try contradiction
  next hcond =>
  simp only [Option.some.injEq] at hr
  subst hr
  refine ⟨?_, hcost⟩
  rw [run_lift hl, hS']
  simp only
  rw [if_pos ⟨by omega, by omega⟩]
  congr 1
  have hv := vars_eval ⟨σ, stk, [], fun _ => 0⟩ S'.d (S.d - S'.d) (by simp; omega)
  simp only [conc]
  have hdrop : stk.drop S'.d = (stk.drop S'.d).take (S.d - S'.d) ++ stk.drop S.d := by
    conv => lhs; rw [← List.take_append_drop (S.d - S'.d) (stk.drop S'.d)]
    rw [List.drop_drop]; congr 2; omega
  rw [hdrop, ← hv, ← List.append_assoc, ← List.map_append, map_eval_of_norm (ρ := ⟨σ, stk, [], fun _ => 0⟩) hts]

/-- Keep the candidate only if the checker accepts it. -/
def optimizeWith (f : Fork) (rw : Block → Block) (b : Block) : Block :=
  let b' := rw b
  if check f b b' then b' else b

theorem optimizeWith_sound {f : Fork} {σ : State} {rw : Block → Block} {b : Block} {stk r : List UInt256}
    (hl : stk.length ≤ 1024) (hr : run f σ b stk = some r) :
    run f σ (optimizeWith f rw b) stk = some r ∧ cost f (optimizeWith f rw b) ≤ cost f b := by
  unfold optimizeWith
  dsimp only
  split
  · next h => exact check_sound h hl hr
  · exact ⟨hr, Nat.le_refl _⟩

/-- **End-to-end guarantee.** If the original block `b` would run to completion on `s`
    (stack fits, enough gas for `b`), then with the optimised block in the code the
    specification reaches the same stack, with pc past the new block and at least as much
    gas left as `b` would leave. -/
theorem optimizeWith_steps {rw : Block → Block} {b : Block} {s : State} {r : List UInt256}
    (hready : Ready s)
    (hcode : CodeAt s.executionEnv.code s.pc.toNat (encode (optimizeWith s.fork rw b)))
    (hpc : s.pc.toNat + (encode (optimizeWith s.fork rw b)).length < UInt256.size)
    (hgas : cost s.fork b ≤ s.gasAvailable) (hl : s.stack.length ≤ 1024)
    (hrun : run s.fork s b s.stack = some r) :
    Steps s (blockPost s (optimizeWith s.fork rw b) r) ∧
      s.gasAvailable - cost s.fork b ≤ (blockPost s (optimizeWith s.fork rw b) r).gasAvailable := by
  obtain ⟨hrun', hcost⟩ := optimizeWith_sound (rw := rw) hl hrun
  exact ⟨run_sound _ s r hready hcode hpc (by omega) hrun', by simp only [blockPost]; omega⟩

end EvmOpt
