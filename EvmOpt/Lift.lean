import EvmOpt.Term

namespace EvmOpt
open EvmSemantics EvmSemantics.EVM

theorem conc_length (stk : List UInt256) (S : SState) :
    (conc stk S).length = S.ts.length + (stk.length - S.d) := by
  simp [conc]

theorem vars_eval (stk : List UInt256) (a n : Nat) (h : a + n ≤ stk.length) :
    (vars a n).map (·.eval stk) = (stk.drop a).take n := by
  apply List.ext_getElem
  · simp [vars]; omega
  · intro j h1 h2
    simp [vars, Term.eval] at h1 ⊢
    simp [List.getElem?_eq_getElem (by omega : a + j < stk.length)]

theorem conc_ensure (stk : List UInt256) (S : SState) (k : Nat)
    (h : S.d + (k - S.ts.length) ≤ stk.length) : conc stk (ensure k S) = conc stk S := by
  simp only [conc, ensure, List.map_append, List.append_assoc]
  rw [vars_eval stk _ _ h, ← List.drop_drop, List.take_append_drop]

theorem ensure_length (k : Nat) (S : SState) : k ≤ (ensure k S).ts.length := by
  simp [ensure, vars]; omega

theorem exchange_append {α : Type} (l r : List α) (i j : Nat) (hi : i < l.length)
    (hj : j < l.length) : (l ++ r).exchange i j = (l.exchange i j).map (· ++ r) := by
  simp [List.exchange, List.getElem?_append_left hi, List.getElem?_append_left hj,
    List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj, List.set_append_left _ _ hi,
    bind, pure]
  rw [List.set_append_left _ _ (by simpa using hj)]

theorem exchange_map {α β : Type} (g : α → β) (l : List α) (i j : Nat) :
    (l.map g).exchange i j = (l.exchange i j).map (List.map g) := by
  unfold List.exchange
  cases hi : l[i]? <;> cases hj : l[j]? <;> simp_all [bind, pure, List.map_set]

theorem stackOp_none_of_short {i : Instr} {l : List UInt256} (h : l.length < i.need) :
    i.stackOp l = none := by
  cases i with
  | push bs => simp [Instr.need] at h
  | dup n => simp [Instr.stackOp, Instr.need] at h ⊢; omega
  | swap n =>
    simp only [Instr.stackOp, Instr.need] at h ⊢
    unfold List.exchange
    simp [List.getElem?_eq_none (by omega : l.length ≤ n.val + 1), bind]
  | pop => rcases l with _ | ⟨a, l⟩ <;> simp_all [Instr.stackOp, Instr.need]
  | op o => simp [Instr.stackOp, Instr.need] at h ⊢; omega

/-- With at least `i.need` symbolic items on top, `stackOp` acts on the symbolic part. -/
theorem stackOp_conc (stk : List UInt256) (S : SState) (i : Instr)
    (hs : i.need ≤ S.ts.length) (hw : ∀ bs, i = .push bs → bs.length ≤ 32) :
    i.stackOp (conc stk S) = some (conc stk { S with ts := i.sym S.ts }) := by
  simp only [conc]
  cases i with
  | push bs => simp [Instr.stackOp, Instr.sym, hw bs rfl, Term.eval]
  | dup n =>
    simp only [Instr.need] at hs
    have h1 : n.val < (S.ts.map (·.eval stk)).length := by simp; omega
    simp [Instr.stackOp, Instr.sym, List.getElem?_append_left h1,
      List.getElem?_eq_getElem (by omega : n.val < S.ts.length)]
  | swap n =>
    simp only [Instr.need] at hs
    simp only [Instr.stackOp, Instr.sym]
    rw [exchange_append _ _ _ _ (by simp; omega) (by simp; omega), exchange_map]
    cases h : S.ts.exchange 0 (n.val + 1) with
    | none =>
      unfold List.exchange at h
      simp [List.getElem?_eq_getElem (by omega : 0 < S.ts.length),
        List.getElem?_eq_getElem (by omega : n.val + 1 < S.ts.length), bind] at h
    | some l => simp
  | pop =>
    simp only [Instr.need] at hs
    rcases h : S.ts with _ | ⟨t, ts⟩
    · simp [h] at hs
    · simp [Instr.stackOp, Instr.sym]
  | op o =>
    simp only [Instr.need] at hs
    have hl : o.arity ≤ (S.ts.map (·.eval stk) ++ stk.drop S.d).length := by simp; omega
    simp only [Instr.stackOp, Instr.sym, if_pos hl, List.map_cons, Option.some.injEq,
      List.cons_append, List.cons.injEq]
    refine ⟨?_, ?_⟩
    · rw [mkApp_eval _ _ _ hs, ArithOp.eval_take, List.take_append_of_le_length (by simpa using hs),
        ← ArithOp.eval_take]
    · rw [List.drop_append_of_le_length (by simpa using hs), List.map_drop]

theorem srun_mono {f : Fork} : ∀ (b : Block) (S S' : SState), srun f b S = some S' →
    S.d ≤ S'.d ∧ S'.slack + (S'.d - S.d : Int) ≤ S.slack := by
  intro b
  induction b with
  | nil => intro S S' h; simp [srun] at h; subst h; simp
  | cons i b ih =>
    intro S S' h
    simp only [srun] at h
    split at h <;> try contradiction
    obtain ⟨h1, h2⟩ := ih _ _ h
    simp only [sstep, ensure] at h1 h2
    omega

theorem exec_none_of_not_static {f : Fork} {i : Instr} {l : List UInt256}
    (h : i.static f = false) : i.exec f l = none := by
  unfold Instr.exec
  cases ha : i.toOp.availableInFork f
  · simp
  · cases i with
    | push bs =>
      simp_all [Instr.static, Instr.stackOp]
      intro h'; omega
    | _ => simp_all [Instr.static]

/-- **Lift correctness.** Running `b` concretely on `conc stk S` is exactly the symbolic
    result, under exactly the depth/slack conditions computed by `srun`. -/
theorem srun_run (f : Fork) (stk : List UInt256) : ∀ (b : Block) (S : SState),
    S.d ≤ stk.length → (stk.length : Int) - S.d ≤ S.slack →
    run f b (conc stk S) =
      match srun f b S with
      | none => none
      | some S' => if S'.d ≤ stk.length ∧ (stk.length : Int) - S'.d ≤ S'.slack
                   then some (conc stk S') else none := by
  intro b
  induction b with
  | nil => intro S h1 h2; simp [run, srun, h1, h2]
  | cons i b ih =>
    intro S h1 h2
    simp only [run, srun]
    cases hst : i.static f
    · simp [exec_none_of_not_static hst]
    · simp only [if_true]
      have hw : ∀ bs, i = .push bs → bs.length ≤ 32 := by
        rintro bs rfl; simp [Instr.static] at hst; exact hst.2
      have hav : i.toOp.availableInFork f = true := by
        simp only [Instr.static, Bool.and_eq_true] at hst; exact hst.1
      by_cases hd : (ensure i.need S).d ≤ stk.length
      · have hce := conc_ensure stk S i.need (by simpa [ensure] using hd)
        have hso := stackOp_conc stk (ensure i.need S) i (ensure_length _ _) hw
        rw [hce] at hso
        have hconc : conc stk { ensure i.need S with ts := i.sym (ensure i.need S).ts } =
            conc stk (sstep i S) := rfl
        rw [hconc] at hso
        unfold Instr.exec
        simp only [hav, if_true, hso, Option.bind_some]
        by_cases hlen : (conc stk (sstep i S)).length ≤ 1024
        · rw [if_pos hlen, Option.bind_some]
          apply ih
          · simpa [sstep] using hd
          · rw [conc_length] at hlen
            simp only [sstep, ensure] at hlen hd ⊢
            omega
        · rw [if_neg hlen, Option.bind_none]
          cases hs : srun f b (sstep i S) with
          | none => rfl
          | some S' =>
            obtain ⟨m1, m2⟩ := srun_mono b _ _ hs
            rw [conc_length] at hlen
            simp only [sstep, ensure] at hlen hd m1 m2
            dsimp only
            rw [if_neg]
            omega
      · have hshort : (conc stk S).length < i.need := by
          rw [conc_length]; simp [ensure] at hd; omega
        unfold Instr.exec
        simp only [hav, if_true, stackOp_none_of_short hshort, Option.bind_none]
        cases hs : srun f b (sstep i S) with
        | none => rfl
        | some S' =>
          obtain ⟨m1, -⟩ := srun_mono b _ _ hs
          simp only [sstep] at m1
          dsimp only
          rw [if_neg]
          omega

end EvmOpt
