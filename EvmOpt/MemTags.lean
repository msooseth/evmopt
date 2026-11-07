import EvmOpt.MemLift

/-! Assembler constants. An asm block may contain `XInstr.tag k`; the assembler later
    replaces each by `PUSH (ρ k)`. `xcheck` on the asm blocks (tags as opaque atoms) implies
    that the assembled blocks agree, for every assignment `ρ`. -/

namespace EvmOpt
open EvmSemantics EvmSemantics.EVM

def XInstr.assemble (ρ : Nat → List UInt8) : XInstr → XInstr
  | .tag k => .base (.push (ρ k))
  | x => x

def assemble (ρ : Nat → List UInt8) (b : XBlock) : XBlock := b.map (XInstr.assemble ρ)

/-- Tag values: what the assembled PUSH pushes. -/
def tagVal (ρ : Nat → List UInt8) (k : Nat) : UInt256 := pushVal (ρ k)

def Term.subst (v : Nat → UInt256) : Term → Term
  | .app1 o a => .app1 o (a.subst v)
  | .app2 o a b => .app2 o (a.subst v) (b.subst v)
  | .app3 o a b c => .app3 o (a.subst v) (b.subst v) (c.subst v)
  | .env1 e a => .env1 e (a.subst v)
  | .tag k => .const (v k)
  | t => t

theorem Term.eval_subst (v : Nat → UInt256) (ρ : Ctx) :
    ∀ t : Term, (t.subst v).eval ρ = t.eval { ρ with tags := v }
  | .var _ => rfl
  | .const _ => rfl
  | .env0 _ => rfl
  | .eff _ => rfl
  | .tag _ => rfl
  | .app1 o a => by simp only [Term.subst, Term.eval, eval_subst v ρ a]
  | .env1 e a => by simp only [Term.subst, Term.eval, eval_subst v ρ a]
  | .app2 o a b => by simp only [Term.subst, Term.eval, eval_subst v ρ a, eval_subst v ρ b]
  | .app3 o a b c => by
    simp only [Term.subst, Term.eval, eval_subst v ρ a, eval_subst v ρ b, eval_subst v ρ c]

def SState.subst (v : Nat → UInt256) (S : SState) : SState :=
  { S with ts := S.ts.map (Term.subst v) }

def XSState.subst (v : Nat → UInt256) (X : XSState) : XSState :=
  { X with S := X.S.subst v, E := X.E.map fun e => (e.1, e.2.map (Term.subst v)) }

theorem vars_subst (v : Nat → UInt256) (a n : Nat) : (vars a n).map (Term.subst v) = vars a n := by
  simp [vars, Term.subst]

theorem ensure_subst (v : Nat → UInt256) (k : Nat) (S : SState) :
    ensure k (S.subst v) = (ensure k S).subst v := by
  simp [ensure, SState.subst, vars_subst]

theorem mkApp_subst (v : Nat → UInt256) (o : ArithOp) (ts : List Term) :
    mkApp o (ts.map (Term.subst v)) = (mkApp o ts).subst v := by
  unfold mkApp
  rcases ArithOp.arity_cases o with h | h | h <;>
    rcases ts with _ | ⟨a, _ | ⟨b, _ | ⟨c, ts⟩⟩⟩ <;> simp [h, Term.subst]

theorem mkEnv_subst (v : Nat → UInt256) (e : EnvOp) (ts : List Term) :
    mkEnv e (ts.map (Term.subst v)) = (mkEnv e ts).subst v := by
  unfold mkEnv
  have : e.arity = 0 ∨ e.arity = 1 := by cases e <;> simp [EnvOp.arity]
  rcases this with h | h <;> rcases ts with _ | ⟨a, ts⟩ <;> simp [h, Term.subst]

theorem sym_subst (v : Nat → UInt256) (i : Instr) (ts : List Term) :
    i.sym (ts.map (Term.subst v)) = (i.sym ts).map (Term.subst v) := by
  cases i with
  | push bs => simp [Instr.sym, Term.subst]
  | dup n =>
    simp only [Instr.sym, List.map_cons, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases ts[n.val]? <;> simp [Term.subst]
  | swap n =>
    simp only [Instr.sym]
    rw [exchange_map]
    cases ts.exchange 0 (n.val + 1) <;> simp
  | pop => simp [Instr.sym, List.map_tail]
  | op o => simp [Instr.sym, mkApp_subst, List.map_drop]
  | env e => simp [Instr.sym, mkEnv_subst, List.map_drop]

theorem sstep_subst (v : Nat → UInt256) (i : Instr) (S : SState) :
    sstep i (S.subst v) = (sstep i S).subst v := by
  simp only [sstep]
  rw [ensure_subst]
  simp only [SState.subst, sym_subst, List.length_map]

theorem xsstep_assemble (f : Fork) (ρ : Nat → List UInt8)
    (hρ : ∀ k, 1 ≤ (ρ k).length ∧ (ρ k).length ≤ 32) (x : XInstr) (X : XSState) :
    xsstep f (x.assemble ρ) (X.subst (tagVal ρ)) = (xsstep f x X).map (·.subst (tagVal ρ)) := by
  cases x with
  | base i =>
    simp only [XInstr.assemble, xsstep]
    split <;> simp [XSState.subst, sstep_subst]
  | mem m =>
    simp only [XInstr.assemble, xsstep]
    split
    · have he := ensure_subst (tagVal ρ) m.arity X.S
      simp only [Option.map_some, Option.some.injEq]
      show _ = XSState.subst (tagVal ρ) _
      simp only [XSState.subst] at he ⊢
      rw [he]
      cases m.pushes <;> simp [SState.subst, List.map_drop, List.map_take, Term.subst]
    · rfl
  | tag k =>
    obtain ⟨h1, h2⟩ := hρ k
    simp only [XInstr.assemble, xsstep, Option.map_some]
    have hm : min (ρ k).length 32 = (ρ k).length := Nat.min_eq_left h2
    have hne : (ρ k).length ≠ 0 := by omega
    have hst : (Instr.push (ρ k)).static f = true := by
      simp [Instr.static, Instr.toOp, Operation.availableInFork, hm, hne, h2]
    rw [if_pos hst]
    have hc : (Instr.push (ρ k)).cost f = tagCost := by
      simp [Instr.cost, Instr.toOp, Gas.baseCost, tagCost, hm, hne]
    simp only [Option.some.injEq, XSState.subst, SState.subst, SState.push, sstep, ensure,
      Instr.need, Instr.sym, hc, List.map_cons, Term.subst, tagVal]
    simp [vars]

theorem xsrun_assemble (f : Fork) (ρ : Nat → List UInt8)
    (hρ : ∀ k, 1 ≤ (ρ k).length ∧ (ρ k).length ≤ 32) :
    ∀ (b : XBlock) (X : XSState),
    xsrun f (assemble ρ b) (X.subst (tagVal ρ)) = (xsrun f b X).map (·.subst (tagVal ρ)) := by
  intro b
  induction b with
  | nil => intro X; rfl
  | cons x b ih =>
    intro X
    simp only [assemble, List.map_cons, xsrun] at ih ⊢
    rw [xsstep_assemble f ρ hρ]
    cases xsstep f x X with
    | none => rfl
    | some X1 => simp only [Option.map_some, Option.bind_some]; exact ih X1

theorem assemble_noTags (ρ : Nat → List UInt8) (b : XBlock) :
    ∀ x ∈ assemble ρ b, x.isTag = false := by
  intro x hx
  simp only [assemble, List.mem_map] at hx
  obtain ⟨y, -, rfl⟩ := hx
  cases y <;> rfl

/-- `effRun` only sees its arguments' values. -/
theorem effRun_congr (σ0 : State) (stk0 : List UInt256) :
    ∀ (E1 E2 : List (MemOp × List Term)) (t : State) (R : List UInt256) (g : Nat),
    E1.map (·.1) = E2.map (·.1) →
    (∀ (i : Nat) (h1 : i < E1.length) (h2 : i < E2.length) (R' : List UInt256),
      E1[i].2.map (·.eval ⟨σ0, stk0, R', fun _ => 0⟩) =
        E2[i].2.map (·.eval ⟨σ0, stk0, R', fun _ => 0⟩)) →
    effRun σ0 stk0 E1 t R g = effRun σ0 stk0 E2 t R g
  | [], [], _, _, _, _, _ => rfl
  | [], _ :: _, _, _, _, h, _ => by simp at h
  | _ :: _, [], _, _, _, h, _ => by simp at h
  | (m1, a1) :: E1, (m2, a2) :: E2, t, R, g, hm, ha => by
    simp only [List.map_cons, List.cons.injEq] at hm
    obtain ⟨rfl, hm⟩ := hm
    have h0 := ha 0 (by simp) (by simp) R
    simp only [List.getElem_cons_zero] at h0
    simp only [effRun, h0]
    apply effRun_congr σ0 stk0 E1 E2 _ _ _ hm
    intro i h1 h2 R'
    have := ha (i + 1) (by simp; omega) (by simp; omega) R'
    simpa using this

theorem conc_subst (v : Nat → UInt256) (ρ : Ctx) (S : SState) :
    conc ρ (S.subst v) = conc { ρ with tags := v } S := by
  simp [conc, SState.subst, Term.eval_subst]

/-- **Soundness with assembler constants.** If `xcheck` accepts `b'` for `b` (tags as
    atoms), then for every tag assignment, the assembled `b'` reaches the frame the
    assembled `b` reaches, except `pc`, with at least as much gas. -/
theorem xcheck_sound_asm {f : Fork} {b b' : XBlock} {s0 s1 : State} (ρ : Nat → List UInt8)
    (hρ : ∀ k, 1 ≤ (ρ k).length ∧ (ρ k).length ≤ 32) (hc : xcheck f b b' = true)
    (hl : s0.stack.length ≤ 1024) (h : xrun f (assemble ρ b) s0 = some s1) :
    ∃ s2, xrun f (assemble ρ b') s0 = some s2 ∧
      s2 = { s1 with gasAvailable := s2.gasAvailable, pc := s2.pc } ∧
      s1.gasAvailable ≤ s2.gasAvailable := by
  unfold xcheck at hc
  split at hc <;> try contradiction
  next X X' hX hX' =>
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
  obtain ⟨⟨⟨⟨hE, hd⟩, hsl⟩, hsc⟩, hts⟩ := hc
  have hinit : XSState.init.subst (tagVal ρ) = XSState.init := by
    simp [XSState.subst, XSState.init, SState.subst, SState.init]
  have hA := xsrun_assemble f ρ hρ b XSState.init
  have hA' := xsrun_assemble f ρ hρ b' XSState.init
  rw [hinit] at hA hA'
  unfold xlift at hX hX'
  rw [hX] at hA; rw [hX'] at hA'
  simp only [Option.map_some] at hA hA'
  have h1 := xsrun_xrun f s0 _ _ _ s0 (assemble_noTags ρ b) (XInv_init s0 hl) hA
  have h2 := xsrun_xrun f s0 _ _ _ s0 (assemble_noTags ρ b') (XInv_init s0 hl) hA'
  rw [h1] at h
  -- the effect replays agree: same ops, argument values agree under the tag values
  have hr : effRun s0 s0.stack (X'.subst (tagVal ρ)).E s0 [] 0 =
      effRun s0 s0.stack (X.subst (tagVal ρ)).E s0 [] 0 := by
    apply effRun_congr
    · have hops : X.E.map (·.1) = X'.E.map (·.1) := by
        have := congrArg (List.map (·.1)) hE
        simpa [normE, Function.comp_def] using this
      simpa [XSState.subst, Function.comp_def] using hops.symm
    · intro i h1 h2 R'
      have hlen : X.E.length = X'.E.length := by
        have := congrArg List.length hE; simpa [normE] using this
      have hi := congrArg (fun l => l[i]?) hE
      simp only [normE, List.getElem?_map] at hi
      simp only [XSState.subst, List.length_map] at h1 h2
      rw [List.getElem?_eq_getElem h2, List.getElem?_eq_getElem (by omega)] at hi
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hi
      simp only [XSState.subst, List.getElem_map, List.map_map]
      have := map_eval_of_norm (ρ := ⟨s0, s0.stack, R', tagVal ρ⟩) hi.2
      simp only [Function.comp_def, Term.eval_subst]
      exact this.symm
  unfold XFinal at h h2
  rw [hr] at h2
  dsimp only at h h2
  split at h <;> try contradiction
  next hcond =>
  obtain ⟨c1, c2, c3⟩ := hcond
  simp only [Option.some.injEq] at h
  subst h
  simp only [XSState.subst, SState.subst] at c1 c2 c3 h2 ⊢
  have hc' : X'.S.d ≤ s0.stack.length ∧ (s0.stack.length : Int) - X'.S.d ≤ X'.S.slack ∧
      X'.sc + (effRun s0 s0.stack (List.map (fun e => (e.fst, List.map (Term.subst (tagVal ρ)) e.snd))
        X.E) s0 [] 0).2.2 ≤ s0.gasAvailable := ⟨by omega, by omega, by omega⟩
  simp only [hc'.1, hc'.2.1, hc'.2.2, and_self, ↓reduceIte] at h2
  refine ⟨_, h2, ?_, by simp only; omega⟩
  simp only
  have e1 := conc_subst (tagVal ρ) ⟨s0, s0.stack, (effRun s0 s0.stack (X.subst (tagVal ρ)).E s0 [] 0).2.1, fun _ => 0⟩ X'.S
  have e2 := conc_subst (tagVal ρ) ⟨s0, s0.stack, (effRun s0 s0.stack (X.subst (tagVal ρ)).E s0 [] 0).2.1, fun _ => 0⟩ X.S
  simp only [SState.subst, XSState.subst] at e1 e2
  rw [e1, e2, conc_eq_of_norm hd c1 hts]

end EvmOpt
