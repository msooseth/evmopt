import EvmOpt.Mem
import EvmOpt.Check

/-! Symbolic execution of blocks with effects. First milestone: effects (memory, storage
    reads, KECCAK) are kept in order with their symbolic arguments; load and KECCAK results
    become `Term.eff i`. TSTORE is not handled symbolically (it changes `accountMap`). -/

namespace EvmOpt
open EvmSemantics EvmSemantics.EVM

namespace MemOp

def arity : MemOp → Nat
  | MLOAD | SLOAD | TLOAD => 1
  | MSTORE | MSTORE8 | TSTORE | KECCAK256 => 2

def pushes : MemOp → Bool
  | MLOAD | SLOAD | TLOAD | KECCAK256 => true
  | _ => false

/-- Gas of the operation on arguments `args` (top first) in state `s`. -/
def costAt (m : MemOp) (args : List UInt256) (s : State) : Nat :=
  match m, args with
  | MLOAD, off :: _ => Gas.mloadTotal s off
  | MSTORE, off :: _ => Gas.mstoreTotal s off
  | MSTORE8, off :: _ => Gas.mstore8Total s off
  | SLOAD, key :: _ => Gas.sloadTotal s key
  | TLOAD, _ => Gas.baseCost s.fork .TLOAD
  | TSTORE, _ => Gas.baseCost s.fork .TSTORE
  | KECCAK256, off :: size :: _ => Gas.keccakTotal s off size
  | _, _ => 0

/-- Result (if any) and the frame after the operation, ignoring stack and gas. -/
def apply (m : MemOp) (args : List UInt256) (s : State) : List UInt256 × State :=
  match m, args with
  | MLOAD, off :: _ =>
    ([MachineState.readWord s.memory off.toNat],
     { s with activeWords := s.activeWordsAfterUInt256 off.toNat 32 })
  | MSTORE, off :: v :: _ =>
    ([], { s with
      memory := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v.toNat 32)
        off.toNat
      activeWords := s.activeWordsAfterUInt256 off.toNat 32 })
  | MSTORE8, off :: v :: _ =>
    ([], { s with
      memory := MachineState.writeBytes s.memory (ByteArray.mk #[UInt8.ofNat (v.toNat % 256)])
        off.toNat
      activeWords := s.activeWordsAfterUInt256 off.toNat 1 })
  | SLOAD, key :: _ =>
    ([(s.accountMap s.executionEnv.address).storage key],
     { s with substate := s.substate.addAccessedStorageKey (s.executionEnv.address, key) })
  | TLOAD, key :: _ => ([(s.accountMap s.executionEnv.address).tstorage key], s)
  | KECCAK256, off :: size :: _ =>
    ([EvmSemantics.keccak256 (MachineState.readPadded s.memory off.toNat size.toNat)],
     { s with activeWords := s.activeWordsAfterUInt256 off.toNat size.toNat })
  | _, _ => ([], s)

end MemOp

/-- `exec` of a non-TSTORE op = shape check, gas check, then `apply`. -/
theorem MemOp.exec_eq (m : MemOp) (hm : m ≠ .TSTORE) (s : State) :
    m.exec s =
      if m.arity ≤ s.stack.length ∧
          (s.stack.drop m.arity).length + (if m.pushes then 1 else 0) ≤ 1024 ∧
          m.costAt (s.stack.take m.arity) s ≤ s.gasAvailable then
        let r := m.apply (s.stack.take m.arity) s
        some { r.2 with stack := r.1 ++ s.stack.drop m.arity,
                        gasAvailable := s.gasAvailable - m.costAt (s.stack.take m.arity) s }
      else none := by
  rcases hs : s.stack with _ | ⟨a, _ | ⟨b, rest⟩⟩ <;> cases m <;>
    simp_all [MemOp.exec, MemOp.arity, MemOp.pushes, MemOp.costAt, MemOp.apply] <;>
    (try split) <;> (try split) <;> simp_all <;> omega

/-- One more than the largest effect index mentioned (0 if none). -/
def Term.effBound : Term → Nat
  | .app1 _ a | .env1 _ a => a.effBound
  | .app2 _ a b => max a.effBound b.effBound
  | .app3 _ a b c => max a.effBound (max b.effBound c.effBound)
  | .eff i => i + 1
  | _ => 0

theorem Term.eval_effs_append (σ : State) (stk R X : List UInt256) :
    ∀ t : Term, t.effBound ≤ R.length → t.eval ⟨σ, stk, R ++ X⟩ = t.eval ⟨σ, stk, R⟩
  | .var _, _ => rfl
  | .const _, _ => rfl
  | .env0 _, _ => rfl
  | .app1 _ a, h => by simp only [Term.eval, Term.effBound] at h ⊢; rw [eval_effs_append σ stk R X a h]
  | .env1 _ a, h => by simp only [Term.eval, Term.effBound] at h ⊢; rw [eval_effs_append σ stk R X a h]
  | .app2 _ a b, h => by
    simp only [Term.eval, Term.effBound] at h ⊢
    rw [eval_effs_append σ stk R X a (by omega), eval_effs_append σ stk R X b (by omega)]
  | .app3 _ a b c, h => by
    simp only [Term.eval, Term.effBound] at h ⊢
    rw [eval_effs_append σ stk R X a (by omega), eval_effs_append σ stk R X b (by omega),
      eval_effs_append σ stk R X c (by omega)]
  | .eff i, h => by
    simp only [Term.eval, Term.effBound] at h ⊢
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : i < R.length)]

def WfTs (n : Nat) (ts : List Term) : Prop := ∀ t ∈ ts, t.effBound ≤ n

theorem exchange_mem {α : Type} {l l' : List α} {i j : Nat} (h : l.exchange i j = some l')
    {x : α} (hx : x ∈ l') : x ∈ l := by
  unfold List.exchange at h
  cases hi : l[i]? <;> cases hj : l[j]? <;> simp_all [bind, pure]
  subst h
  rcases List.mem_or_eq_of_mem_set hx with h1 | h1
  · rcases List.mem_or_eq_of_mem_set h1 with h2 | h2
    · exact h2
    · subst h2; exact List.mem_of_getElem? hj
  · subst h1; exact List.mem_of_getElem? hi

theorem wf_mkApp {n : Nat} {o : ArithOp} {ts : List Term} (h : WfTs n ts) :
    (mkApp o ts).effBound ≤ n := by
  unfold mkApp
  dsimp only
  split <;> simp only [Term.effBound] <;> (try omega)
  all_goals (simp only [WfTs, List.mem_cons, forall_eq_or_imp] at h; omega)

theorem wf_mkEnv {n : Nat} {e : EnvOp} {ts : List Term} (h : WfTs n ts) :
    (mkEnv e ts).effBound ≤ n := by
  unfold mkEnv
  dsimp only
  split <;> simp only [Term.effBound] <;> (try omega)
  simp only [WfTs, List.mem_cons, forall_eq_or_imp] at h; omega

theorem wf_vars (n a k : Nat) : WfTs n (vars a k) := by
  intro t ht; simp [vars] at ht; obtain ⟨_, _, rfl⟩ := ht; simp [Term.effBound]

theorem wf_ensure {n k : Nat} {S : SState} (h : WfTs n S.ts) : WfTs n (ensure k S).ts := by
  intro t ht
  simp only [ensure, List.mem_append] at ht
  rcases ht with ht | ht
  · exact h t ht
  · exact wf_vars n _ _ t ht

theorem wf_sym {n : Nat} {i : Instr} {ts : List Term} (h : WfTs n ts) : WfTs n (i.sym ts) := by
  intro t ht
  cases i with
  | push bs =>
    simp only [Instr.sym, List.mem_cons] at ht
    rcases ht with rfl | ht
    · simp [Term.effBound]
    · exact h t ht
  | dup k =>
    simp only [Instr.sym, List.mem_cons] at ht
    rcases ht with rfl | ht
    · rw [List.getD_eq_getElem?_getD]
      cases hk : ts[k.val]? with
      | none => simp [Term.effBound]
      | some u => simpa using h u (List.mem_of_getElem? hk)
    · exact h t ht
  | swap k =>
    simp only [Instr.sym] at ht
    cases he : ts.exchange 0 (k.val + 1) with
    | none => simp [he] at ht; exact h t ht
    | some l => simp [he] at ht; exact h t (exchange_mem he ht)
  | pop => simp only [Instr.sym] at ht; exact h t (List.mem_of_mem_tail ht)
  | op o =>
    simp only [Instr.sym, List.mem_cons] at ht
    rcases ht with rfl | ht
    · exact wf_mkApp h
    · exact h t (List.mem_of_mem_drop ht)
  | env e =>
    simp only [Instr.sym, List.mem_cons] at ht
    rcases ht with rfl | ht
    · exact wf_mkEnv h
    · exact h t (List.mem_of_mem_drop ht)

theorem conc_effs_append {σ : State} {stk R X : List UInt256} {S : SState}
    (h : WfTs R.length S.ts) : conc ⟨σ, stk, R ++ X⟩ S = conc ⟨σ, stk, R⟩ S := by
  simp only [conc]
  congr 1
  apply List.map_congr_left
  intro t ht
  exact Term.eval_effs_append σ stk R X t (h t ht)


theorem MemOp.costAt_congr (m : MemOp) (vals : List UInt256) (t : State) (stk : List UInt256)
    (g : Nat) (p : UInt256) :
    m.costAt vals { t with stack := stk, gasAvailable := g, pc := p } = m.costAt vals t := by
  cases m <;> rcases vals with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> rfl

theorem MemOp.apply_congr (m : MemOp) (vals : List UInt256) (t : State) (stk : List UInt256)
    (g : Nat) (p : UInt256) :
    m.apply vals { t with stack := stk, gasAvailable := g, pc := p } =
      ((m.apply vals t).1, { (m.apply vals t).2 with stack := stk, gasAvailable := g, pc := p }) := by
  cases m <;> rcases vals with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> rfl

theorem MemOp.apply_env (m : MemOp) (hm : m ≠ .TSTORE) (vals : List UInt256) (t : State) :
    EnvEq (m.apply vals t).2 t := by
  cases m <;> rcases vals with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> simp_all [MemOp.apply, EnvEq]

theorem MemOp.apply_length (m : MemOp) (vals : List UInt256) (t : State) (h : m.arity ≤ vals.length) :
    (m.apply vals t).1.length = if m.pushes then 1 else 0 := by
  cases m <;> rcases vals with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> simp_all [MemOp.apply, MemOp.arity, MemOp.pushes]

/-- Symbolic state of an effect block: stack terms, effects so far (op and argument terms,
    top first) and static gas of the stack instructions. -/
structure XSState where
  S : SState
  E : List (MemOp × List Term)
  sc : Nat

def XSState.init : XSState := ⟨SState.init, [], 0⟩

def memStatic (f : Fork) (m : MemOp) : Bool := m != .TSTORE && m.toOp.availableInFork f

def xsstep (f : Fork) : XInstr → XSState → Option XSState
  | .base i, X => if i.static f then some { X with S := sstep i X.S, sc := X.sc + i.cost f }
                  else none
  | .mem m, X =>
    if memStatic f m then
      let S1 := ensure m.arity X.S
      let ts := (if m.pushes then [Term.eff X.E.length] else []) ++ S1.ts.drop m.arity
      some { S := ⟨ts, S1.d, min S1.slack (1024 - ts.length)⟩
             E := X.E ++ [(m, S1.ts.take m.arity)], sc := X.sc }
    else none

def xsrun (f : Fork) : XBlock → XSState → Option XSState
  | [], X => some X
  | x :: b, X => (xsstep f x X).bind (xsrun f b)

def xlift (f : Fork) (b : XBlock) : Option XSState := xsrun f b XSState.init

/-- Run the effect list on frame `t`: results (one per effect, 0 for stores) and gas. -/
def effRun (σ0 : State) (stk0 : List UInt256) :
    List (MemOp × List Term) → State → List UInt256 → Nat → State × List UInt256 × Nat
  | [], t, R, g => (t, R, g)
  | (m, args) :: E, t, R, g =>
    let vals := args.map (·.eval ⟨σ0, stk0, R⟩)
    effRun σ0 stk0 E (m.apply vals t).2 (R ++ [(m.apply vals t).1.headD 0])
      (g + m.costAt vals t)

theorem effRun_append (σ0 : State) (stk0 : List UInt256) (m : MemOp) (args : List Term) :
    ∀ (E : List (MemOp × List Term)) (t : State) (R : List UInt256) (g : Nat),
    effRun σ0 stk0 (E ++ [(m, args)]) t R g =
      let r := effRun σ0 stk0 E t R g
      let vals := args.map (·.eval ⟨σ0, stk0, r.2.1⟩)
      ((m.apply vals r.1).2, r.2.1 ++ [(m.apply vals r.1).1.headD 0], r.2.2 + m.costAt vals r.1)
  | [], t, R, g => rfl
  | (m', a') :: E, t, R, g => by simp only [List.cons_append, effRun]; rw [effRun_append σ0 stk0 m args E]

theorem effRun_length (σ0 : State) (stk0 : List UInt256) :
    ∀ (E : List (MemOp × List Term)) (t : State) (R : List UInt256) (g : Nat),
    (effRun σ0 stk0 E t R g).2.1.length = R.length + E.length
  | [], t, R, g => by simp [effRun]
  | (m, a) :: E, t, R, g => by
    simp only [effRun]; rw [effRun_length σ0 stk0 E]; simp; omega

theorem effRun_gas_mono (σ0 : State) (stk0 : List UInt256) :
    ∀ (E : List (MemOp × List Term)) (t : State) (R : List UInt256) (g : Nat),
    g ≤ (effRun σ0 stk0 E t R g).2.2
  | [], t, R, g => by simp [effRun]
  | (m, a) :: E, t, R, g => by
    simp only [effRun]
    exact Nat.le_trans (Nat.le_add_right g _) (effRun_gas_mono σ0 stk0 E _ _ _)


theorem effRun_append_gen (σ0 : State) (stk0 : List UInt256) :
    ∀ (E E2 : List (MemOp × List Term)) (t : State) (R : List UInt256) (g : Nat),
    effRun σ0 stk0 (E ++ E2) t R g =
      effRun σ0 stk0 E2 (effRun σ0 stk0 E t R g).1 (effRun σ0 stk0 E t R g).2.1
        (effRun σ0 stk0 E t R g).2.2
  | [], E2, t, R, g => rfl
  | (m, a) :: E, E2, t, R, g => by simp only [List.cons_append, effRun]; exact effRun_append_gen σ0 stk0 E E2 _ _ _

theorem effRun_gas_prefix (σ0 : State) (stk0 : List UInt256) (E E2 : List (MemOp × List Term))
    (t : State) (R : List UInt256) (g : Nat) :
    (effRun σ0 stk0 E t R g).2.2 ≤ (effRun σ0 stk0 (E ++ E2) t R g).2.2 := by
  rw [effRun_append_gen]; exact effRun_gas_mono _ _ _ _ _ _

theorem xsrun_mono {f : Fork} : ∀ (b : XBlock) (X X' : XSState), xsrun f b X = some X' →
    X.S.d ≤ X'.S.d ∧ X'.S.slack + ((X'.S.d : Int) - X.S.d) ≤ X.S.slack ∧ X.sc ≤ X'.sc ∧
    ∃ E2, X'.E = X.E ++ E2 := by
  intro b
  induction b with
  | nil => intro X X' h; simp [xsrun] at h; subst h; exact ⟨Nat.le_refl _, by omega, Nat.le_refl _, [], by simp⟩
  | cons x b ih =>
    intro X X' h
    simp only [xsrun, Option.bind_eq_some_iff] at h
    obtain ⟨X1, h1, h2⟩ := h
    obtain ⟨m1, m2, m3, E2, hE⟩ := ih X1 X' h2
    cases x with
    | base i =>
      simp only [xsstep] at h1
      split at h1 <;> try contradiction
      simp only [Option.some.injEq] at h1; subst h1
      simp only [sstep, ensure] at m1 m2 m3 hE
      exact ⟨by omega, by omega, by omega, E2, hE⟩
    | mem m =>
      simp only [xsstep] at h1
      split at h1 <;> try contradiction
      simp only [Option.some.injEq] at h1; subst h1
      simp only [ensure] at m1 m2 m3 hE
      exact ⟨by omega, by omega, by omega, (m, (ensure m.arity X.S).ts.take m.arity) :: E2,
        by simp [hE, ensure]⟩

/-- The frame the effect block ends in, if the stack fits and the gas suffices. -/
def XFinal (s0 : State) (X : XSState) (pc : UInt256) : Option State :=
  let r := effRun s0 s0.stack X.E s0 [] 0
  if X.S.d ≤ s0.stack.length ∧ (s0.stack.length : Int) - X.S.d ≤ X.S.slack ∧
      X.sc + r.2.2 ≤ s0.gasAvailable then
    some { r.1 with stack := conc ⟨s0, s0.stack, r.2.1⟩ X.S,
                    gasAvailable := s0.gasAvailable - X.sc - r.2.2, pc := pc }
  else none

/-- Concrete frame `s` corresponds to symbolic state `X` (relative to the block start `s0`). -/
def XInv (s0 : State) (X : XSState) (s : State) : Prop :=
  let r := effRun s0 s0.stack X.E s0 [] 0
  EnvEq r.1 s0 ∧ r.2.1.length = X.E.length ∧ WfTs r.2.1.length X.S.ts ∧
  X.S.d ≤ s0.stack.length ∧ (s0.stack.length : Int) - X.S.d ≤ X.S.slack ∧
  X.sc + r.2.2 ≤ s0.gasAvailable ∧
  ∃ p, s = { r.1 with stack := conc ⟨s0, s0.stack, r.2.1⟩ X.S,
                      gasAvailable := s0.gasAvailable - X.sc - r.2.2, pc := p }

/-- If the block's symbolic run reaches `X'` from an intermediate `X1` whose conditions
    already fail, the final conditions fail too. -/
theorem XFinal_none_of_fail {f : Fork} {s0 : State} {b : XBlock} {X1 X' : XSState} {pc : UInt256}
    (h : xsrun f b X1 = some X')
    (hfail : ¬ (X1.S.d ≤ s0.stack.length ∧ (s0.stack.length : Int) - X1.S.d ≤ X1.S.slack ∧
      X1.sc + (effRun s0 s0.stack X1.E s0 [] 0).2.2 ≤ s0.gasAvailable)) :
    XFinal s0 X' pc = none := by
  obtain ⟨m1, m2, m3, E2, hE⟩ := xsrun_mono b X1 X' h
  have hg := effRun_gas_prefix s0 s0.stack X1.E E2 s0 [] 0
  rw [← hE] at hg
  unfold XFinal
  rw [if_neg]
  intro ⟨c1, c2, c3⟩
  apply hfail
  exact ⟨by omega, by omega, by omega⟩


theorem MemOp.apply_res (m : MemOp) (vals : List UInt256) (t : State)
    (h : m.arity ≤ vals.length) :
    (m.apply vals t).1 = if m.pushes then [(m.apply vals t).1.headD 0] else [] := by
  cases m <;> rcases vals with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> simp_all [MemOp.apply, MemOp.arity, MemOp.pushes]

theorem conc_push {σ : State} {stk R : List UInt256} {v : UInt256} {ts : List Term} {d : Nat}
    {sl : Int} (hw : WfTs R.length ts) :
    conc ⟨σ, stk, R ++ [v]⟩ ⟨Term.eff R.length :: ts, d, sl⟩ = v :: conc ⟨σ, stk, R⟩ ⟨ts, d, sl⟩ := by
  have := conc_effs_append (σ := σ) (stk := stk) (X := [v]) (S := ⟨ts, d, sl⟩) hw
  simp only [conc, List.map_cons, List.cons_append] at this ⊢
  rw [this]
  simp [Term.eval]

theorem Instr.exec_congr {f : Fork} {σ σ' : State} (h : EnvEq σ σ') (i : Instr)
    (stk : List UInt256) : i.exec f σ stk = i.exec f σ' stk := by
  unfold Instr.exec; rw [Instr.stackOp_congr h]

theorem EnvEq.trans {a b c : State} (h1 : EnvEq a b) (h2 : EnvEq b c) : EnvEq a c :=
  ⟨h1.1.trans h2.1, h1.2.1.trans h2.2.1, h1.2.2.trans h2.2.2⟩

theorem WfTs.mono {n m : Nat} {ts : List Term} (h : WfTs n ts) (hnm : n ≤ m) : WfTs m ts :=
  fun t ht => Nat.le_trans (h t ht) hnm

theorem xencode_length_cons (x : XInstr) (b : XBlock) :
    (xencode (x :: b)).length = x.size + (xencode b).length := by
  simp [xencode, XInstr.size]

theorem xsrun_xrun (f : Fork) (s0 : State) : ∀ (b : XBlock) (X X' : XSState) (s : State),
    XInv s0 X s → xsrun f b X = some X' →
    xrun f b s = XFinal s0 X' (s.pc + UInt256.ofNat (xencode b).length) := by
  intro b
  induction b with
  | nil =>
    intro X X' s hinv h
    simp only [xsrun, Option.some.injEq] at h; subst h
    obtain ⟨-, -, -, h4, h5, h6, p, rfl⟩ := hinv
    unfold XFinal
    rw [if_pos ⟨h4, h5, h6⟩]
    simp [xrun, xencode, pc_add_zero]
  | cons x b ih =>
    intro X X' s hinv h
    simp only [xsrun, Option.bind_eq_some_iff] at h
    obtain ⟨X1, h1, h2⟩ := h
    obtain ⟨hE, hR, hW, hd0, hsl0, hg0, p, hs⟩ := hinv
    have hEs : EnvEq s s0 := by rw [hs]; exact hE
    have hss : s.stack = conc ⟨s0, s0.stack, (effRun s0 s0.stack X.E s0 [] 0).2.1⟩ X.S := by
      rw [hs]
    have hsg : s.gasAvailable = s0.gasAvailable - X.sc - (effRun s0 s0.stack X.E s0 [] 0).2.2 := by
      rw [hs]
    have hpc : ∀ q, q + UInt256.ofNat x.size + UInt256.ofNat (xencode b).length =
        q + UInt256.ofNat (xencode (x :: b)).length := by
      intro q; rw [pc_add_add, xencode_length_cons]
    simp only [xrun]
    cases x with
    | base i =>
      simp only [xsstep] at h1
      split at h1 <;> try contradiction
      next hst =>
      simp only [Option.some.injEq] at h1; subst h1
      have hav : i.toOp.availableInFork f = true := by
        simp only [Instr.static, Bool.and_eq_true] at hst; exact hst.1
      have hex := exec_conc f ⟨s0, s0.stack, (effRun s0 s0.stack X.E s0 [] 0).2.1⟩ i X.S hst hd0
      simp only [XInstr.exec, XInstr.toOp, hav, if_true, XInstr.effect]
      rw [Instr.exec_congr hEs, hss, hex]
      by_cases hA : (sstep i X.S).d ≤ s0.stack.length ∧
          (conc ⟨s0, s0.stack, (effRun s0 s0.stack X.E s0 [] 0).2.1⟩ (sstep i X.S)).length ≤ 1024
      · rw [if_pos hA]
        simp only
        by_cases hG : i.cost f ≤ s.gasAvailable
        · rw [if_pos hG]
          simp only [Option.map_some, Option.bind_some]
          rw [ih _ X' _ ?_ h2, hpc]
          refine ⟨hE, hR, wf_sym (wf_ensure hW), hA.1, ?_, ?_, ?_⟩
          · have hl := hA.2
            rw [conc_length] at hl
            simp only [sstep, ensure] at hl hA ⊢
            omega
          · simp only; omega
          · exact ⟨_, by rw [hs]; simp only [Nat.sub_sub]; rw [Nat.add_right_comm]⟩
        · rw [if_neg hG]
          simp only [Option.map_none, Option.bind_none]
          exact (XFinal_none_of_fail h2 (by simp only; omega)).symm
      · rw [if_neg hA]
        simp only [Option.map_none, Option.bind_none]
        refine (XFinal_none_of_fail h2 ?_).symm
        intro ⟨c1, c2, _⟩
        apply hA
        refine ⟨c1, ?_⟩
        rw [conc_length]
        simp only [sstep, ensure] at c1 c2 ⊢
        omega
    | mem m =>
      simp only [xsstep] at h1
      split at h1 <;> try contradiction
      next hms =>
      simp only [Option.some.injEq] at h1; subst h1
      have hmT : m ≠ .TSTORE := by intro h; subst h; simp [memStatic] at hms
      have hav : m.toOp.availableInFork f = true := by
        simp only [memStatic, Bool.and_eq_true] at hms; exact hms.2
      simp only [XInstr.exec, XInstr.toOp, hav, if_true, XInstr.effect]
      rw [MemOp.exec_eq m hmT s]
      have hRl := hR
      generalize hRd : (effRun s0 s0.stack X.E s0 [] 0).2.1 = R at hss hW hRl
      have hS1d : (ensure m.arity X.S).d = X.S.d + (m.arity - X.S.ts.length) := rfl
      have hS1s : (ensure m.arity X.S).slack = X.S.slack - (m.arity - X.S.ts.length : Nat) := rfl
      generalize hS1 : ensure m.arity X.S = S1 at h2 hS1d hS1s ⊢
      have hlen1 : m.arity ≤ S1.ts.length := by rw [← hS1]; exact ensure_length _ _
      have hW1 : WfTs R.length S1.ts := by rw [← hS1]; exact wf_ensure hW
      by_cases hd : S1.d ≤ s0.stack.length
      · have hce := conc_ensure ⟨s0, s0.stack, R⟩ X.S m.arity
          (by have h' := hd; rw [← hS1] at h'; simpa [ensure] using h')
        rw [hS1] at hce
        have hstk : s.stack = S1.ts.map (·.eval ⟨s0, s0.stack, R⟩) ++ s0.stack.drop S1.d := by
          rw [hss, ← hce]; rfl
        have hlm : m.arity ≤ (S1.ts.map (·.eval ⟨s0, s0.stack, R⟩)).length := by simpa using hlen1
        have htake : s.stack.take m.arity = (S1.ts.take m.arity).map (·.eval ⟨s0, s0.stack, R⟩) := by
          rw [hstk, List.take_append_of_le_length hlm, List.map_take]
        have hdrop : s.stack.drop m.arity =
            (S1.ts.drop m.arity).map (·.eval ⟨s0, s0.stack, R⟩) ++ s0.stack.drop S1.d := by
          rw [hstk, List.drop_append_of_le_length hlm, List.map_drop]
        have harity : m.arity ≤ s.stack.length := by rw [hstk]; simp; omega
        rw [htake, hdrop]
        generalize hvals : (S1.ts.take m.arity).map (·.eval ⟨s0, s0.stack, R⟩) = vals
        have hcost : m.costAt vals s = m.costAt vals (effRun s0 s0.stack X.E s0 [] 0).1 := by
          rw [hs]; exact MemOp.costAt_congr _ _ _ _ _ _
        have happ : m.apply vals s = ((m.apply vals (effRun s0 s0.stack X.E s0 [] 0).1).1,
            { Prod.snd (m.apply vals (effRun s0 s0.stack X.E s0 [] 0).1) with
              stack := s.stack, gasAvailable := s.gasAvailable, pc := s.pc }) := by
          rw [hs]; exact MemOp.apply_congr _ _ _ _ _ _
        have hvlen : m.arity ≤ vals.length := by rw [← hvals]; simp; omega
        have hres := MemOp.apply_res m vals (effRun s0 s0.stack X.E s0 [] 0).1 hvlen
        have hg1 := effRun_append s0 s0.stack m (S1.ts.take m.arity) X.E s0 [] 0
        simp only [hRd, hvals] at hg1
        by_cases hB : ((S1.ts.drop m.arity).map (·.eval ⟨s0, s0.stack, R⟩) ++
              s0.stack.drop S1.d).length + (if m.pushes then 1 else 0) ≤ 1024 ∧
            m.costAt vals s ≤ s.gasAvailable
        · rw [if_pos ⟨harity, hB⟩]
          simp only [Option.map_some, Option.bind_some]
          rw [ih _ X' _ ?_ h2, hpc]
          have hWd : WfTs R.length (S1.ts.drop m.arity) := fun t ht => hW1 t (List.mem_of_mem_drop ht)
          have hstack : (m.apply vals (effRun s0 s0.stack X.E s0 [] 0).1).1 ++
              ((S1.ts.drop m.arity).map (·.eval ⟨s0, s0.stack, R⟩) ++ s0.stack.drop S1.d) =
              conc ⟨s0, s0.stack, R ++ [(m.apply vals (effRun s0 s0.stack X.E s0 [] 0).1).1.headD 0]⟩
                ⟨(if m.pushes then [Term.eff X.E.length] else []) ++ S1.ts.drop m.arity, S1.d,
                 min S1.slack (1024 - ((if m.pushes then [Term.eff X.E.length] else []) ++
                   S1.ts.drop m.arity).length)⟩ := by
            rw [← hRl]
            cases hp : m.pushes
            · rw [hres]; simp only [hp, Bool.false_eq_true, ↓reduceIte, List.nil_append]
              rw [conc_effs_append hWd]; rfl
            · rw [hres]
              simp only [hp, ↓reduceIte, List.cons_append, List.nil_append,
                List.headD_cons]
              rw [conc_push hWd]; rfl
          refine ⟨?_, ?_, ?_, hd, ?_, ?_, ?_⟩
          · rw [hg1]; exact (MemOp.apply_env m hmT vals _).trans hE
          · rw [hg1]; simp [hRl]
          · rw [hg1]
            intro t ht
            simp only [List.mem_append] at ht
            simp only [List.length_append, List.length_singleton]
            rcases ht with ht | ht
            · cases hp : m.pushes <;> simp [hp] at ht; subst ht; simp [Term.effBound, hRl]
            · exact Nat.le_succ_of_le (hWd t ht)
          · have hl := hB.1
            simp only [List.length_append, List.length_map, List.length_drop] at hl
            simp only
            cases hp : m.pushes <;> simp only [hp, Bool.false_eq_true, ↓reduceIte, List.length_cons,
              List.cons_append, List.nil_append, List.length_drop] at hl ⊢ <;> omega
          · rw [hg1]; have := hB.2; rw [hcost, hsg] at this; simp only; omega
          · exact ⟨_, by
              rw [hg1, happ]
              simp only
              rw [hstack, hsg, hcost, Nat.sub_sub, Nat.sub_sub]⟩
        · rw [if_neg (fun h => hB h.2)]
          simp only [Option.map_none, Option.bind_none]
          refine (XFinal_none_of_fail h2 ?_).symm
          intro ⟨_, c2, c3⟩
          apply hB
          simp only [hg1] at c3
          refine ⟨?_, by rw [hcost, hsg]; omega⟩
          simp only [List.length_append, List.length_map, List.length_drop] at c2 ⊢
          cases hp : m.pushes <;> simp only [hp, Bool.false_eq_true, ↓reduceIte, List.length_cons,
            List.length_nil] at c2 ⊢ <;> omega
      · have hshort : ¬ m.arity ≤ s.stack.length := by
          rw [hss, conc_length]; dsimp only; omega
        rw [if_neg (fun h => hshort h.1)]
        simp only [Option.map_none, Option.bind_none]
        refine (XFinal_none_of_fail h2 ?_).symm
        intro ⟨c1, _, _⟩
        exact hd c1


def normE (E : List (MemOp × List Term)) : List (MemOp × List Term) :=
  E.map fun e => (e.1, e.2.map norm)

/-- Translation validation for effect blocks: same effects (normalised arguments) in the
    same order, same normalised stack result, no deeper reads, no less stack room, no more
    stack-instruction gas. -/
def xcheck (f : Fork) (b b' : XBlock) : Bool :=
  match xlift f b, xlift f b' with
  | some X, some X' =>
    normE X.E == normE X'.E && decide (X'.S.d ≤ X.S.d) &&
    decide (X.S.slack + ((X.S.d : Int) - X'.S.d) ≤ X'.S.slack) && decide (X'.sc ≤ X.sc) &&
    (X.S.ts.map norm == (X'.S.ts ++ vars X'.S.d (X.S.d - X'.S.d)).map norm)
  | _, _ => false

theorem effRun_normE (σ0 : State) (stk0 : List UInt256) :
    ∀ (E1 E2 : List (MemOp × List Term)) (t : State) (R : List UInt256) (g : Nat),
    normE E1 = normE E2 → effRun σ0 stk0 E1 t R g = effRun σ0 stk0 E2 t R g
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, _, _, _, h => by simp [normE] at h
  | _ :: _, [], _, _, _, h => by simp [normE] at h
  | (m1, a1) :: E1, (m2, a2) :: E2, t, R, g, h => by
    simp only [normE, List.map_cons, List.cons.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, ha⟩, hE⟩ := h
    have hv : a1.map (·.eval ⟨σ0, stk0, R⟩) = a2.map (·.eval ⟨σ0, stk0, R⟩) := map_eval_of_norm ha
    simp only [effRun, hv]
    exact effRun_normE σ0 stk0 E1 E2 _ _ _ hE

theorem conc_eq_of_norm {ρ : Ctx} {S S' : SState} (hd : S'.d ≤ S.d) (hl : S.d ≤ ρ.stk.length)
    (hts : S.ts.map norm = (S'.ts ++ vars S'.d (S.d - S'.d)).map norm) :
    conc ρ S' = conc ρ S := by
  have hv := vars_eval ρ S'.d (S.d - S'.d) (by omega)
  simp only [conc]
  have hdrop : ρ.stk.drop S'.d = (ρ.stk.drop S'.d).take (S.d - S'.d) ++ ρ.stk.drop S.d := by
    conv => lhs; rw [← List.take_append_drop (S.d - S'.d) (ρ.stk.drop S'.d)]
    rw [List.drop_drop]; congr 2; omega
  rw [hdrop, ← hv, ← List.append_assoc, ← List.map_append, map_eval_of_norm hts]

theorem XInv_init (s0 : State) (hl : s0.stack.length ≤ 1024) : XInv s0 XSState.init s0 := by
  refine ⟨⟨rfl, rfl, rfl⟩, rfl, fun t ht => by simp [XSState.init, SState.init] at ht,
    by simp [XSState.init, SState.init], by simp [XSState.init, SState.init]; omega,
    by simp [XSState.init, effRun], s0.pc, ?_⟩
  simp [XSState.init, effRun, conc, SState.init]

/-- **Stage 8 checker soundness.** If `xcheck` accepts `b'` for `b`, then from any frame on
    which `b` runs, `b'` runs to the same frame except `pc` and with at least as much gas. -/
theorem xcheck_sound {f : Fork} {b b' : XBlock} {s0 s1 : State} (hc : xcheck f b b' = true)
    (hl : s0.stack.length ≤ 1024) (h : xrun f b s0 = some s1) :
    ∃ s2, xrun f b' s0 = some s2 ∧
      s2 = { s1 with gasAvailable := s2.gasAvailable, pc := s2.pc } ∧
      s1.gasAvailable ≤ s2.gasAvailable := by
  unfold xcheck at hc
  split at hc <;> try contradiction
  next X X' hX hX' =>
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
  obtain ⟨⟨⟨⟨hE, hd⟩, hsl⟩, hsc⟩, hts⟩ := hc
  have h1 := xsrun_xrun f s0 b XSState.init X s0 (XInv_init s0 hl) hX
  have h2 := xsrun_xrun f s0 b' XSState.init X' s0 (XInv_init s0 hl) hX'
  rw [h1] at h
  have hr : effRun s0 s0.stack X'.E s0 [] 0 = effRun s0 s0.stack X.E s0 [] 0 :=
    effRun_normE _ _ _ _ _ _ _ hE.symm
  unfold XFinal at h h2
  rw [hr] at h2
  dsimp only at h h2
  split at h <;> try contradiction
  next hcond =>
  obtain ⟨c1, c2, c3⟩ := hcond
  simp only [Option.some.injEq] at h
  subst h
  rw [if_pos ⟨by omega, by omega, by omega⟩] at h2
  refine ⟨_, h2, ?_, by simp only; omega⟩
  simp only
  rw [conc_eq_of_norm hd c1 hts]


/-- **End-to-end guarantee for effect blocks.** With the accepted candidate `b'` in the
    code, the specification steps to the frame the original `b` would reach, except `pc`,
    with at least as much gas left. -/
theorem xcheck_steps {b b' : XBlock} {s s1 : State} (hc : xcheck s.fork b b' = true)
    (hready : Ready s) (hcode : CodeAt s.executionEnv.code s.pc.toNat (xencode b'))
    (hpc : s.pc.toNat + (xencode b').length < UInt256.size) (hl : s.stack.length ≤ 1024)
    (h : xrun s.fork b s = some s1) :
    ∃ s2, Steps s s2 ∧ s2 = { s1 with gasAvailable := s2.gasAvailable, pc := s2.pc } ∧
      s1.gasAvailable ≤ s2.gasAvailable := by
  obtain ⟨s2, h2, heq, hg⟩ := xcheck_sound hc hl h
  exact ⟨s2, xrun_sound b' s s2 hready hcode hpc h2, heq, hg⟩

end EvmOpt
