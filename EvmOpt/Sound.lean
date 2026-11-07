import EvmOpt.Decode

namespace EvmOpt
open EvmSemantics EvmSemantics.EVM

/-- The frame preconditions every instruction step needs besides decoding and gas. -/
structure Ready (s : State) : Prop where
  running : s.halt = .Running
  notPrecompile : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
    s.executionEnv.fork s.executionEnv.codeAddr = false

/-- State after executing `i` with result stack `stk'`. -/
def Instr.post (s : State) (i : Instr) (stk' : List UInt256) : State :=
  { s with stack := stk', pc := s.pc + UInt256.ofNat i.size,
           gasAvailable := s.gasAvailable - i.cost s.fork }

theorem pushVal_nil : pushVal [] = ⟨0⟩ := by rw [pushVal_eq]; rfl

theorem exchange_length {α : Type} {l l' : List α} {i j : Nat}
    (h : l.exchange i j = some l') : l'.length = l.length := by
  unfold List.exchange at h
  cases hi : l[i]? <;> cases hj : l[j]? <;> simp_all [bind, pure] <;> subst h <;> simp

theorem decoded_of_codeAt {s : State} {i : Instr}
    (hc : CodeAt s.executionEnv.code s.pc.toNat i.bytes)
    (hw : ∀ bs, i = .push bs → bs.length ≤ 32)
    (ha : i.toOp.availableInFork s.fork = true) :
    s.decoded = some i.decoded := by
  have hd := decodeAt_of_codeAt hc hw
  have h1 : i.decoded.1 = i.toOp := by cases i <;> rfl
  unfold State.decoded
  rw [hd]
  simp [h1, ha]
  rw [← h1]

set_option hygiene false in
/-- Close one `ArithOp` case: destructure the stack and apply the matching rule. -/
local macro "arith1" r:ident : tactic => `(tactic| (
  obtain ⟨a, rest, hs⟩ : ∃ a rest, s.stack = a :: rest := by
    rcases h : s.stack with _ | ⟨a, rest⟩
    · simp [h, ArithOp.arity] at hle
    · exact ⟨a, rest, rfl⟩
  simp only [hs, ArithOp.arity, ArithOp.eval, List.drop, List.length_cons] at hlen ⊢
  exact Step.running hr.running hr.notPrecompile
    ($r s a rest hop hgas hs (by simp [hs, Operation.pushArity, Operation.popArity]; omega))))

set_option hygiene false in
local macro "arith2" r:ident : tactic => `(tactic| (
  obtain ⟨a, b, rest, hs⟩ : ∃ a b rest, s.stack = a :: b :: rest := by
    rcases h : s.stack with _ | ⟨a, _ | ⟨b, rest⟩⟩
    · simp [h, ArithOp.arity] at hle
    · simp [h, ArithOp.arity] at hle
    · exact ⟨a, b, rest, rfl⟩
  simp only [hs, ArithOp.arity, ArithOp.eval, List.drop, List.length_cons] at hlen ⊢
  exact Step.running hr.running hr.notPrecompile
    ($r s a b rest hop hgas hs (by simp [hs, Operation.pushArity, Operation.popArity]; omega))))

set_option hygiene false in
local macro "arith3" r:ident : tactic => `(tactic| (
  obtain ⟨a, b, c, rest, hs⟩ : ∃ a b c rest, s.stack = a :: b :: c :: rest := by
    rcases h : s.stack with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
    · simp [h, ArithOp.arity] at hle
    · simp [h, ArithOp.arity] at hle
    · simp [h, ArithOp.arity] at hle
    · exact ⟨a, b, c, rest, rfl⟩
  simp only [hs, ArithOp.arity, ArithOp.eval, List.drop, List.length_cons] at hlen ⊢
  exact Step.running hr.running hr.notPrecompile
    ($r s a b c rest hop hgas hs (by simp [hs, Operation.pushArity, Operation.popArity]; omega))))

/-- One instruction is one `Step` of the specification. -/
theorem step_instr {s : State} {i : Instr} {stk' : List UInt256} (hr : Ready s)
    (hc : CodeAt s.executionEnv.code s.pc.toNat i.bytes)
    (hgas : i.cost s.fork ≤ s.gasAvailable)
    (hx : i.exec s.fork s.stack = some stk') :
    Step s (i.post s stk') := by
  obtain ⟨ha, hop', hlen⟩ := Instr.exec_eq_some.1 hx
  have hw : ∀ bs, i = .push bs → bs.length ≤ 32 := by
    rintro bs rfl
    simp only [Instr.stackOp] at hop'
    split at hop' <;> simp_all
  have hdec := decoded_of_codeAt hc hw ha
  unfold Instr.post
  cases i with
  | push bs =>
    have hl := hw bs rfl
    simp only [Instr.stackOp, hl, if_true, Option.some.injEq] at hop'
    subst hop'
    have hto : (Instr.push bs).toOp = .Push ⟨⟨bs.length, by omega⟩⟩ := by
      simp only [Instr.toOp, Operation.Push.injEq, Operation.PushOp.mk.injEq, Fin.mk.injEq]
      omega
    simp only [Instr.decoded, Nat.min_eq_left hl] at hdec
    simp only [Instr.cost, hto] at hgas ⊢
    rcases bs with _ | ⟨b, bs'⟩
    · rw [pushVal_nil]
      exact Step.running hr.running hr.notPrecompile
        (StepRunning.push0 s (by simp [State.decodedOp, hdec]) hgas (by simp at hlen; omega))
    · exact Step.running hr.running hr.notPrecompile
        (StepRunning.pushN s ⟨(b :: bs').length, by omega⟩ _ _ (by simp) hdec hgas
          (by simp at hlen; omega))
  | dup n =>
    simp only [Instr.stackOp, Option.map_eq_some_iff] at hop'
    obtain ⟨v, hv, rfl⟩ := hop'
    exact Step.running hr.running hr.notPrecompile
      (StepRunning.dup s n v (by simp [State.decodedOp, hdec, Instr.decoded, Instr.toOp]) hgas
        hv (by simp at hlen; omega))
  | swap n =>
    simp only [Instr.stackOp] at hop'
    have hl := exchange_length hop'
    exact Step.running hr.running hr.notPrecompile
      (StepRunning.swap s n stk' (by simp [State.decodedOp, hdec, Instr.decoded, Instr.toOp])
        hgas hop' (by simp [Operation.pushArity, Operation.popArity]; omega))
  | pop =>
    simp only [Instr.stackOp] at hop'
    obtain ⟨a, hs⟩ : ∃ a, s.stack = a :: stk' := by
      rcases h : s.stack with _ | ⟨a, rest⟩ <;> simp_all
    exact Step.running hr.running hr.notPrecompile
      (StepRunning.pop s a stk' (by simp [State.decodedOp, hdec, Instr.decoded, Instr.toOp])
        hgas hs (by simp [hs, Operation.pushArity, Operation.popArity]; omega))
  | op o =>
    simp only [Instr.stackOp] at hop'
    split at hop' <;> try contradiction
    rename_i hle
    simp only [Option.some.injEq] at hop'
    subst hop'
    have hop : s.decodedOp = some o.toOp := by
      simp [State.decodedOp, hdec, Instr.decoded, Instr.toOp]
    cases o
    · arith2 StepRunning.add
    · arith2 StepRunning.mul
    · arith2 StepRunning.sub
    · arith2 StepRunning.div
    · arith2 StepRunning.sdiv
    · arith2 StepRunning.mod
    · arith2 StepRunning.smod
    · arith3 StepRunning.addmod
    · arith3 StepRunning.mulmod
    · arith2 StepRunning.signextend
    · arith2 StepRunning.lt
    · arith2 StepRunning.gt
    · arith2 StepRunning.slt
    · arith2 StepRunning.sgt
    · arith2 StepRunning.eq
    · arith1 StepRunning.iszero
    · arith2 StepRunning.and
    · arith2 StepRunning.or
    · arith2 StepRunning.xor_
    · arith1 StepRunning.not
    · arith2 StepRunning.byte_
    · arith2 StepRunning.shl
    · arith2 StepRunning.shr
    · arith2 StepRunning.sar
    · arith1 StepRunning.clz

end EvmOpt

namespace EvmOpt
open EvmSemantics EvmSemantics.EVM

theorem UInt256.ext' {a b : UInt256} (h : a.toNat = b.toNat) : a = b := by
  cases a; cases b; simp only [UInt256.toNat] at h; congr; exact Fin.ext h

theorem UInt256.toNat_add (a b : UInt256) : (a + b).toNat = (a.toNat + b.toNat) % UInt256.size := by
  rfl

theorem UInt256.toNat_ofNat (n : Nat) : (UInt256.ofNat n).toNat = n % UInt256.size := by
  rfl

theorem pc_add_add (p : UInt256) (a b : Nat) :
    p + UInt256.ofNat a + UInt256.ofNat b = p + UInt256.ofNat (a + b) := by
  apply UInt256.ext'
  simp only [UInt256.toNat_add, UInt256.toNat_ofNat, Nat.add_mod_mod, Nat.mod_add_mod,
    Nat.add_assoc]

theorem pc_add_zero (p : UInt256) : p + UInt256.ofNat 0 = p := by
  apply UInt256.ext'
  simp only [UInt256.toNat_add, UInt256.toNat_ofNat, Nat.zero_mod, Nat.add_zero]
  exact Nat.mod_eq_of_lt p.val.isLt

theorem toNat_pc_add {p : UInt256} {k : Nat} (h : p.toNat + k < UInt256.size) :
    (p + UInt256.ofNat k).toNat = p.toNat + k := by
  simp only [UInt256.toNat_add, UInt256.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : k < UInt256.size), Nat.mod_eq_of_lt h]

theorem encode_cons (i : Instr) (b : Block) : encode (i :: b) = i.bytes ++ encode b := by
  simp [encode]

/-- The state after running block `b` to completion with result stack `stk'`. -/
def blockPost (s : State) (b : Block) (stk' : List UInt256) : State :=
  { s with stack := stk', pc := s.pc + UInt256.ofNat (encode b).length,
           gasAvailable := s.gasAvailable - cost s.fork b }

/-- **Stage 1 headline.** If the code at `pc` is block `b`, there is enough gas for all of
    it, and the stack-level `run` succeeds, the specification executes `b` to the matching
    post-state. -/
theorem run_sound (b : Block) : ∀ (s : State) (stk' : List UInt256), Ready s →
    CodeAt s.executionEnv.code s.pc.toNat (encode b) →
    s.pc.toNat + (encode b).length < UInt256.size →
    cost s.fork b ≤ s.gasAvailable →
    run s.fork b s.stack = some stk' →
    Steps s (blockPost s b stk') := by
  induction b with
  | nil =>
    intro s stk' _ _ _ _ hrun
    simp only [run, Option.some.injEq] at hrun
    subst hrun
    unfold blockPost
    simp only [encode, List.flatMap_nil, List.length_nil, pc_add_zero, cost, Nat.sub_zero]
    exact Steps.refl _
  | cons i b ih =>
    intro s stk' hr hc hpc hgas hrun
    simp only [run, Option.bind_eq_some_iff] at hrun
    obtain ⟨stk1, hx, hrest⟩ := hrun
    rw [encode_cons] at hc hpc
    rw [List.length_append] at hpc
    obtain ⟨hci, hcb⟩ := CodeAt.append.1 hc
    simp only [cost] at hgas
    have hstep := step_instr hr hci (by omega) hx
    have hr1 : Ready (i.post s stk1) := ⟨hr.running, hr.notPrecompile⟩
    have hpc1 : (i.post s stk1).pc.toNat = s.pc.toNat + i.size :=
      toNat_pc_add (by unfold Instr.size; omega)
    have hrest' := ih (i.post s stk1) stk' hr1
      (by rw [hpc1]; exact hcb)
      (by rw [hpc1]; unfold Instr.size; omega)
      (by show cost s.fork b ≤ s.gasAvailable - i.cost s.fork; omega)
      hrest
    have e : blockPost s (i :: b) stk' = blockPost (i.post s stk1) b stk' := by
      simp only [blockPost, Instr.post, encode_cons, List.length_append, cost, Instr.size,
        pc_add_add, Nat.sub_sub]
    rw [e]
    exact Steps.trans hstep hrest'

end EvmOpt
