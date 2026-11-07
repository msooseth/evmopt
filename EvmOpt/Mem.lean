import EvmOpt.Sound
import EvmOpt.Decode

/-! Blocks with memory, storage and KECCAK256 (stage 8). The block state is the full frame
    `State`; each operation updates exactly the fields its `StepRunning` rule updates,
    including the dynamic gas, while `pc` is advanced separately. -/

namespace EvmOpt
open EvmSemantics EvmSemantics.EVM

inductive MemOp
  | MLOAD | MSTORE | MSTORE8 | SLOAD | TLOAD | TSTORE | KECCAK256
  deriving DecidableEq, Repr, Inhabited, Ord, Hashable

namespace MemOp

def toOp : MemOp → Operation
  | MLOAD => .MLOAD | MSTORE => .MSTORE | MSTORE8 => .MSTORE8 | SLOAD => .SLOAD
  | TLOAD => .TLOAD | TSTORE => .TSTORE | KECCAK256 => .KECCAK256

def byte : MemOp → UInt8
  | MLOAD => 0x51 | MSTORE => 0x52 | MSTORE8 => 0x53 | SLOAD => 0x54
  | TLOAD => 0x5c | TSTORE => 0x5d | KECCAK256 => 0x20

/-- Effect on the frame, minus `pc`; `none` on underflow, overflow, out of gas or a
    static-context violation. -/
def exec (m : MemOp) (s : State) : Option State :=
  match m, s.stack with
  | MLOAD, off :: rest =>
    if Gas.mloadTotal s off ≤ s.gasAvailable ∧ rest.length + 1 ≤ 1024 then
      some { s with
        stack := MachineState.readWord s.memory off.toNat :: rest
        gasAvailable := s.gasAvailable - Gas.mloadTotal s off
        activeWords := s.activeWordsAfterUInt256 off.toNat 32 }
    else none
  | MSTORE, off :: v :: rest =>
    if Gas.mstoreTotal s off ≤ s.gasAvailable ∧ rest.length ≤ 1024 then
      some { s with
        stack := rest
        gasAvailable := s.gasAvailable - Gas.mstoreTotal s off
        memory := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v.toNat 32)
          off.toNat
        activeWords := s.activeWordsAfterUInt256 off.toNat 32 }
    else none
  | MSTORE8, off :: v :: rest =>
    if Gas.mstore8Total s off ≤ s.gasAvailable ∧ rest.length ≤ 1024 then
      some { s with
        stack := rest
        gasAvailable := s.gasAvailable - Gas.mstore8Total s off
        memory := MachineState.writeBytes s.memory (ByteArray.mk #[UInt8.ofNat (v.toNat % 256)])
          off.toNat
        activeWords := s.activeWordsAfterUInt256 off.toNat 1 }
    else none
  | SLOAD, key :: rest =>
    if Gas.sloadTotal s key ≤ s.gasAvailable ∧ rest.length + 1 ≤ 1024 then
      some { s with
        stack := ((s.accountMap s.executionEnv.address).storage key) :: rest
        gasAvailable := s.gasAvailable - Gas.sloadTotal s key
        substate := s.substate.addAccessedStorageKey (s.executionEnv.address, key) }
    else none
  | TLOAD, key :: rest =>
    if Gas.baseCost s.fork .TLOAD ≤ s.gasAvailable ∧ rest.length + 1 ≤ 1024 then
      some { s with
        stack := ((s.accountMap s.executionEnv.address).tstorage key) :: rest
        gasAvailable := s.gasAvailable - Gas.baseCost s.fork .TLOAD }
    else none
  | TSTORE, key :: v :: rest =>
    if s.executionEnv.permitStateMutation = true ∧ Gas.baseCost s.fork .TSTORE ≤ s.gasAvailable
      ∧ rest.length ≤ 1024 then
      some { s with
        stack := rest
        gasAvailable := s.gasAvailable - Gas.baseCost s.fork .TSTORE
        accountMap := s.accountMap.set s.executionEnv.address
          { s.accountMap s.executionEnv.address with
              tstorage := (s.accountMap s.executionEnv.address).tstorage.set key v } }
    else none
  | KECCAK256, off :: size :: rest =>
    if Gas.keccakTotal s off size ≤ s.gasAvailable ∧ rest.length + 1 ≤ 1024 then
      some { s with
        stack := EvmSemantics.keccak256 (MachineState.readPadded s.memory off.toNat size.toNat)
          :: rest
        gasAvailable := s.gasAvailable - Gas.keccakTotal s off size
        activeWords := s.activeWordsAfterUInt256 off.toNat size.toNat }
    else none
  | _, _ => none

end MemOp

/-- `tag k` is an assembler-provided constant (`PUSH [tag] k` and friends): symbolic only;
    it must be assembled into a real PUSH before it can run. -/
inductive XInstr
  | base (i : Instr)
  | mem (m : MemOp)
  | tag (k : Nat)
  deriving DecidableEq, Repr, Inhabited

abbrev XBlock := List XInstr

namespace XInstr

def toOp : XInstr → Operation
  | base i => i.toOp
  | mem m => m.toOp
  | tag _ => .Push ⟨2⟩

/-- For `tag`, a size estimate (the assembler typically emits PUSH2). -/
def bytes : XInstr → List UInt8
  | base i => i.bytes
  | mem m => [m.byte]
  | tag _ => [0x61, 0, 0]

def size (x : XInstr) : Nat := x.bytes.length

/-- Effect on the frame without the pc advance. -/
def effect (f : Fork) (x : XInstr) (s : State) : Option State :=
  match x with
  | base i =>
    match i.exec f s s.stack with
    | some stk =>
      if i.cost f ≤ s.gasAvailable then
        some { s with stack := stk, gasAvailable := s.gasAvailable - i.cost f }
      else none
    | none => none
  | mem m => m.exec s
  | tag _ => none

/-- One instruction: its effect, then `pc` past it. -/
def exec (f : Fork) (x : XInstr) (s : State) : Option State :=
  if x.toOp.availableInFork f then
    (x.effect f s).map fun s' => { s' with pc := s.pc + UInt256.ofNat x.size }
  else none

end XInstr

def xrun (f : Fork) : XBlock → State → Option State
  | [], s => some s
  | x :: b, s => (x.exec f s).bind (xrun f b)

def xencode (b : XBlock) : List UInt8 := b.flatMap XInstr.bytes

theorem opcodeOf_mem (m : MemOp) : Decode.opcodeOf m.byte = some m.toOp := by
  cases m <;> rfl

theorem decodedOp_mem {s : State} {m : MemOp}
    (hc : CodeAt s.executionEnv.code s.pc.toNat [m.byte])
    (ha : m.toOp.availableInFork s.fork = true) : s.decodedOp = some m.toOp := by
  obtain ⟨hpc, h0⟩ := hc 0 (by simp)
  simp only [Nat.add_zero, List.getElem_cons_zero] at hpc h0
  have hd : Decode.decodeAt s.executionEnv.code s.pc.toNat = some (m.toOp, none) := by
    unfold Decode.decodeAt
    rw [dif_pos hpc, h0, opcodeOf_mem]
    cases m <;> rfl
  simp [State.decodedOp, State.decoded, hd, ha]

set_option hygiene false in
local macro "memcase" : tactic => `(tactic| (
  simp only [MemOp.exec, hs] at hx
  split at hx <;> try contradiction
  rename_i hcond
  simp only [Option.some.injEq] at hx
  subst hx))

theorem xstep {s s' : State} {x : XInstr} (hr : Ready s)
    (hc : CodeAt s.executionEnv.code s.pc.toNat x.bytes)
    (hx : x.exec s.fork s = some s') : Step s s' := by
  unfold XInstr.exec at hx
  split at hx <;> try contradiction
  next ha =>
  obtain ⟨s1, he, rfl⟩ := Option.map_eq_some_iff.1 hx
  clear hx
  have hx := he
  cases x with
  | base i =>
    simp only [XInstr.effect] at hx
    split at hx <;> try contradiction
    next stk hi =>
    split at hx <;> try contradiction
    next hg =>
    simp only [Option.some.injEq] at hx
    subst hx
    exact step_instr hr hc hg hi
  | tag _ => simp [XInstr.effect] at hx
  | mem m =>
    simp only [XInstr.effect] at hx
    have hop := decodedOp_mem hc ha
    cases m <;> simp only [XInstr.size, XInstr.bytes, List.length_cons,
      List.length_nil, Nat.zero_add]
    · rcases hs : s.stack with _ | ⟨off, rest⟩
      · simp [MemOp.exec, hs] at hx
      memcase
      exact Step.running hr.running hr.notPrecompile (StepRunning.mload (s := s) (offset := off)
        (rest := rest) (h_op := hop) (h_stack := hs) (h_gas := hcond.1)
        (h_cap := by simp [hs, Operation.pushArity, Operation.popArity]; omega))
    · rcases hs : s.stack with _ | ⟨off, _ | ⟨v, rest⟩⟩
      · simp [MemOp.exec, hs] at hx
      · simp [MemOp.exec, hs] at hx
      memcase
      exact Step.running hr.running hr.notPrecompile (StepRunning.mstore (s := s) (offset := off)
        (value := v) (rest := rest) (h_op := hop) (h_stack := hs) (h_gas := hcond.1)
        (h_cap := by simp [hs, Operation.pushArity, Operation.popArity]; omega))
    · rcases hs : s.stack with _ | ⟨off, _ | ⟨v, rest⟩⟩
      · simp [MemOp.exec, hs] at hx
      · simp [MemOp.exec, hs] at hx
      memcase
      exact Step.running hr.running hr.notPrecompile (StepRunning.mstore8 (s := s) (offset := off)
        (value := v) (rest := rest) (h_op := hop) (h_stack := hs) (h_gas := hcond.1)
        (h_cap := by simp [hs, Operation.pushArity, Operation.popArity]; omega))
    · rcases hs : s.stack with _ | ⟨key, rest⟩
      · simp [MemOp.exec, hs] at hx
      memcase
      exact Step.running hr.running hr.notPrecompile (StepRunning.sload (s := s) (key := key)
        (rest := rest) (h_op := hop) (h_stack := hs) (h_gas := hcond.1)
        (h_cap := by simp [hs, Operation.pushArity, Operation.popArity]; omega))
    · rcases hs : s.stack with _ | ⟨key, rest⟩
      · simp [MemOp.exec, hs] at hx
      memcase
      exact Step.running hr.running hr.notPrecompile (StepRunning.tload (s := s) (key := key)
        (rest := rest) (h_op := hop) (h_stack := hs) (h_gas := hcond.1)
        (h_cap := by simp [hs, Operation.pushArity, Operation.popArity]; omega))
    · rcases hs : s.stack with _ | ⟨key, _ | ⟨v, rest⟩⟩
      · simp [MemOp.exec, hs] at hx
      · simp [MemOp.exec, hs] at hx
      memcase
      exact Step.running hr.running hr.notPrecompile (StepRunning.tstore (s := s) (key := key)
        (value := v) (rest := rest) (h_op := hop) (h_perm := hcond.1) (h_stack := hs)
        (h_gas := hcond.2.1)
        (h_cap := by simp [hs, Operation.pushArity, Operation.popArity]; omega))
    · rcases hs : s.stack with _ | ⟨off, _ | ⟨sz, rest⟩⟩
      · simp [MemOp.exec, hs] at hx
      · simp [MemOp.exec, hs] at hx
      memcase
      exact Step.running hr.running hr.notPrecompile (StepRunning.keccak256 (s := s)
        (offset := off) (size := sz) (rest := rest) (h_op := hop) (h_stack := hs)
        (h_gas := hcond.1)
        (h_cap := by simp [hs, Operation.pushArity, Operation.popArity]; omega))

theorem effect_preserves {f : Fork} {x : XInstr} {s s1 : State} (h : x.effect f s = some s1) :
    s1.halt = s.halt ∧ s1.executionEnv = s.executionEnv := by
  cases x with
  | base i =>
    simp only [XInstr.effect] at h
    split at h <;> try contradiction
    split at h <;> try contradiction
    simp only [Option.some.injEq] at h; subst h; exact ⟨rfl, rfl⟩
  | tag _ => simp [XInstr.effect] at h
  | mem m =>
    simp only [XInstr.effect, MemOp.exec] at h
    split at h <;> (try contradiction) <;> (split at h <;> try contradiction) <;>
      (simp only [Option.some.injEq] at h; subst h; exact ⟨rfl, rfl⟩)

theorem xencode_cons (x : XInstr) (b : XBlock) : xencode (x :: b) = x.bytes ++ xencode b := by
  simp [xencode]

/-- **Stage 8 headline (concrete).** If the code at `pc` is `b` and `xrun` succeeds, the
    specification executes `b` to exactly `xrun`'s final state. -/
theorem xrun_sound (b : XBlock) : ∀ (s s' : State), Ready s →
    CodeAt s.executionEnv.code s.pc.toNat (xencode b) →
    s.pc.toNat + (xencode b).length < UInt256.size →
    xrun s.fork b s = some s' → Steps s s' := by
  induction b with
  | nil => intro s s' _ _ _ h; simp [xrun] at h; subst h; exact Steps.refl _
  | cons x b ih =>
    intro s s' hr hc hpc h
    simp only [xrun, Option.bind_eq_some_iff] at h
    obtain ⟨s1, h1, h2⟩ := h
    rw [xencode_cons] at hc hpc
    rw [List.length_append] at hpc
    obtain ⟨hcx, hcb⟩ := CodeAt.append.1 hc
    have hstep := xstep hr hcx h1
    unfold XInstr.exec at h1
    split at h1 <;> try contradiction
    obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.1 h1
    obtain ⟨hhalt, henv⟩ := effect_preserves he
    have hpc1 : (s.pc + UInt256.ofNat x.size).toNat = s.pc.toNat + x.size :=
      toNat_pc_add (by unfold XInstr.size; omega)
    refine Steps.trans hstep (ih _ s' ⟨?_, ?_⟩ ?_ ?_ ?_)
    · simpa [hhalt] using hr.running
    · simpa [henv] using hr.notPrecompile
    · simp only [henv]; rw [hpc1]; exact hcb
    · simp only; rw [hpc1]; unfold XInstr.size; omega
    · have hf : ({ e with pc := s.pc + UInt256.ofNat x.size } : State).fork = s.fork := by
        simp [State.fork, henv]
      rw [hf]; exact h2

end EvmOpt
