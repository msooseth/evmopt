# EVM block superoptimizer in Lean

A gasol-style (`gasol-optimizer/`) basic-block superoptimizer for EVM, written in Lean 4
and proven correct against powdr-labs' `evm-semantics` (`evm-semantics/`).

## Decisions

- **Spec:** `evm-semantics`. Its `StepRunning` rules give each opcode's post-state as an
  explicit `{ s with … }` update, `Step` is deterministic (`step_iff_stepF`), and `stepF`
  is a proven-equivalent executable for differential testing.
- **Level:** we rewrite solc assembly (symbolic `tag`s), not raw bytecode, so the optimised
  block may change length; the assembler resolves jump targets. A relocation-correctness
  proof for the assembler is out of scope for now.
- **Trust:** the search is untrusted. Only the checker and its soundness proof are trusted.
- **Guarantee (per block `B` rewritten to `B'`):** from any state where `B` runs to its end
  without an exception, `B'` also runs to its end and reaches the same state, except `pc`,
  code, and more-or-equal remaining gas.
- **Not preserved:** behaviour from states where `B` throws (underflow, OOG, stack
  overflow). solc code has statically known stack heights so underflow is unreachable;
  OOG differing is inherent to using less gas. Same stance as gasol.
- **Excluded from blocks:** `PC`, `GAS` (they observe pc/gas), and anything that ends a block
  (`JUMP`, `JUMPI`, `JUMPDEST`, halts, calls, creates). Self-code observation (`CODECOPY`
  over the contract's own code) is assumed not to depend on the optimised bytes.

## Stages

Everything is written in Lean. Each stage ends with a commit; `lake build` must be clean
(no `sorry`, no warnings).

### 0. Project setup
Lake project `EvmOpt` requiring `evm-semantics` (local path). Builds clean.

### 1. Stack-level block semantics
- `Block := List Instr` over PUSH0–PUSH32, DUPn, SWAPn, POP and pure stack→stack
  arithmetic/comparison/bitwise ops (ADD … SAR, no memory/storage/env).
- `run : Block → List UInt256 → Option (List UInt256)` (none on underflow),
  `cost : Fork → Block → Nat`, `size : Block → Nat`, `peak : Block → List UInt256 → Nat`.
- `encode : Block → List UInt8` and a decode lemma: code bytes at `pc` = `encode B` ⇒
  `decodeAt` yields `B`'s ops in order (pc is a `UInt256`; PUSHk advances it by `k+1`).
- **Theorem `run_sound`:** if `s.halt = .Running`, the code at `s.pc` is `encode B`, the
  ops are available in `s.fork`, `cost B ≤ s.gasAvailable`, peak stack ≤ 1024 and
  `run B s.stack = some stk'`, then
  `Steps s { s with stack := stk', pc := s.pc + size B, gasAvailable := … - cost B }`.
- Differential test: `run` vs. iterated `stepF` on random blocks/stacks.

### 2. Peephole rewrites on stack code
Local rules on `Instr` windows, each a theorem about `run`/`cost`/`peak`
(`SWAPn SWAPn → ε`, `DUPn POP → ε`, `PUSH a PUSH b ADD → PUSH (a+b)`, `PUSH 0 ADD → ε`,
`ISZERO ISZERO ISZERO → ISZERO`, …). Arithmetic facts via a `UInt256 ≃ BitVec 256` bridge
and `bv_decide`. Composed with `run_sound` this gives the end-to-end guarantee for any
sequence of rule applications. First user-visible optimizer.

### 3. Lift to SSA (block level)
- SSA block: inputs `%0 … %d-1`, a list of `let %v := op(args)` (args are inputs, earlier
  values or constants), and an output stack of values. Equivalent to gasol's SFS but with
  explicit sharing.
- `lift : Block → Option SSA` with **theorem `lift_sound`:** `eval (lift B) stk = run B stk`.

### 4. Rewrite in SSA
Constant folding, algebraic simplification, CSE, dead-value elimination, commutative
normalisation; each pass proven to preserve `eval`.

### 5. Lower back to stack code (untrusted) + translation validation
- Stack scheduler from SSA to `Block` (port gasol's greedy generator; optimal search or an
  SMT oracle later). Unproven.
- Validator: `check B B' := lift B' ≡ opt (lift B)` (syntactic after normalisation) plus
  `cost`/`peak` comparison. **Theorem `check_sound`** follows from `lift_sound` and the
  pass proofs, so only lift, the SSA passes and the validator are trusted. On failure keep
  the original block.

### 6. SSA-CFG (whole function)
- Lift a contract to a CFG of SSA blocks with block arguments (stack layout at block
  entry), resolving jump targets: constant tags first, then pushed return-address tags
  (legacy codegen) via a small tag-propagation analysis; unresolved dynamic jumps keep
  their region unoptimised.
- Cross-block rewrites; lowering must agree on each edge's stack layout.
- Simulation theorem across blocks on `Steps`.

### 7. Frontend and benchmarks
- Parse gasol's plain block format (`gasol-optimizer/examples/blocks`) early (needed from
  stage 2 for testing), then solc `--combined-json asm`; emit optimised asm.
- Benchmark gas/size against gasol on `gasol-optimizer/examples/`.

### Later
Memory/storage/keccak as SSA ops with effect ordering, dynamic memory-expansion gas, size
criterion, relocation-correctness of the assembler.
