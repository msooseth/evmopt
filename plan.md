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

Each stage ends with a commit; `lake build` must be clean (no `sorry`, no warnings).

### 0. Project setup
Lake project `EvmOpt` requiring `evm-semantics` (local path). Builds clean.

### 1. Stack-only interpretation
- `Block := List Instr` over PUSH0–PUSH32, DUPn, SWAPn, POP and pure stack→stack
  arithmetic/comparison/bitwise ops (ADD … SAR, no memory/storage/env).
- `run : Block → List UInt256 → Option (List UInt256)` (none on underflow),
  `cost : Fork → Block → Nat`, `size : Block → Nat`, `peak : Block → List UInt256 → Nat`.
- **Theorem `run_sound`:** if `s.halt = .Running`, the code at `s.pc` decodes to `B`, the
  ops are available in `s.fork`, `cost B ≤ s.gasAvailable`, peak stack ≤ 1024 and
  `run B s.stack = some stk'`, then
  `Steps s { s with stack := stk', pc := s.pc + size B, gasAvailable := … - cost B }`.
- Differential test: `run` vs. iterated `stepF` on random blocks/stacks.

### 2. SFS and the proven checker
- `Term := input (i : Nat) | const (v : UInt256) | app (op) (args : List Term)`;
  `sfs : Block → Option (List Term × Nat)` (output terms, input depth consumed).
- **Theorem `sfs_sound`:** `sfs B = some (ts, d)` ⇒ `run B stk` = `ts` evaluated over `stk`
  (for `stk.length ≥ d`).
- `normalize : Term → Term` (sort commutative args, fold constants) with
  `eval (normalize t) = eval t`.
- `check : Fork → Block → Block → Bool` compares normalised SFS, input depth, cost and peak.
- **Theorem `check_sound`:** `check f B B' = true` ⇒ the guarantee above, stated on `Steps`.

### 3. Rewrite rules
Algebraic simplifications (`x+0`, `x*1`, `NOT NOT x`, `ISZERO ISZERO ISZERO x`, …) as
`Term` rewrites, each proved with `eval` preservation; arithmetic facts via a
`UInt256 ≃ BitVec 256` bridge and `bv_decide`.

### 4. Search (untrusted)
Port gasol's greedy block generator: given normalised SFS, produce a stack-op sequence.
Optional later: SMT oracle (OptiMathSAT/Z3) via subprocess for optimal sequences. Every
candidate goes through `check`; on failure keep the original block.

### 5. Frontend and benchmarks
- Parse gasol's plain block format (`gasol-optimizer/examples/blocks`), then solc
  `--combined-json asm`; split into blocks; emit the optimised asm.
- Benchmark gas/size against gasol on `gasol-optimizer/examples/`.

### Later
Memory/storage/keccak as uninterpreted ops with dependency ordering (gasol's
`store_uninterpreted`), dynamic memory-expansion gas, size criterion, whole-contract
theorem including relocation.
