# EVM block superoptimizer in Lean

A gasol-style (`gasol-optimizer/`) basic-block superoptimizer for EVM, written in Lean 4
and proven correct against powdr-labs' `evm-semantics` (`evm-semantics/`).

Markers: `[todo]`, `[wip]`, `[done]`.

## Decisions

- **Spec:** `evm-semantics`. Its `StepRunning` rules give each opcode's post-state as an
  explicit `{ s with … }` update, `Step` is deterministic (`step_iff_stepF`), and `stepF`
  is a proven-equivalent executable for differential testing.
- **Level:** we rewrite solc assembly (symbolic `tag`s), not raw bytecode, so the optimised
  block may change length; the assembler resolves jump targets. A relocation-correctness
  proof for the assembler is out of scope for now.
- **Trust = translation validation.** Every rewriter (peephole, SSA passes, lowering) is
  untrusted. One trusted checker lifts original and candidate blocks to symbolic terms,
  normalises both, and compares terms, input depth, stack-limit slack, gas and fork
  availability. Algebraic rules live in the normaliser, each with an eval-preservation
  proof. A candidate the checker rejects is replaced by the original block.
- **Guarantee (per block `B` rewritten to `B'`):** from any state with ≤ 1024 stack items
  where `B` runs to its end without an exception, `B'` also runs to its end and reaches
  the same state, except `pc`, code, and more-or-equal remaining gas.
- **Not preserved:** behaviour from states where `B` throws (underflow, OOG, stack
  overflow). solc code has statically known stack heights so underflow is unreachable;
  OOG differing is inherent to using less gas. Same stance as gasol.
- **Excluded from blocks:** `PC`, `GAS` (they observe pc/gas), `EXP` (value-dependent gas,
  for now), and anything that ends a block (`JUMP`, `JUMPI`, `JUMPDEST`, halts, calls,
  creates). Self-code observation (`CODECOPY` over the contract's own code) is assumed not
  to depend on the optimised bytes.

## Stages

### 0. Project setup [done]
Lake project `EvmOpt` requiring `evm-semantics` (local path).

### 1. Stack-level block semantics [done]
- [done] `Instr` (PUSH0–32, DUPn, SWAPn, POP, `ArithOp`), `exec`, `run`, `cost`, `encode`.
- [done] Decoding: code bytes at `pc` = `encode B` ⇒ `decodeAt` yields `B`'s instructions.
- [done] `step_instr`: one instruction is one `Step`.
- [done] `run_sound`: `run B s.stack = some stk'` + gas ⇒ `Steps s (blockPost s B stk')`.
- [todo] Differential test of `run` vs. iterated `stepF` on random blocks/stacks.

### 2. Symbolic lift (SFS) [wip]
- [done] `Term` (vars, consts, `app1/2/3`), symbolic stack `SState` (terms, input depth,
  stack-limit slack), `sstep`, `srun`, `lift`.
- [todo] `srun_run`: concrete `run` on `conc stk S` = `conc stk` of the symbolic result,
  with exactly matching underflow/overflow conditions.

### 3. Trusted checker [todo]
- [todo] `check f B B'`: normalised terms equal (padding the shallower side with vars),
  `d' ≤ d`, slack condition, `cost B' ≤ cost B`.
- [todo] `check_sound`: `check = true` ∧ `run B stk = some r` ⇒ `run B' stk = some r`;
  composed with `run_sound` this is the guarantee above.
- [todo] `optimize f B := if check f B (rewrite B) then rewrite B else B`.

### 4. Normaliser rules (each proven eval-preserving) [todo]
gasol's SFS rules (`sfs_generator/gasol_optimization.py`), `X` = any term:
- [todo] constant folding of every `ArithOp` on constant args (gasol `EVAL`)
- [todo] `ADD(X,0) → X`
- [todo] `SUB(X,0) → X`
- [todo] `SUB(X,X) → 0`
- [todo] `MUL(X,1) → X`
- [todo] `MUL(X,0) → 0`
- [todo] `MOD(X,X) → 0`
- [todo] `MOD(X,1) → 0`
- [todo] `MOD(X,0) → 0`
- [todo] `AND(X,X) → X`
- [todo] `AND(X,0) → 0`
- [todo] `AND(X,2^256-1) → X`
- [todo] `OR(X,X) → X`
- [todo] `OR(X,0) → X`
- [todo] `XOR(X,X) → 0`
- [todo] `XOR(X,0) → X`
- [todo] `EQ(X,X) → 1`
- [todo] `LT(X,0) → 0`
- [todo] `GT(0,X) → 0`
- [todo] `ISZ(0) → 1`, `ISZ(1) → 0` (subsumed by folding)
- [todo] `NOT(NOT(X)) → X` and gasol's other `NOT(X)` forms
- [todo] `ISZERO(ISZERO(ISZERO(X))) → ISZERO(X)`
- [todo] commutative argument ordering (ADD, MUL, AND, OR, XOR, EQ)
- [todo] `GT(X,Y) ↔ LT(Y,X)`, `SGT(X,Y) ↔ SLT(Y,X)` canonical form
- (EXP rules `EXP(X,0)`, `EXP(X,1)`, `EXP(1,X)` wait for EXP support)

### 5. Peephole rewriter (untrusted) [todo]
Stack-local windows proposing candidates for the checker:
- [todo] `SWAPn SWAPn → ε`
- [todo] `DUPn POP → ε`, `PUSH x POP → ε`
- [todo] `op POP → POP…` (drop a dead pure result)
- [todo] `PUSH a PUSH b op → PUSH (a op b)` (and unary/ternary folding)
- [todo] identity-element forms (`PUSH0 ADD → ε`, `PUSH1 1 MUL → ε`, `PUSH0 SWAP1 SUB → ε`, …)
- [todo] `DUP1 op` self-forms (`DUP1 SUB → POP PUSH0`, `DUP1 AND → ε`, …)
- [todo] `SWAP1 comm-op → comm-op`, `SWAP1 LT → GT`, …
- [todo] `NOT NOT → ε`, `ISZERO ISZERO ISZERO → ISZERO`
- [todo] `PUSH1 0 → PUSH0` (Shanghai+)

### 6. Frontend and gasol comparison [todo]
- [todo] Parse gasol's plain block format (`gasol-optimizer/examples/blocks`), optimise,
  print gas/size before/after.
- [todo] solc `--combined-json asm` input (`gasol-optimizer/examples/jsons-solc`): split
  into blocks, optimise, emit.
- [todo] Benchmark against gasol's results; record disagreements; log gasol bugs in
  `gasol-bugs.md`.

### 7. SSA lift / rewrite / lower (block level) [todo]
- [todo] SSA with explicit sharing (CSE, dead-value elimination) over `Term` DAGs.
- [todo] Stack scheduler from SSA to `Block` (port gasol's greedy generator); validated by
  the checker.

### 8. SSA-CFG (whole function) [todo]
- [todo] CFG of SSA blocks with block arguments; jump-target resolution (constant tags,
  pushed return-address tags); unresolved dynamic jumps keep their region unoptimised.
- [todo] Cross-block rewrites; lowering agrees on each edge's stack layout.
- [todo] Simulation theorem across blocks on `Steps`.

### Later [todo]
Memory/storage/keccak as SSA ops with effect ordering, EXP and dynamic memory-expansion
gas, size criterion, relocation-correctness of the assembler.
