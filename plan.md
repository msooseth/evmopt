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

### 2. Symbolic lift (SFS) [done]
- [done] `Term` (vars, consts, `app1/2/3`), symbolic stack `SState` (terms, input depth,
  stack-limit slack), `sstep`, `srun`, `lift`.
- [done] `srun_run`: concrete `run` on `conc stk S` = `conc stk` of the symbolic result,
  with exactly matching underflow/overflow conditions.

### 3. Trusted checker [done]
- [done] `check f B B'`: normalised terms equal (padding the shallower side with vars),
  `d' ≤ d`, slack condition, `cost B' ≤ cost B`.
- [done] `check_sound`: `check = true` ∧ `run B stk = some r` ⇒ `run B' stk = some r`;
  composed with `run_sound` this is the guarantee above.
- [done] `optimizeWith_steps` (end-to-end on `Steps`); `Checks.lean` pins axioms.
- [done] `optimizeWith f rw B := if check f B (rewrite B) then rewrite B else B`.

### 4. Normaliser rules (each proven eval-preserving) [wip]
gasol's SFS rules (`sfs_generator/gasol_optimization.py`), `X` = any term:
- [done] constant folding of every `ArithOp` on constant args (gasol `EVAL`)
- [done] `ADD(X,0) → X`
- [done] `SUB(X,0) → X`
- [done] `SUB(X,X) → 0`
- [done] `MUL(X,1) → X`
- [done] `MUL(X,0) → 0`
- [done] `MOD(X,X) → 0`
- [done] `MOD(X,1) → 0`
- [done] `MOD(X,0) → 0`
- [done] `AND(X,X) → X`
- [done] `AND(X,0) → 0`
- [done] `AND(X,2^256-1) → X`
- [done] `OR(X,X) → X`
- [done] `OR(X,0) → X`
- [done] `XOR(X,X) → 0`
- [done] `XOR(X,0) → X`
- [done] `EQ(X,X) → 1`
- [done] `LT(X,0) → 0`
- [done] `GT(0,X) → 0`
- [done] `ISZ(0) → 1`, `ISZ(1) → 0` (subsumed by folding)
- [done] `NOT(NOT(X)) → X`
- [done] `ISZERO(ISZERO(ISZERO(X))) → ISZERO(X)`
- [done] commutative argument ordering (ADD, MUL, AND, OR, XOR, EQ)
- [done] `GT(X,Y) ↔ LT(Y,X)`, `SGT(X,Y) ↔ SLT(Y,X)` canonical form
- [done] `DIV(X,1) → X`, `LT(X,X)`/`GT(X,X)`/`SLT(X,X)`/`SGT(X,X)` → 0
- [done] `GT(1,X) → ISZ(X)`, `LT(X,1) → ISZ(X)`, `EQ(0,X) → ISZ(X)`
- [done] `AND(X,AND(X,Y))`, `OR(OR(X,Y),Y)`, `OR(X,AND(X,Y)) → X`, `AND(X,OR(X,Y)) → X`,
  `XOR(X,XOR(X,Y)) → Y` (all argument orders)
- [todo] remaining gasol type-2 rules: `ISZ(GT(X,0)) → ISZ(X)`, `EQ(1,ISZ(X)) → ISZ(X)`, `ISZ(LT(0,X)) → ISZ(X)`, `ISZ(XOR(X,Y)) → EQ`,
  `ISZ(SUB(X,Y)) → EQ`, `AND(X,NOT(X)) → 0`, `OR(X,NOT(X)) → 2^256-1`,
  `MUL(X,SHL(Y,1)) → SHL(Y,X)`, `DIV(X,SHL(Y,1)) → SHR(Y,X)`, `AND(SHL(X,Y),SHL(X,Z))`
- [done] `SHL(0,X) → X`, `SHR(0,X) → X`, `SHL(X,0) → 0`, `SHR(X,0) → 0` (correct versions of
  gasol's buggy rules, see `gasol-bugs.md` 1-2)
- not taken: gasol's `DIV(X,X) → 1` / `SDIV(X,X) → 1` (unsound, `gasol-bugs.md` 3)
- (EXP rules `EXP(X,0)`, `EXP(X,1)`, `EXP(1,X)` wait for EXP support)

### 5. Peephole rewriter (untrusted proposals, proven driver) [done]
- [done] `pass`/`passes` driver: each window rewrite is validated by `check`; `pass_sound`.
- [done] regression tests `Tests/Peephole.lean`
Stack-local windows proposing candidates for the checker:
- [done] `SWAPn SWAPn → ε`
- [done] `DUPn POP → ε`, `PUSH x POP → ε`
- [done] `op POP → POP…` (drop a dead pure result)
- [done] `PUSH a PUSH b op → PUSH (a op b)` (and unary/ternary folding)
- [done] identity-element forms (`PUSH0 ADD → ε`, `PUSH1 1 MUL → ε`, `PUSH0 SWAP1 SUB → ε`, …)
- [done] `DUP1 op` self-forms (`DUP1 SUB → POP PUSH0`, `DUP1 AND → ε`, …)
- [done] `SWAP1 comm-op → comm-op`, `SWAP1 LT → GT`, …
- [done] `NOT NOT → ε`, `ISZERO ISZERO ISZERO → ISZERO`
- [done] `PUSH1 0 → PUSH0` (Shanghai+), minimal-width PUSH
- [done] `PUSH0 EQ → ISZERO`, `PUSH1 1 GT → ISZERO`, `PUSH1 1 SWAP1 LT → ISZERO`, `PUSH0 SHL/SHR → ε`

### 6. Frontend and gasol comparison [wip]
- [done] Parse gasol's plain block format (`gasol-optimizer/examples/blocks`), optimise,
  print gas/size before/after (`evmopt opt`); validate claimed rewrites (`evmopt check`).
  gasol's `redundant_swap` optimum `DUP2 SWAP5` validates.
- [todo] solc `--combined-json asm` input (`gasol-optimizer/examples/jsons-solc`): split
  into blocks, optimise, emit.
- [done] gasol differential: `scripts/gasol_diff.sh` runs gasol per block and validates
  its output with `evmopt check` + concrete counterexample search; targeted blocks in
  `Tests/gasol_bug_blocks.txt`; 4 wrong-code bugs and 3 crashes confirmed (`gasol-bugs.md`).
- [done] `evmopt stats` over solc asm json; `evmopt gasolcmp` block-pairs two asm jsons.
- [done] size policy `sizeOk`: at most one extra byte per 3 gas saved (stops folding solc's
  `PUSH 0 NOT`-style size tricks into PUSH32s).
- [done] corpus stats (`evmopt --fork london stats`, 30 contracts, 26580 blocks): stack-op
  gas 289351 -> 285653 (-1.3%), bytes 163397 -> 162467 (-0.6%). Small because barriers
  (memory/storage/env ops, `PUSH [tag]`) cut blocks into short runs; see stage 7.
- [todo] Run gasol on `examples/jsons-solc` and compare at scale with `gasolcmp`.

### 7. SSA lift / rewrite / lower (block level) [wip]
- [done] Lowering by goal-directed search (`Search.lean`): Dijkstra on gas over normalised
  symbolic states; moves restricted to DUP/SWAP within the original depth, POP, target
  constants, ops producing target subterms. Validated by `check`; `optimizeBlock_sound`.
  Finds gasol's `redundant_swap` optimum `DUP2 SWAP5` in 60 ms.
- [todo] Uninterpreted ops in `Term` (env reads, SLOAD/MLOAD/KECCAK with effect order,
  `PUSH [tag]` as opaque constants) so blocks span full basic blocks.
- [todo] Greedy scheduler for blocks beyond the search budget (port gasol's greedy).
- [todo] SSA with explicit sharing (CSE, dead-value elimination) over `Term` DAGs.

### 8. SSA-CFG (whole function) [todo]
- [todo] CFG of SSA blocks with block arguments; jump-target resolution (constant tags,
  pushed return-address tags); unresolved dynamic jumps keep their region unoptimised.
- [todo] Cross-block rewrites; lowering agrees on each edge's stack layout.
- [todo] Simulation theorem across blocks on `Steps`.

### Later [todo]
Memory/storage/keccak as SSA ops with effect ordering, EXP and dynamic memory-expansion
gas, size criterion, relocation-correctness of the assembler.
