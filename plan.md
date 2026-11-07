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
- [done] `ISZ(GT(X,0)) → ISZ(X)` (canonical `ISZ(LT(0,X))`), `ISZ(XOR(X,Y)) → EQ(X,Y)`,
  `ISZ(SUB(X,Y)) → EQ(X,Y)`, `EQ(1,B) → B` and `ISZ(ISZ(B)) → B` for boolean-valued `B`
  (subsumes `EQ(1,ISZ(X))`, `ISZ(ISZ(LT/GT/EQ…))`, `ISZ(ISZ(ISZ(X)))`),
  `MUL(X,SHL(Y,1)) → SHL(Y,X)`, `DIV(X,SHL(Y,1)) → SHR(Y,X)`
- [todo] `AND(X,NOT(X)) → 0`, `OR(X,NOT(X)) → 2^256-1`, `AND(SHL(X,Y),SHL(X,Z)) → SHL(X,AND(Y,Z))`
- [todo] `BALANCE(ADDRESS) → SELFBALANCE` (needs BALANCE: dynamic gas)
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
- [done] gasol on `examples/jsons-solc` (`-solver z3`) vs `gasolcmp` (28 contracts):
  stack-only blocks original 43328 gas, gasol (validated rewrites only) 41975, ours 41518;
  ours better on 33 blocks, gasol on 16 (long blocks needing CSE + reordering). gasol's
  stack-only rewrites: 1003 validate, 111 exceed the original stack peak (`gasol-bugs.md` H).
- [done] Speed and totals (30 contracts, one core): gasol median 486 s/contract (13345 s
  for 28), ours ~5 s/contract (161 s for 30). Stack-only blocks: original 43328, gasol 41975,
  ours 41630. Whole contract: gasol saves 15725 gas, ours 7333; the gap is the 10160 blocks
  with memory/storage/KECCAK/`PUSH [tag]` that we treat as barriers (stage 8).
- [todo] Check gasol's blocks with memory/storage ops (needs stage 8).

### 7. SSA lift / rewrite / lower (block level) [wip]
- [done] Lowering by goal-directed search (`Search.lean`): Dijkstra on gas over normalised
  symbolic states; moves restricted to DUP/SWAP within the original depth, POP, target
  constants, ops producing target subterms. Validated by `check`; `optimizeBlock_sound`.
  Finds gasol's `redundant_swap` optimum `DUP2 SWAP5` in 60 ms.
- [done] Env reads as terms: ADDRESS ORIGIN CALLER CALLVALUE CALLDATALOAD CALLDATASIZE
  GASPRICE RETURNDATASIZE BLOCKHASH COINBASE TIMESTAMP NUMBER PREVRANDAO GASLIMIT CHAINID
  SELFBALANCE BASEFEE (static gas, read-only frame σ threaded through `run`/`eval`;
  CODESIZE excluded: it observes the rewritten code). Corpus: stack-op gas -2.1%.
- [done] `AND(CALLER|ORIGIN|ADDRESS|COINBASE, 2^160-1) → X` (gasol type-2).
- [todo] `PUSH [tag]` as opaque constants.
- [done] `dupZero`: DUP of a known-zero item → PUSH0 (checked candidate).
- [done] Greedy scheduler (`greedy`): demand-counted emission with CSE (DUP1 keeps a copy
  while uses remain), last-use consumption in place / by SWAP, solc-style constant recipes
  (`PUSH0 NOT`, `1 DUP1 k SHL SUB`, `m s SHL`), then a DUP/POP/SWAP shuffle to the goal.
  Candidates ranked by gas + 3·bytes; `tryCand` requires check ∧ size policy ∧ better score.
  vs gasol (28 contracts, stack-only blocks): ours better on 57, gasol on 14.
- [todo] Remaining gasol wins: deep-stack reorderings (e.g. `SWAP8 POP … SWAP3 POP POP`).
- [todo] SSA with explicit sharing (CSE, dead-value elimination) over `Term` DAGs.

### 8. Memory, storage, KECCAK (next) [todo]
Goal: optimise the blocks we now cut at barriers, and validate gasol's memory/storage
rewrites (its alias analysis looks wrong: `gasol-bugs.md` 16-18).
- [done] Concrete core (`Mem.lean`): `XInstr` = `Instr` + MLOAD MSTORE MSTORE8 SLOAD TLOAD
  TSTORE KECCAK256; `xrun` over the full frame `State`, each op updating exactly the fields
  of its `StepRunning` rule incl. dynamic gas (memory expansion, cold SLOAD surcharge, KECCAK
  words) and pc; `xstep`/`xrun_sound`: `xrun b s = some s'` ⇒ `Steps s s'`.
- [todo] SSTORE (net-metered gas, refunds, sentry): barrier for now.
- [done] Effect-preserving milestone (`MemLift.lean`): symbolic state = stack terms + ordered
  effect list (op, argument terms) + static gas; load/KECCAK results are `Term.eff i`.
  `effRun` replays the effects; each op factored into gas-free `apply` + `costAt`, so
  `xsrun_xrun` (concrete run = symbolic prediction, exact failure conditions) needs no gas
  formula: equal effect lists give equal effect gas. `xcheck` (same normalised effects,
  stack result, depth/slack, ≤ static gas); `xcheck_sound`, `xcheck_steps` (end-to-end on
  `Steps`). TSTORE excluded symbolically (changes `accountMap`).
- [done] Candidate generation for effect blocks (`XOpt.lean`): per-segment `optimizeBlock`
  and `xgreedy` (effects emitted in order, CSE across them), both validated by `xcheck`;
  `optimizeX_sound`. Frontend no longer cuts blocks at MLOAD MSTORE MSTORE8 SLOAD TLOAD
  KECCAK256 (TSTORE still a barrier). Corpus (30 contracts): stack-op gas saved 7333 ->
  10462 (-3.6%), 32 s wall on 16 cores.
- [todo] gasolcmp on effect blocks: `xcheck` for gasol's effect-preserving rewrites, and a
  concrete differential (random frames incl. memory/storage, `xrun`) for the rest, to
  confirm or refute `gasol-bugs.md` 16-19.
- [todo] Effect-changing rewrites (next milestone): dynamic gas comparison (memory expansion
  telescopes to the final high-water mark; SLOAD cold surcharge depends on the key set) and
  final-state equality up to the access list's membership.
- [todo] Normaliser/checker rules, each proven: load-after-store forwarding with
  provably equal / provably disjoint addresses (constant offsets with 32-byte ranges for
  memory; MSTORE8 single byte), dead-store elimination, `store(k, load(k))` removal, KECCAK
  CSE when no intervening memory write overlaps its range.
- [todo] Scheduler/search: keep effects in a legal order; emit loads/stores from the
  effect list.
- [done] Assembler constants (`PUSH [tag]`, `PUSH #[$]`, `PUSH [$]`, `PUSH data`, …) as
  opaque atoms (`XInstr.tag`, `Term.tag`); concrete core unchanged. `xcheck_sound_asm`: for
  every assignment of PUSH1..32 values to tags, the assembled candidate matches the assembled
  original (via `xsrun_assemble`: lifting commutes with substitution). Schedulers use
  sentinel PUSH3s, validated against the real asm blocks.
- [done] Scheduler work to close the gap with gasol (see `benchmark-*.md`): pre-clean of
  dead inputs, last-use SWAP1/in-place commutative operands, interleaved effect emission,
  bottom-preserving goal construction, effect-ordered search, `DIV/MUL` by `2^k`, `PUSH c
  NOT` recipe. On the 4406 blocks gasol improves: evmopt 5655 -> 10474 gas (gasol 16279, of
  which ~2321 on effect blocks exceed the original stack peak).
- [todo] Reordering independent effects (gasol: 576 gas on effect blocks) — needs
  disjointness reasoning (milestone 2).
- [todo] Corpus re-run vs gasol including its memory/storage blocks (gasol temp dir inside
  the scratchpad, deleted afterwards: one run left 11G in /tmp); log confirmed bugs.

### 9. SSA-CFG (whole function) [todo]
- [todo] CFG of SSA blocks with block arguments; jump-target resolution (constant tags,
  pushed return-address tags); unresolved dynamic jumps keep their region unoptimised.
- [todo] Cross-block rewrites; lowering agrees on each edge's stack layout.
- [todo] Simulation theorem across blocks on `Steps`.

### Later [todo]
EXP (value-dependent gas), BALANCE/EXTCODE* (warm/cold gas), size criterion option,
relocation-correctness of the assembler.
