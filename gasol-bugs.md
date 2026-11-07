# gasol bugs

gasol at `gasol-optimizer/` HEAD ff5efe78. Paths are relative to `gasol-optimizer/`;
`GO` = `sfs_generator/gasol_optimization.py`. In gasol terms the first argument is the top
of stack (`inpt_sk[0]`), e.g. `SUB(X,0)` = X − 0 and `SHL(a,b)` shifts b by a.

Status: **confirmed end-to-end** = gasol run on a block (`scripts/gasol_diff.sh
Tests/gasol_bug_blocks.txt -solver z3`, gasol in a venv with networkx+pandas, z3 4.x) emits
code that `evmopt check` rejects and the concrete counterexample search shows wrong;
**confirmed (rule level)** = the rule as written is refuted by a kernel-checked
counterexample (`Tests/GasolBugs.lean`) but was not triggered end-to-end yet;
**suspected** = found by reading the code only.

## Wrong code emitted (confirmed end-to-end)

A. **Float division in constant folding.** `PUSH1 0x3 PUSH32 0xff…ff DIV` →
   `PUSH32 0x5555555555555400…00`; correct is `0x5555…55` (`(2^256-1)/3`). See 12.
B. **MUL result not reduced mod 2^256.** `PUSH1 0x2 PUSH32 0x80…00 MUL` →
   `PUSH33 0x1000…00` (PUSH33 does not exist); correct is `PUSH0`. See 11.
C. **ADD result not reduced mod 2^256.** `PUSH1 0x1 PUSH32 0xff…ff ADD` → `PUSH33 0x1000…00`;
   correct is `PUSH0`. See 11.
D. **SMOD folded as unsigned MOD.** `PUSH1 0x3 PUSH32 0xff…ff SMOD` → `PUSH0`; correct is
   `SMOD(-1,3) = -1` = `0xff…ff`. See 4.

H. **Stack limit not modelled: output needs a higher stack peak.** Corpus run
   (`examples/jsons-solc`, 24 contracts, `-solver z3`, compared with `evmopt --fork cancun
   gasolcmp`): of 1114 changed stack-only blocks, 1003 validate and 111 are rejected only
   because gasol's block needs more stack room, e.g.
   `PUSH1 0x01 PUSH1 0x01 PUSH1 0xa0 SHL SUB DUP4 AND` (peak +3) →
   `DUP3 PUSH1 0x01 DUP1 PUSH1 0xa0 SHL SUB AND` (peak +4). From a 1021-item stack the
   original runs and gasol's code overflows (exceptional halt). Corner case, but a real
   semantic change. No other wrong code found among stack-only blocks; 8562 blocks with
   memory/storage/env ops are not checkable yet.

   Re-run at 55b306d (28 contracts, `benchmark-55b306d.md`): 137 of 1397 changed
   stack-only blocks.

I. **Memory/storage rewrites (16-19) not reproduced on the corpus.** Of 1717 effect blocks,
   206 gasol rewrites change the effect sequence; `gasolcmp` ran both versions on 200 random
   frames each (random stack and memory, zero storage) and found no difference. Still
   suspected: random frames rarely hit overlapping offsets, and storage was all zero.

J. **Resource blow-up:** `0x5552F868…` grows gasol's temp dir past 8.5 GB within 22 min
   (11 GB in an earlier run before the 50 min limit), filling a 16 GB /tmp.

## Crashes (no output; block left unoptimised)

E. `DUP1 NOT NOT` → `Exception: ('Error in RBR generation', 4)` (cf. 7).
F. `PUSH1 0x7 PUSH1 0x5 PUSH1 0x3 ADDMOD` → same exception (cf. 15).
G. `PUSH1 0x1 PUSH32 0x80…00 SAR` → no optimized sequence printed.

## Notes from the same run
- gasol emits `PUSH0` by default (no `-push0` flag given), i.e. it assumes Shanghai+.
- Rules 1-3 did not fire in `-bl` mode on `PUSH1 0x0 SHL`, `PUSH1 0x0 SWAP1 SHL`,
  `DUP1 DIV` (gasol left them unchanged).

## Rewrite rules

1. **SHL(0,X)/SHR(0,X) returns 0 instead of X** — confirmed (rule level; not triggered in `-bl`).
   GO:4135-4141 returns `inp_vars[0]` (the zero shift) instead of `inp_vars[1]`.
   Counterexample: `SHL(0,1)` = 1, gasol gives 0. Introduced by commit 25f09177 ("fixing
   rule"), which also enabled SHL/SHR in `apply_transform_rules`.
2. **SHL(X,0)/SHR(X,0) returns the shift amount instead of 0** — confirmed (rule level).
   GO:4142-4148 returns `inp_vars[0]`. Counterexample: `SHL(5,0)` = 0, gasol gives 5.
3. **DIV(X,X) → 1 and SDIV(X,X) → 1** — confirmed (rule level). GO:3997-4003. Wrong for
   X = 0: `DIV(0,0)` = 0.
4. **SMOD modelled as MOD** — confirmed end-to-end (D). `sfs_generator/ir_block.py:240-244`
   emits `v1 % v2` for SMOD, same as MOD; `funct_to_opcode("%")` (GO:2743) maps back to MOD.
   Counterexample: `SMOD(-1,3)` = −1 (2^256−1), `MOD(2^256−1,3)` = 0.
5. **ISZ(ISZ(op)) / ISZ(ISZ(ISZ(X))) can leave dangling variables** — suspected.
   GO:4291-4308, 4326-4344 delete the middle ISZERO after checking only that its output is
   not in the target stack and has one ISZERO user; another consumer would dangle.
6. **OR(OR(X,Y),Y)** — suspected. GO:4609 reassigns `outpt_sk` without
   `update_tstack_userdef` (the AND variant does it).
7. **NOT(NOT(X))** — suspected. GO:4780 uses `instr["inpt_sk"]` (a list) instead of `[0]`.
8. **OR(X,NOT(X)) unreachable** — suspected (missed optimisation). GO:4775 filters for
   `NOT` instead of `OR`.
9. **`"outpr_sk"` typo** — suspected. GO:4961, 4999: KeyError when an equivalent SHL exists.
10. **MOD rules dead** — suspected (missed optimisation). MOD(X,1)/MOD(X,X)/MOD(X,0)
    (GO:4014-4030) exist but MOD is not in `apply_transform_rules`' list (GO:4175).

## Constant folding (`evaluate_expression`, GO:1476-1514)

11. **No mod 2^256 for `+ - * ^`** — confirmed end-to-end for `+`, `*` (B, C). 0−1 folds to −1; output does
    `hex(int(result))[2:]` (GO:2994) and `hex(-1)[2:]` is `'x1'`.
12. **Float division for `/`, `shr`, `sar`** — confirmed end-to-end for `/` (A). `math.floor(val0/val1)` loses
    precision for large values (`math.floor((2**256-1)/3) != (2**256-1)//3`).
13. **SAR folded unsigned** — suspected. Wrong whenever the value's high bit is set.
14. **Division/modulo by zero raises instead of giving 0** — suspected (missed
    optimisation only: `gasol_asm.py:587/597` catch it and skip the block).
15. **`compute_ternary` folds strings** — suspected. GO:1613 builds `vals` as strings without
    `int()`, so `+` concatenates.

## Memory/storage

16. **Overlapping MSTOREs at different constant offsets treated as independent** —
    suspected. GO:6627-6631: `mstore(0,a); mstore(16,b)` get no ordering edge;
    `mstore(0,v); mstore(16,w); mload(0)` can fold to `v`.
17. **MSTORE vs KECCAK overlap checked one-sided** — suspected. GO:6569-6585 only flag
    dependence when the store starts at/after the hash region start.
18. **`remove_store_loads` compares a list to a string** — suspected. GO:5769, 5822: always
    takes the memory branch, so `sstore(k, sload(k))` is never removed; `find("mstore")`
    also matches `mstore8`, so `mstore8(x, mload(x))` (not a no-op) could be removed.
19. **MSIZE merged by CSE / unordered against memory ops** — suspected. MSIZE is not a split
    point (`global_params/constants.py:5`) nor excluded in `unify_user_defins` (GO:7180).
