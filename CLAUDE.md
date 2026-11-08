# EVM block optimizer in Lean

gasol-style (`gasol-optimizer/`) basic-block optimizer written in Lean 4, proven against
powdr-labs' `evm-semantics/` (local path dependency). `EVMYulLean/` and `powdr/` are
reference clones only; none of the clones are tracked in this repo.

## Plan tracking
- `plan.md` is the source of truth for what is being built. Every item carries `[todo]`,
  `[wip]` or `[done]`; each rewrite rule is its own sub-item.
- Update the markers in the same commit as the work. Commit each finished stage/sub-item.
- When the design changes, edit `plan.md` first (Decisions section), then the code.

## Build
- `lake build` from the repo root (Lean v4.33, Batteries only, no Mathlib). Builds the
  library, `Checks.lean` (axiom pins), `Tests/` (`#guard` regression tests) and `evmopt`.
- `lake exe evmopt optimize <blocks.txt>` optimises gasol-format blocks (one per line);
  `lake exe evmopt verify "<original>" "<candidate>"` validates a claimed rewrite.
- Trusted core: `Sound` (`run_sound`), `Lift` (`srun_run`), `Norm` (`norm_eval`), `Check`
  (`check_sound`, `optimizeWith_steps`), `Peephole` (`pass_sound`). Everything else
  (`Rules`, `Asm`, `Main`) is untrusted and only proposes candidates.
- No `sorry`, no new axioms: trusted theorems must print only
  `[propext, Classical.choice, Quot.sound]` under `#print axioms`.

## gasol bugs
gasol is a reference, not ground truth. When a proof attempt or a differential test shows
gasol's rule/folding/output is wrong w.r.t. the EVM semantics, record it in
`gasol-bugs.md`: file:line, the rule, a concrete counterexample (input stack/values),
expected vs. gasol result, and how it was found.
