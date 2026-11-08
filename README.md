# evmopt: a proven EVM block optimizer

A gasol-style superoptimizer for EVM basic blocks, written in Lean 4. Every rewrite is checked
by a validator whose soundness is proven against powdr-labs'
[evm-semantics](https://github.com/powdr-labs/evm-semantics). Design and status: `plan.md`;
bugs found in gasol: `gasol-bugs.md`; results: `benchmark-*.md`.

## Requirements

- git
- [elan](https://github.com/leanprover/elan) (Lean toolchain manager); the Lean version
  (4.33.0) is pinned in `lean-toolchain` and installed by elan on first build. The toolchain
  bundles its own clang and linker. On macOS, if linking `evmopt` fails for a missing SDK,
  install the Xcode command line tools (`xcode-select --install`).
- Python 3.9+ (the scripts use only the standard library)

To compare against gasol, additionally:

- [z3](https://github.com/Z3Prover/z3) on `PATH` (`brew install z3`, `apt install z3`, …)
- a Python environment with gasol's dependencies: `networkx` and `pandas`
- disk space: gasol's temporary files reach several GB for some contracts (one corpus
  contract exceeds 8 GB); they go under the output directory, not `/tmp`

## Setup

```sh
git clone <this repo> evm-rewrite && cd evm-rewrite
git clone https://github.com/powdr-labs/evm-semantics
git -C evm-semantics checkout 2f8714d6ba960a3de67720019b54513f5bc1a2e3
git clone https://github.com/costa-group/gasol-optimizer
git -C gasol-optimizer checkout ff5efe78581df35c1c1e49b9d92f4a338f3744ca
lake build
```

`lake build` checks all proofs (`Checks.lean` pins the axioms of the main theorems), runs the
regression tests in `Tests/`, and builds `.lake/build/bin/evmopt`. The first build compiles
evm-semantics and takes a few minutes.

## Using evmopt

```sh
E=.lake/build/bin/evmopt
$E opt gasol-optimizer/examples/blocks/redundant_swap.txt   # gasol's block format, one per line
$E check "SWAP1 SWAP4 DUP5 SWAP2 SWAP1" "DUP2 SWAP5"           # validate a stack-only rewrite
$E xcheck "PUSH0 MLOAD DUP1 ADD" "PUSH0 MLOAD DUP1 ADD"        # ... one with memory/storage ops
$E stats gasol-optimizer/examples/jsons-solc/*.json_solc      # solc --combined-json asm
$E gasolcmp ORIG.json_solc GASOL_OPTIMIZED.json_solc          # validate gasol's output
```

All commands take `--fork london|paris|shanghai|cancun|prague|osaka` first (default
`cancun`); PUSH0 is used only from Shanghai on.

## Comparing with gasol

1. Python environment for gasol:

   ```sh
   python3 -m venv ~/gasol-venv && ~/gasol-venv/bin/pip install networkx pandas
   ```

2. Run gasol on its own corpus (30 contracts). It writes per contract a log summary, the
   optimised asm and its per-block CSV (gzipped) under `--out`:

   ```sh
   scripts/run_gasol.py --python ~/gasol-venv/bin/python --out bench/gasol-run/raw --jobs 8
   ```

   With 8 jobs this takes about an hour; `--timeout` (default 3000 s) bounds each contract,
   `--only 0x08B0 0x0c9C` restricts it to some contracts. `bench/*/raw/` is gitignored.

3. Benchmark evmopt against those results:

   ```sh
   scripts/benchmark.py --gasol bench/gasol-run/raw --jobs 12 > benchmark-$(git rev-parse --short HEAD).md
   ```

   Per contract: evmopt time and peak memory, gas and bytes saved; gasol's time and its own
   estimate of gas saved. Then, summed over the corpus, `gasolcmp`'s verdict on every gasol
   block rewrite: validated by our checker, rejected (with a concrete counterexample if one
   is found on random inputs), or changing memory/storage operations.

A recorded gasol run (summary only) is in `bench/gasol-ff5efe78/summary.csv`.

Single blocks: `GASOL_PY=~/gasol-venv/bin/python scripts/gasol_diff.sh blocks.txt -solver z3`
runs gasol on each line of `blocks.txt` and validates its output with `evmopt check`
(`Tests/gasol_bug_blocks.txt` holds blocks that expose gasol bugs).

## Layout

- `EvmOpt/` — the optimizer. Trusted (proven): `Instr`, `Decode`, `Sound`, `Term`, `Lift`,
  `Norm`, `Check`, `Peephole`, `Mem`, `MemLift`, `MemTags`. Untrusted candidate generators:
  `Rules`, `Search`, `XOpt`. Frontend: `Asm`, `SolcAsm`, `Main.lean`.
- `Checks.lean` — axiom pins of the headline theorems.
- `Tests/` — `#guard` regression tests, kernel-checked gasol counterexamples.
- `scripts/` — `benchmark.py`, `run_gasol.py`, `gasol_tmp.py`, `gasol_diff.sh`.
