# evmopt: a proven EVM block optimizer

> **Acknowledgement.** This project is inspired by and builds on the ideas of
> [GASOL](https://github.com/costa-group/gasol-optimizer), the EVM superoptimizer by
> **Elvira Albert, Pablo Gordillo, Alejandro Hernández-Cerezo, Albert Rubio and Maria A. Schett**
> (COSTA group). The stack functional specification (SFS) representation of a block, the
> simplification rules and the overall approach (lift a block, simplify, re-synthesise cheaper
> code) come from their work:
>
> - Elvira Albert, Pablo Gordillo, Alejandro Hernández-Cerezo, Albert Rubio.
>   [*A Max-SMT Superoptimizer for EVM handling Memory and Storage*](https://doi.org/10.1007/978-3-030-99524-9_11).
>   TACAS 2022, LNCS 13243, Springer.
> - Elvira Albert, Pablo Gordillo, Alejandro Hernández-Cerezo, Albert Rubio, Maria A. Schett.
>   [*Super-Optimization of Smart Contracts*](https://doi.org/10.1145/3506800).
>   ACM Transactions on Software Engineering and Methodology 31(4), 2022.
>
> The correctness proofs are against powdr-labs'
> [evm-semantics](https://github.com/powdr-labs/evm-semantics), a formal EVM semantics in Lean 4,
> which in turn builds on Nethermind's [EVMYulLean](https://github.com/NethermindEth/EVMYulLean).
> We thank both teams: without a precise, executable and conformance-tested model of the EVM,
> proving the optimiser correct would not be possible.

A gasol-inspired superoptimizer for EVM basic blocks, written in Lean 4. Every rewrite is checked
by a validator whose soundness is proven against powdr-labs'
[evm-semantics](https://github.com/powdr-labs/evm-semantics).

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
git clone https://github.com/msooseth/evmopt && cd evmopt
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

`optimize` reads blocks in gasol's text format, one per line, and prints a cheaper equivalent
of each (gas counts the stack instructions; memory/storage operations are kept as they are):

```
$ lake exe evmopt optimize gasol-optimizer/examples/blocks/order_load_instructions.txt
in:  PUSH1 0x08 SLOAD SWAP1 MLOAD SWAP1 DUP2 MSTORE SWAP1 DUP2 SWAP1 PUSH1 0x20 DUP3 ADD SWAP1
out: PUSH1 0x08 SLOAD SWAP1 MLOAD SWAP1 DUP2 MSTORE DUP1 PUSH1 0x20 ADD DUP2 SWAP3
     gas 33 -> 27, bytes 16 -> 14
```

`verify` checks a rewrite you supply (e.g. another optimizer's output) with the proven
checker; a rejection says why, with a concrete counterexample when one is found:

```
$ lake exe evmopt verify "SWAP1 SWAP4 DUP5 SWAP2 SWAP1" "DUP2 SWAP5"
verified: equivalent, gas 15 -> 6

$ lake exe evmopt verify "PUSH1 0x01 PUSH1 0x01 SUB" "PUSH1 0x01"
rejected: results differ, or could not be proven equal
  counterexample: input stack (top first) []
    original  -> [0x0]
    candidate -> [0x1]

$ lake exe evmopt verify "PUSH0 MLOAD POP" ""
rejected: candidate drops, adds or reorders memory/storage operations (not supported yet)
  (no concrete counterexample found)
```

The exit code is 0 for verified, 1 for rejected. `stats` optimises whole contracts from
`solc --combined-json asm` and prints totals:

```
$ lake exe evmopt stats gasol-optimizer/examples/jsons-solc/0x1f2cF791d940Bbb9fbe777271afa6ff9bBA8AbA0.json_solc
…: 400 blocks, stack-op gas 4868 -> 4577, stack-op bytes 3127 -> 3057
```

Options go first: `--fork london|paris|shanghai|cancun|prague|osaka` (default `cancun`;
PUSH0 is used only from Shanghai on).

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
runs gasol on each line of `blocks.txt` and validates its output with `evmopt verify`
(`Tests/gasol_bug_blocks.txt` holds blocks that expose gasol bugs).

## Layout

- `EvmOpt/` — the optimizer. Trusted (proven): `Instr`, `Decode`, `Sound`, `Term`, `Lift`,
  `Norm`, `Check`, `Peephole`, `Mem`, `MemLift`, `MemTags`. Untrusted candidate generators:
  `Rules`, `Search`, `XOpt`. Frontend: `Asm`, `SolcAsm`, `Main.lean`.
- `Checks.lean` — axiom pins of the headline theorems.
- `Tests/` — `#guard` regression tests, kernel-checked gasol counterexamples.
- `scripts/` — `benchmark.py`, `run_gasol.py`, `gasol_tmp.py`, `gasol_diff.sh`.

## License

GPL-3.0, the same as GASOL; see `LICENSE`. The evm-semantics dependency is Apache-2.0.
