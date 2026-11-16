# Comparing with gasol

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

   Per contract: evmopt's time, memory, gas and bytes saved; gasol's time and the gas and
   bytes its validated rewrites save. Then `gasolcmp`'s verdict on every gasol rewrite.

A recorded gasol run (summary only) is in `bench/gasol-ff5efe78/summary.csv`.

Single blocks: `GASOL_PY=~/gasol-venv/bin/python scripts/gasol_diff.sh blocks.txt -solver z3`
runs gasol on each line of `blocks.txt` and validates its output with `evmopt verify`
(`Tests/gasol_bug_blocks.txt` holds blocks that expose gasol bugs).
