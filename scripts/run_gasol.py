#!/usr/bin/env python3
"""Run gasol on every contract of its asm corpus, in parallel, into OUT/<name>/.

Usage: scripts/run_gasol.py --python PY --out DIR [--jobs N] [--timeout S] [--only NAME...]
PY must have gasol's dependencies (networkx, pandas). gasol's temp files go to OUT/<name>/tmp
(they can reach many GB for some contracts); they are removed after each contract.
"""
import argparse
import concurrent.futures as cf
import gzip
import os
import shutil
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CORPUS = ROOT / "gasol-optimizer/examples/jsons-solc"
WRAPPER = ROOT / "scripts/gasol_tmp.py"


def run_one(path, args):
    d = args.out / path.stem
    tmp = d / "tmp"
    tmp.mkdir(parents=True, exist_ok=True)
    try:
        with open(d / "full-log.txt", "w") as log:
            r = subprocess.run([args.python, "-W", "ignore", str(WRAPPER), str(path), "-solver", "z3"],
                               cwd=d, stdout=log, stderr=subprocess.STDOUT, timeout=args.timeout,
                               env={**os.environ, "GASOL_TMP": str(tmp)})
        status = str(r.returncode)
    except subprocess.TimeoutExpired:
        status = "timeout"
    shutil.rmtree(tmp, ignore_errors=True)
    full = d / "full-log.txt"
    keep = ("Total time", "Estimated", "number of instructions", "Error", "Exception")
    (d / "log.txt").write_text("".join(l for l in full.read_text(errors="replace").splitlines(True)
                                       if l.startswith(keep)))
    full.unlink()
    for f in list(d.glob("*_optimized.json_solc")) + list(d.glob("blocks.csv")):
        f.with_name(f.name + ".gz").write_bytes(gzip.compress(f.read_bytes()))
        f.unlink()
    return path.stem, status


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--python", required=True)
    ap.add_argument("--out", type=Path, required=True)
    ap.add_argument("--jobs", type=int, default=8)
    ap.add_argument("--timeout", type=int, default=3000)
    ap.add_argument("--only", nargs="*")
    args = ap.parse_args()
    args.out = args.out.resolve()
    files = sorted(CORPUS.glob("*.json_solc"))
    if args.only:
        files = [f for f in files if any(f.stem.startswith(o) for o in args.only)]
    with cf.ThreadPoolExecutor(args.jobs) as ex:
        for name, status in ex.map(lambda f: run_one(f, args), files):
            print(f"{name} {status}", flush=True)


if __name__ == "__main__":
    main()
