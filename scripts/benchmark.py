#!/usr/bin/env python3
"""Benchmark evmopt (and optionally gasol's outputs) on gasol's asm corpus; prints markdown.

Usage: scripts/benchmark.py [--gasol DIR] [--jobs N] [--only NAME...]
With --gasol, only the contracts gasol finished.
DIR holds <name>/<name>_optimized.json_solc[.gz] and <name>/log.txt per contract (gasol runs),
e.g. bench/gasol-ff5efe78/raw.
"""
import argparse
import concurrent.futures as cf
import gzip
import tempfile
import os
import re
import subprocess
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
EVMOPT = ROOT / ".lake/build/bin/evmopt"
CORPUS = ROOT / "gasol-optimizer/examples/jsons-solc"

STATS = re.compile(r": (\d+) blocks, stack-op gas (\d+) -> (\d+), stack-op bytes (\d+) -> (\d+)")
NUM = re.compile(r"\d+")


def run_timed(cmd):
    """Stdout and wall seconds of one process."""
    t0 = time.perf_counter()
    out = subprocess.run(cmd, stdout=subprocess.PIPE, text=True, check=True).stdout
    return out, time.perf_counter() - t0


def gasol_log(log):
    if not log.exists():
        return None
    text = log.read_text(errors="replace")
    t = re.search(r"Total time: ([\d.]+)", text)
    return {"time": float(t.group(1)) if t else None}


def bench_one(path, gasol_dir):
    name = path.stem
    out, wall = run_timed([str(EVMOPT), "--fork", "cancun", "stats", str(path)])
    m = STATS.search(out)
    if m is None:
        raise RuntimeError(f"unexpected evmopt output for {name}: {out!r}")
    n, gb, ga, sb, sa = map(int, m.groups())
    row = {"name": name, "blocks": n, "time": wall, "gas": (gb, ga), "bytes": (sb, sa)}
    if gasol_dir:
        d = gasol_dir / name
        row["gasol"] = gasol_log(d / "log.txt")
        opt = d / f"{name}_optimized.json_solc"
        gz = opt.with_name(opt.name + ".gz")
        with tempfile.TemporaryDirectory() as tmp:
            if not opt.exists() and gz.exists():
                opt = Path(tmp) / opt.name
                opt.write_bytes(gzip.decompress(gz.read_bytes()))
            if opt.exists():
                cmp = subprocess.run([str(EVMOPT), "--fork", "cancun", "gasolcmp", str(path), str(opt)],
                                     capture_output=True, text=True).stdout
                row["cmp"] = cmp.splitlines()[-4:]
    return row


def sum_cmp(rows):
    """Aggregate gasolcmp's three summary lines over all contracts."""
    keys = {"blocks:": 8, "effect blocks:": 5, "stack-only blocks gas:": 5, "measured:": 6}
    tot = {k: [0] * n for k, n in keys.items()}
    for r in rows:
        for line in r.get("cmp", []):
            for k, n in keys.items():
                if line.startswith(k):
                    nums = list(map(int, NUM.findall(line)))[:n]
                    if len(nums) == n:
                        tot[k] = [a + b for a, b in zip(tot[k], nums)]
    return tot


def measured(r):
    """gasol's (gas, bytes) saved by its validated runs, and by its raw output."""
    for line in r.get("cmp", []):
        if line.startswith("measured:"):
            g0, g1, gv, b0, b1, bv = map(int, NUM.findall(line)[:6])
            return (g0 - gv, b0 - bv), (g0 - g1, b0 - b1)
    return None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--gasol", type=Path)
    ap.add_argument("--jobs", type=int, default=os.cpu_count())
    ap.add_argument("--only", nargs="*")
    args = ap.parse_args()
    files = sorted(CORPUS.glob("*.json_solc"))
    if args.only:
        files = [f for f in files if any(f.stem.startswith(o) for o in args.only)]
    if args.gasol:
        files = [f for f in files if (gasol_log(args.gasol / f.stem / "log.txt") or {}).get("time") is not None]
    t0 = time.perf_counter()
    with cf.ThreadPoolExecutor(args.jobs) as ex:
        rows = sorted(ex.map(lambda f: bench_one(f, args.gasol), files), key=lambda r: r["name"])
    total_wall = time.perf_counter() - t0

    print("| contract | blocks | evmopt s | gasol s | evmopt gas saved | gasol gas saved "
          "| evmopt bytes saved | gasol bytes saved | evmopt better |")
    print("|---|---:|---:|---:|---:|---:|---:|---:|---|")
    for r in rows:
        g = r.get("gasol") or {}
        gt = f"{g['time']:.0f}" if g.get("time") is not None else ("fail/timeout" if args.gasol else "-")
        m = measured(r) if g.get("time") is not None else None
        gg, gb = (str(m[0][0]), str(m[0][1])) if m else ("-", "-")
        eg, eb = r['gas'][0] - r['gas'][1], r['bytes'][0] - r['bytes'][1]
        better = {(True, True): "both", (True, False): "gas", (False, True): "bytes"}.get(
            (eg > m[0][0], eb > m[0][1]), "-") if m else "-"
        print(f"| {r['name'][:10]} | {r['blocks']} | {r['time']:.1f} | {gt} | "
              f"{eg} | {gg} | {eb} | {gb} | {better} |")
    gb = sum(r["gas"][0] for r in rows); ga = sum(r["gas"][1] for r in rows)
    sb = sum(r["bytes"][0] for r in rows); sa = sum(r["bytes"][1] for r in rows)
    gtime = [r["gasol"]["time"] for r in rows if r.get("gasol") and r["gasol"].get("time") is not None]
    print()
    print(f"- contracts: {len(rows)}, blocks: {sum(r['blocks'] for r in rows)}")
    print(f"- evmopt: sum of per-contract wall times {sum(r['time'] for r in rows):.1f} s, "
          f"wall {total_wall:.1f} s with {args.jobs} jobs")
    print(f"- evmopt stack-op gas {gb} -> {ga} (saved {gb - ga}), bytes {sb} -> {sa} (saved {sb - sa})")
    if args.gasol:
        print(f"- gasol: {len(gtime)} finished, total {sum(gtime):.0f} s")
        done = [r for r in rows if r.get("gasol") and r["gasol"].get("time") is not None and measured(r)]
        ev = (sum(r["gas"][0] - r["gas"][1] for r in done), sum(r["bytes"][0] - r["bytes"][1] for r in done))
        val = tuple(sum(measured(r)[0][i] for r in done) for i in (0, 1))
        raw = tuple(sum(measured(r)[1][i] for r in done) for i in (0, 1))
        print(f"- on the {len(done)} gasol finished, gas / bytes saved: evmopt {ev[0]} / {ev[1]}, "
              f"gasol validated {val[0]} / {val[1]}, gasol unvalidated {raw[0]} / {raw[1]}")
        tot = sum_cmp(rows)
        u, v, g0, g1, rj, wr, ns, mm = tot["blocks:"]
        print(f"- gasol stack-only rewrites: unchanged {u}, validated {v} ({g0} -> {g1} gas), "
              f"rejected {rj} (with counterexample {wr}), other blocks {ns}, block-count mismatches {mm}")
        e, es, eo, eb, eu = tot["effect blocks:"]
        print(f"- gasol effect-block rewrites: {e} blocks, unchanged {es}, validated {eo}, wrong {eb}, "
              f"effects changed without counterexample {eu}")
        o, gg, ours, ob, gbt = tot["stack-only blocks gas:"]
        print(f"- same stack-only blocks: original {o}, gasol (validated) {gg}, evmopt {ours}; "
              f"evmopt better on {ob}, gasol better on {gbt}")


if __name__ == "__main__":
    main()
