#!/usr/bin/env python3
"""Benchmark evmopt (and optionally gasol's outputs) on gasol's asm corpus; prints markdown.

Usage: scripts/benchmark.py [--gasol DIR] [--jobs N] [--only NAME...]
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
    """Stdout, wall seconds and peak RSS (MB) of one process, via /usr/bin/time."""
    r = subprocess.run(["/usr/bin/time", "-f", "TIME %e %M", *cmd],
                       capture_output=True, text=True, check=True)
    wall, kb = r.stderr.strip().splitlines()[-1].split()[1:]
    return r.stdout, float(wall), int(kb) // 1024


def gasol_log(log):
    if not log.exists():
        return None
    text = log.read_text(errors="replace")
    t = re.search(r"Total time: ([\d.]+)", text)
    gi = re.search(r"Estimated initial gas: (\d+)", text)
    go = re.search(r"Estimated gas optimized: (\d+)", text)
    return {
        "time": float(t.group(1)) if t else None,
        "saved": int(gi.group(1)) - int(go.group(1)) if gi and go else None,
    }


def bench_one(path, gasol_dir):
    name = path.stem
    out, wall, rss = run_timed([str(EVMOPT), "--fork", "cancun", "stats", str(path)])
    m = STATS.search(out)
    if m is None:
        raise RuntimeError(f"unexpected evmopt output for {name}: {out!r}")
    n, gb, ga, sb, sa = map(int, m.groups())
    row = {"name": name, "blocks": n, "time": wall, "rss": rss, "gas": (gb, ga), "bytes": (sb, sa)}
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
                row["cmp"] = cmp.splitlines()[-3:]
    return row


def sum_cmp(rows):
    """Aggregate gasolcmp's three summary lines over all contracts."""
    keys = {"blocks:": 8, "effect blocks:": 5, "stack-only blocks gas:": 5}
    tot = {k: [0] * n for k, n in keys.items()}
    for r in rows:
        for line in r.get("cmp", []):
            for k, n in keys.items():
                if line.startswith(k):
                    nums = list(map(int, NUM.findall(line)))[:n]
                    if len(nums) == n:
                        tot[k] = [a + b for a, b in zip(tot[k], nums)]
    return tot


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--gasol", type=Path)
    ap.add_argument("--jobs", type=int, default=os.cpu_count())
    ap.add_argument("--only", nargs="*")
    args = ap.parse_args()
    files = sorted(CORPUS.glob("*.json_solc"))
    if args.only:
        files = [f for f in files if any(f.stem.startswith(o) for o in args.only)]
    t0 = time.perf_counter()
    with cf.ThreadPoolExecutor(args.jobs) as ex:
        rows = sorted(ex.map(lambda f: bench_one(f, args.gasol), files), key=lambda r: r["name"])
    total_wall = time.perf_counter() - t0

    print("| contract | blocks | evmopt s | evmopt MB | gas saved | bytes saved | gasol s | gasol est. gas saved |")
    print("|---|---:|---:|---:|---:|---:|---:|---:|")
    for r in rows:
        g = r.get("gasol") or {}
        gt = f"{g['time']:.0f}" if g.get("time") is not None else ("fail/timeout" if args.gasol else "-")
        gs = str(g["saved"]) if g.get("saved") is not None else "-"
        print(f"| {r['name'][:10]} | {r['blocks']} | {r['time']:.1f} | {r['rss']} | "
              f"{r['gas'][0] - r['gas'][1]} | {r['bytes'][0] - r['bytes'][1]} | {gt} | {gs} |")
    gb = sum(r["gas"][0] for r in rows); ga = sum(r["gas"][1] for r in rows)
    sb = sum(r["bytes"][0] for r in rows); sa = sum(r["bytes"][1] for r in rows)
    gsaved = [r["gasol"]["saved"] for r in rows if r.get("gasol") and r["gasol"].get("saved") is not None]
    gtime = [r["gasol"]["time"] for r in rows if r.get("gasol") and r["gasol"].get("time") is not None]
    print()
    print(f"- contracts: {len(rows)}, blocks: {sum(r['blocks'] for r in rows)}")
    print(f"- evmopt: sum of per-contract wall times {sum(r['time'] for r in rows):.1f} s, "
          f"wall {total_wall:.1f} s with {args.jobs} jobs")
    print(f"- evmopt stack-op gas {gb} -> {ga} (saved {gb - ga}), bytes {sb} -> {sa} (saved {sb - sa})")
    if args.gasol:
        print(f"- gasol: {len(gtime)} finished, total {sum(gtime):.0f} s; "
              f"estimated gas saved {sum(gsaved)} over those contracts")
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
