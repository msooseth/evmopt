# Benchmark at 55b306d

Corpus: `gasol-optimizer/examples/jsons-solc` (30 contracts, 26580 blocks). Machine: AMD Ryzen AI 9
HX 370, 12 cores. Lean 4.33.0. evmopt `--fork cancun`, 12 contracts in parallel. gasol HEAD
ff5efe78, `-solver z3`, 2 s/block, 8 contracts in parallel, 50 min limit per contract.

Reproduce: run gasol per contract via `scripts/gasol_tmp.py <json> -solver z3` into
`DIR/<name>/` (log in `DIR/<name>/log.txt`), then `scripts/benchmark.py --gasol DIR --jobs 12`.

## Summary

| | evmopt | gasol |
|---|---:|---:|
| contracts finished | 30 | 28 (2 fail/timeout) |
| total time, sum over contracts | 299 s | 12190 s |
| per-contract time, median / max | 10.3 s / 25.9 s | 466 s / 874 s |
| gas saved, all 30 | 10462 | – |
| gas saved, the 28 gasol finished | 9573 | 16279 (estimate) |
| bytes saved | 2449 | – |

- evmopt "gas saved" counts stack-instruction gas; effect ops are kept unchanged, so this is the
  block's whole gas saving. Every rewrite is proven (checker + `Steps` theorems).
- gasol's figure is its own estimate and includes rewrites that are not validated: 137
  stack-only rewrites exceed the original stack peak (`gasol-bugs.md` H) and 206 effect-block
  rewrites change the effect sequence (beyond our checker; no counterexample found on random
  frames).
- On the stack-only blocks both tools handle: original 43328, gasol (validated rewrites only)
  41951, evmopt 41630; evmopt better on 57 blocks, gasol on 19.
- gasol's rewrites checked: stack-only 1260 validated, 137 rejected, 0 with counterexample;
  effect blocks 1717 (878 unchanged, 633 validated, 206 changed effects, 0 wrong).
- The gap in total savings is gasol's effect-changing rewrites (load forwarding, dead stores,
  reordering) and `PUSH [tag]`/SSTORE/TSTORE barriers on our side.
- `0x5552F868`: gasol's temp files passed 8.5 GB in 22 min (11 GB in an earlier run before the
  limit killed it); stopped. `0x4cEe28ED`: gasol exit 1.

## Per contract

| contract | blocks | evmopt s | evmopt MB | gas saved | bytes saved | gasol s | gasol est. gas saved |
|---|---:|---:|---:|---:|---:|---:|---:|
| 0x08B02C0B | 888 | 6.9 | 118 | 351 | 68 | 444 | 491 |
| 0x0c9C2e96 | 1850 | 11.4 | 126 | 530 | 108 | 838 | 1105 |
| 0x140A4455 | 788 | 10.6 | 103 | 285 | 59 | 374 | 473 |
| 0x15754A1c | 950 | 7.9 | 164 | 352 | 105 | 466 | 669 |
| 0x1E77fbE7 | 775 | 13.1 | 160 | 343 | 77 | 552 | 531 |
| 0x1d29Bafa | 895 | 14.0 | 148 | 572 | 104 | 659 | 645 |
| 0x1f2cF791 | 400 | 3.6 | 101 | 161 | 29 | 188 | 226 |
| 0x20e7Efc1 | 733 | 7.2 | 111 | 268 | 61 | 211 | 553 |
| 0x32E6C34C | 1245 | 13.1 | 123 | 440 | 98 | 624 | 765 |
| 0x351B9532 | 720 | 10.9 | 120 | 309 | 86 | 306 | 432 |
| 0x363c4219 | 278 | 3.4 | 122 | 47 | 11 | 97 | 133 |
| 0x3BfcE6D6 | 624 | 8.7 | 103 | 243 | 50 | 364 | 412 |
| 0x3E873439 | 469 | 5.0 | 110 | 145 | 13 | 169 | 413 |
| 0x444DBcb1 | 1020 | 5.4 | 112 | 308 | 106 | 317 | 743 |
| 0x4cEe28ED | 547 | 8.0 | 98 | 178 | 43 | fail/timeout | - |
| 0x5552F868 | 1607 | 25.9 | 188 | 711 | 118 | fail/timeout | - |
| 0x6237CeA6 | 1007 | 9.0 | 164 | 358 | 105 | 484 | 678 |
| 0x62AB956D | 951 | 15.9 | 165 | 430 | 133 | 565 | 772 |
| 0x63B72a67 | 724 | 15.1 | 127 | 381 | 55 | 408 | 303 |
| 0x6488216d | 1028 | 11.8 | 103 | 460 | 60 | 496 | 759 |
| 0x6FD61714 | 734 | 10.3 | 103 | 281 | 58 | 374 | 410 |
| 0x7aa21657 | 5 | 0.0 | 67 | 1 | 0 | 0 | 1 |
| 0x7d657Cf5 | 980 | 7.9 | 165 | 380 | 111 | 536 | 741 |
| 0x81AFa8AC | 943 | 13.4 | 165 | 350 | 105 | 471 | 631 |
| 0x8551fe60 | 825 | 5.4 | 110 | 298 | 90 | 204 | 457 |
| 0x8C3c2547 | 967 | 9.3 | 133 | 594 | 200 | 874 | 746 |
| 0x8CFeA40E | 1326 | 12.1 | 113 | 638 | 139 | 590 | 1155 |
| 0x8DBEaDAD | 1006 | 12.8 | 120 | 360 | 71 | 490 | 661 |
| 0x8f16c864 | 1343 | 12.0 | 121 | 336 | 81 | 626 | 722 |
| 0xC2bb2D28 | 952 | 8.3 | 165 | 352 | 105 | 465 | 652 |

```
- contracts: 30, blocks: 26580
- evmopt: sum of per-contract wall times 298.5 s, wall 36.1 s with 12 jobs
- evmopt stack-op gas 288034 -> 277572 (saved 10462), bytes 171257 -> 168808 (saved 2449)
- gasol: 28 finished, total 12190 s; estimated gas saved 16279 over those contracts
- gasol stack-only rewrites: unchanged 12869, validated 1260 (14515 -> 13138 gas), rejected 137 (with counterexample 0), other blocks 8443, block-count mismatches 0
- gasol effect-block rewrites: 1717 blocks, unchanged 878, validated 633, wrong 0, effects changed without counterexample 206
- same stack-only blocks: original 43328, gasol (validated) 41951, evmopt 41630; evmopt better on 57, gasol better on 19
```
