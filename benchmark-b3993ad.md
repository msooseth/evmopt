# Benchmark at b3993ad

Corpus: `gasol-optimizer/examples/jsons-solc` (30 contracts, 26580 blocks). Machine: AMD Ryzen AI 9
HX 370, 12 cores. Lean 4.33.0. evmopt `--fork cancun`, 12 contracts in parallel. gasol: the
ff5efe78 run recorded in `bench/gasol-ff5efe78/` (`-solver z3`, 2 s/block, 8 in parallel).

Reproduce: `scripts/benchmark.py --gasol bench/gasol-ff5efe78/raw --jobs 12` (`raw/` is local,
see `bench/gasol-ff5efe78/README.md`).

## Summary

| | evmopt b3993ad | evmopt 55b306d | gasol |
|---|---:|---:|---:|
| contracts finished | 30 | 30 | 28 (2 fail/timeout) |
| total time, sum over contracts | 1593 s | 299 s | 12190 s |
| per-contract time, median / max | 53 s / 128 s | 10 s / 26 s | 466 s / 874 s |
| gas saved, the 28 gasol finished | 18237 | 9573 | 16279 (estimate) |
| gas saved, all 30 | 20085 | 10462 | – |
| bytes saved | 5591 | 2449 | – |

- evmopt's savings are all proven (`xcheck_sound_asm`, `optimizeX_sound`, `Checks.lean`).
- gasol's figure is its own estimate and includes rewrites that do not validate: 137
  stack-only and ~720 effect-block rewrites exceed the original stack peak (`gasol-bugs.md`
  H), and 165 effect-block rewrites change the effect sequence (beyond our checker; no
  counterexample on random frames).
- Same stack-only blocks: original 43328, gasol (validated) 41951, evmopt 41029; evmopt
  better on 125 blocks, gasol on 16.
- Changes since 55b306d: assembler constants (`PUSH [tag]` & co) as opaque atoms instead of
  barriers, scheduler fixes (dead-input pre-clean, last-use SWAP1/in-place commutative
  operands, interleaved effect emission, goal reservation, cheap-constant re-push), effect-
  ordered search, window superoptimisation, `DIV/MUL` by `2^k` rules.
- "stack-op gas" now includes the 3 gas of each tag push (tags are part of blocks), so the
  before/after totals are larger than at 55b306d; savings are comparable.
- Slower: per-contract time is 5x that of 55b306d (8 greedy variants, search on effect
  blocks, window search); still ~8x faster than gasol in total.

## Per contract

| contract | blocks | evmopt s | evmopt MB | gas saved | bytes saved | gasol s | gasol est. gas saved |
|---|---:|---:|---:|---:|---:|---:|---:|
| 0x08B02C0B | 888 | 64.7 | 128 | 586 | 142 | 444 | 491 |
| 0x0c9C2e96 | 1850 | 73.4 | 135 | 1082 | 242 | 838 | 1105 |
| 0x140A4455 | 788 | 33.1 | 111 | 479 | 127 | 374 | 473 |
| 0x15754A1c | 950 | 59.8 | 165 | 688 | 223 | 466 | 669 |
| 0x1E77fbE7 | 775 | 69.6 | 150 | 761 | 229 | 552 | 531 |
| 0x1d29Bafa | 895 | 87.4 | 165 | 951 | 239 | 659 | 645 |
| 0x1f2cF791 | 400 | 27.8 | 107 | 291 | 70 | 188 | 226 |
| 0x20e7Efc1 | 733 | 26.1 | 111 | 527 | 138 | 211 | 553 |
| 0x32E6C34C | 1245 | 81.3 | 162 | 745 | 200 | 624 | 765 |
| 0x351B9532 | 720 | 36.6 | 155 | 526 | 163 | 306 | 432 |
| 0x363c4219 | 278 | 19.5 | 130 | 131 | 28 | 97 | 133 |
| 0x3BfcE6D6 | 624 | 47.9 | 111 | 395 | 112 | 364 | 412 |
| 0x3E873439 | 469 | 24.0 | 111 | 364 | 82 | 169 | 413 |
| 0x444DBcb1 | 1020 | 60.1 | 120 | 697 | 219 | 317 | 743 |
| 0x4cEe28ED | 547 | 40.2 | 116 | 342 | 82 | fail/timeout | - |
| 0x5552F868 | 1607 | 128.4 | 172 | 1506 | 444 | fail/timeout | - |
| 0x6237CeA6 | 1007 | 53.4 | 166 | 715 | 232 | 484 | 678 |
| 0x62AB956D | 951 | 77.9 | 166 | 821 | 272 | 565 | 772 |
| 0x63B72a67 | 724 | 59.4 | 127 | 727 | 164 | 408 | 303 |
| 0x6488216d | 1028 | 42.9 | 113 | 866 | 174 | 496 | 759 |
| 0x6FD61714 | 734 | 51.9 | 112 | 480 | 127 | 374 | 410 |
| 0x7aa21657 | 5 | 0.5 | 85 | 1 | 0 | 0 | 1 |
| 0x7d657Cf5 | 980 | 71.0 | 166 | 812 | 262 | 536 | 741 |
| 0x81AFa8AC | 943 | 49.1 | 165 | 683 | 222 | 471 | 631 |
| 0x8551fe60 | 825 | 30.2 | 112 | 622 | 184 | 204 | 457 |
| 0x8C3c2547 | 967 | 68.9 | 145 | 983 | 331 | 874 | 746 |
| 0x8CFeA40E | 1326 | 62.1 | 129 | 1165 | 327 | 590 | 1155 |
| 0x8DBEaDAD | 1006 | 43.8 | 130 | 733 | 167 | 490 | 661 |
| 0x8f16c864 | 1343 | 62.6 | 134 | 718 | 166 | 626 | 722 |
| 0xC2bb2D28 | 952 | 39.1 | 165 | 688 | 223 | 465 | 652 |

```
- contracts: 30, blocks: 26580
- evmopt: sum of per-contract wall times 1592.9 s, wall 163.8 s with 12 jobs
- evmopt stack-op gas 342127 -> 322042 (saved 20085), bytes 225350 -> 219759 (saved 5591)
- gasol: 28 finished, total 12190 s; estimated gas saved 16279 over those contracts
- gasol stack-only rewrites: unchanged 12869, validated 1260 (14515 -> 13138 gas), rejected 137 (with counterexample 0), other blocks 8443, block-count mismatches 0
- gasol effect-block rewrites: 1717 blocks, unchanged 878, validated 674, wrong 0, effects changed without counterexample 165
- same stack-only blocks: original 43328, gasol (validated) 41951, evmopt 41029; evmopt better on 125, gasol better on 16
```
