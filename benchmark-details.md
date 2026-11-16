# Benchmark details

The 28 contracts of `gasol-optimizer/examples/jsons-solc` that gasol finishes (24426 blocks).
evmopt at 9ca37f4, `--fork cancun`, 12 in parallel; gasol ff5efe78 (`bench/gasol-ff5efe78/`),
`-solver z3`, 2 s/block, 8 in parallel. AMD Ryzen AI 9 HX 370, Lean 4.33.0. Gas and bytes
are measured by evmopt; gasol's are its validated rewrites only. Reproduce: `HOWTO-compare.md`.

| contract | blocks | evmopt s | gasol s | evmopt gas saved | gasol gas saved | evmopt bytes saved | gasol bytes saved | evmopt better |
|---|---:|---:|---:|---:|---:|---:|---:|---|
| 0x08B02C0B | 888 | 63.8 | 444 | 586 | 378 | 142 | 126 | both |
| 0x0c9C2e96 | 1850 | 101.5 | 838 | 1082 | 874 | 242 | 310 | gas |
| 0x140A4455 | 788 | 54.6 | 374 | 479 | 321 | 127 | 106 | both |
| 0x15754A1c | 950 | 77.7 | 466 | 688 | 491 | 223 | 168 | both |
| 0x1E77fbE7 | 775 | 41.6 | 552 | 761 | 352 | 229 | 118 | both |
| 0x1d29Bafa | 895 | 75.4 | 659 | 951 | 394 | 239 | 134 | both |
| 0x1f2cF791 | 400 | 16.8 | 188 | 291 | 177 | 70 | 58 | both |
| 0x20e7Efc1 | 733 | 41.7 | 211 | 527 | 428 | 138 | 170 | gas |
| 0x32E6C34C | 1245 | 76.3 | 624 | 745 | 531 | 200 | 185 | both |
| 0x351B9532 | 720 | 36.6 | 306 | 526 | 327 | 163 | 118 | both |
| 0x363c4219 | 278 | 12.2 | 97 | 131 | 114 | 28 | 36 | gas |
| 0x3BfcE6D6 | 624 | 49.4 | 364 | 395 | 308 | 112 | 110 | both |
| 0x3E873439 | 469 | 18.4 | 169 | 364 | 311 | 82 | 107 | gas |
| 0x444DBcb1 | 1020 | 36.6 | 317 | 697 | 582 | 219 | 209 | both |
| 0x6237CeA6 | 1007 | 59.0 | 484 | 715 | 515 | 232 | 172 | both |
| 0x62AB956D | 951 | 54.3 | 565 | 821 | 549 | 272 | 181 | both |
| 0x63B72a67 | 724 | 60.2 | 408 | 727 | 287 | 164 | 85 | both |
| 0x6488216d | 1028 | 67.9 | 496 | 866 | 605 | 174 | 217 | gas |
| 0x6FD61714 | 734 | 40.5 | 374 | 480 | 317 | 127 | 104 | both |
| 0x7aa21657 | 5 | 0.5 | 0 | 1 | 1 | 0 | 0 | - |
| 0x7d657Cf5 | 980 | 62.1 | 536 | 812 | 557 | 262 | 184 | both |
| 0x81AFa8AC | 943 | 71.6 | 471 | 683 | 489 | 222 | 163 | both |
| 0x8551fe60 | 825 | 39.6 | 204 | 622 | 368 | 184 | 130 | both |
| 0x8C3c2547 | 967 | 65.2 | 874 | 983 | 481 | 331 | 157 | both |
| 0x8CFeA40E | 1326 | 59.7 | 590 | 1165 | 773 | 327 | 261 | both |
| 0x8DBEaDAD | 1006 | 59.4 | 490 | 733 | 515 | 167 | 177 | gas |
| 0x8f16c864 | 1343 | 53.4 | 626 | 718 | 548 | 166 | 203 | gas |
| 0xC2bb2D28 | 952 | 37.3 | 465 | 688 | 497 | 223 | 167 | both |

- contracts: 28, blocks: 24426
- evmopt: sum of per-contract wall times 1433.3 s, wall 149.9 s with 12 jobs
- evmopt stack-op gas 310399 -> 292162 (saved 18237), bytes 203444 -> 198379 (saved 5065)
- gasol: 28 finished, total 12190 s
- on the 28 gasol finished, gas / bytes saved: evmopt 18237 / 5065, gasol validated 12090 / 4156, gasol unvalidated 16075 / 5510
- gasol stack-only rewrites: unchanged 12869, validated 1260 (14515 -> 13138 gas), rejected 137 (with counterexample 0), other blocks 8443, block-count mismatches 0
- gasol effect-block rewrites: 1717 blocks, unchanged 878, validated 674, wrong 0, effects changed without counterexample 165
- same stack-only blocks: original 43328, gasol (validated) 41951, evmopt 41029; evmopt better on 125, gasol better on 16
