# M2 census: replications, extensions, piece census, C0 at m = 10

Lane M2, 2026-10-04/05 EDT. Machine: 18 cores (aarch64 macOS 25.6). Times are one core unless
stated. "core-s" is user CPU time. A count from geng_q4 / genbg_q4 is "graphs with no 4-regular
subgraph"; plain geng / genbg counts are whole classes, split by the SAT decider into SAT (has one)
and UNSAT (has none).

Binaries (SHA-256; full table and build commands in `BUILD.md`):

| Name | Path | SHA-256 |
|---|---|---|
| geng_q4 | `reports/585-fable-wildcard/lanes/quartic-subgraph/geng_q4` (nauty 2.8.9 geng + q4 PRUNE) | `8b4d5783...ea0f0656` |
| genbg_q4 | same folder (nauty 2.8.9 genbg + q4 PRUNE1) | `a29067ac...bd84404c` |
| geng 2.9.3 | `~/.cache/erdos585/nauty2_9_3/geng` (plain) | `588052a8...7fdaca1` |
| genbg 2.9.3 | `~/.cache/erdos585/nauty2_9_3/genbg` (plain) | `502f5f46...4ef957` |
| validate_sat.py | quartic-subgraph folder (pysat CaDiCaL 1.5.3, witness-checked SAT answers) | `a6535d81...0ff4a21` |
| sat_all.py | `census/sat_all.py` (imports validate_sat's `has_q4` and `check_witness` unchanged; writes UNSAT graphs out) | `b4bf00d7...7625d6c` |
| pairc | `reports/585-fable/tools/pairc` (pair test; one control only) | `a8a4af8e...6c611366` |

Python: `[temporary path]`.

## Summary

No run in an F1, F2, C0, X-type or Q-type class produced a graph without a 4-regular subgraph.
The only 4-regular-free graphs seen were controls below the thresholds; all 48,231 of them are
saved and were re-decided by `validate_sat.py --expect-unsat` (all UNSAT, exit 0):
`f1/q4free_bip_n11_all.g6` (3), `f1/q4free_bip_n12_all.g6` (4), `f1/q4free_bip_n13_e28-31.g6` (124),
`logs/selftest/found.g6` (290, n = 14, e = 30..33), `f1/q4free_bip_n15_e33-45.g6` (23094),
`f1/q4free_bg_7x7_d4.g6` (485) and `f1/q4free_bg_7x8_d4.g6` (24231).

| Job | Result | Status |
|---|---|---|
| 1. F2 n = 13..18 with geng_q4 | 0 graphs for every n ≤ 17; n = 18 pilot shards 0 | replicated n ≤ 17; n = 18 replicated by genbg_q4 (0, 57 s), geng_q4 run in `run_f2_n18.sh` |
| 2. F1 n = 14, plain geng 2.9.3 + SAT | 1798 graphs, all have a 4-regular subgraph | replicated (independent generator and decider); also n ≤ 13 |
| 3. F1 n = 15, 16 | 0 graphs (geng_q4) and all 13330 / 515389 plain-geng graphs SAT | extended, two methods each |
| 3. F1 n = 17 | 0 graphs (genbg_q4, sides 8 + 9) | extended, one method |
| 3. F1 n = 18 | sides 8 + 10: 0; sides 9 + 9, e ≥ 50: 0; sides 9 + 9, e = 48, 49: pilots 0 | projected ~0.2 core-h, `run_f1_n18.sh` |
| 3. F2 n = 19 | 0 graphs (genbg_q4, sides 9 + 10, 83 s) | extended, one method; geng_q4 in `run_f2_n19.sh` |
| 3. F2 n = 20 | pilots 0 | projected ~11 core-h (genbg_q4), `run_f2_n20.sh` |
| 4. X-type c = 7, 8 | 0 graphs (c = 7 also by plain genbg + SAT: 17044 graphs all SAT) | run |
| 4. X-type c = 9 | pilots 0 | projected ~0.6-0.75 core-h, `run_xtype_c9.sh` |
| 4. Q-type (9, 10, e = 53) | 0 graphs (111.7 s) | run, one method |
| 5. C0 m = 10 | pilots 0 | projected ~0.75 core-h (swapped class order, -X-2), `run_c0_m10.sh` |
| 5. C0 m = 8, independent | plain genbg 2.9.3 + SAT: 18963 graphs, all SAT | replicated (independent) |
| 5. C0 m = 9 | genbg_q4 swapped order: 0 (3.4-5.3 s); plain genbg class has 12,576,934 graphs | re-run by a second order; independent run projected ~1 core-h, `run_c0_m9_indep.sh` |

## Launch scripts for the lead

All run 12 shards at a time under `nohup nice -n 15` (they detach themselves), log each shard to
`logs/<tag>/shard_<r>.{g6,err}`, skip finished shards on restart, and end by calling
`sum_shards.sh`, which checks every shard finished, sums counts and CPU, and re-decides any output
graph with `validate_sat.py --expect-unsat`. Template tested end to end by `run_selftest.sh`.

| Script | Command | Shards | Projected | Wall on 12 cores | Expected |
|---|---|---|---|---|---|
| `run_c0_m10.sh` (+ `sum_c0_m10.sh`) | `genbg_q4 -X-2 -d0:6 -D6:6 11 10 r/200` | 200 | ~2,700 core-s (0.75 core-h) | ~4-6 min | 0 graphs |
| `run_c0_m9_indep.sh` (own `sum` mode) | plain `genbg -X-2 -d0:6 -D6:6 10 9 r/48` piped to `sat_all.py` | 48 | ~3,200-4,500 core-s (0.9-1.25 core-h) | ~6-8 min | 12,576,934 graphs generated, all SAT, UNSAT 0 |
| `run_xtype_c9.sh` | `genbg_q4 -d2:6 -D6:6 11 9 r/24` | 24 | ~2,000-2,700 core-s | ~5 min | unknown (c = 7, 8 gave 0); copies output to `pieces/xtype_c9.g6` |
| `run_f1_n18.sh` | `genbg_q4 -X-2 -d4:4 -D6:6 9 9 48:49 r/24` (last piece of F1 at n = 18) | 24 | ~700 core-s (0.2 core-h) | ~2 min | 0 graphs |
| `run_f2_n18.sh` | `geng_q4 -b -d4 -D6 18 50:54 r/40` | 40 | ~340 core-s | ~1 min | 0 graphs |
| `run_f2_n19.sh` | `geng_q4 -b -d4 -D6 19 53:57 r/400` | 400 | ~13,000 core-s (3.6 core-h) | ~20 min | 0 graphs |
| `run_f2_n20.sh` | `genbg_q4 -X-2 -d4:4 -D6:6 10 10 56:60 r/200` | 200 | ~40,000 core-s (11 core-h) | ~55-60 min | 0 graphs |

Timing caveat: the machine ran other projects' builds during this lane (load average 4 at the
start, 13-30 from 23:46 on), and Apple silicon mixes performance and efficiency cores, so CPU
times are good to about a factor of 2. Counts are exact.

## Job 1. F2 replication with geng_q4 (different generator and decider from geng + pairc)

F2(n): bipartite, δ ≥ 4, Δ ≤ 6, e ≥ 3n − 4 ⇒ 4-regular subgraph.

Controls (all passed):
- geng_q4 reproduces the REPORT bipartite counts: n = 11 all e → 3, n = 12 all e → 4,
  n = 13 all e → 124 (28 + 50 + 37 + 9), `geng_q4 -b -d4 -D6 14 30:42` → 290 (94 + 108 + 77 + 11).
- res/mod split: `geng_q4 -b -d4 -D6 -u 13 28:31 r/8` shards sum to 124 (= unsplit);
  `... 14 30:42 r/16` shards sum to 290 (= unsplit). The 290 graphs were re-decided by
  validate_sat.py: 290 UNSAT (logs/selftest, which also tested the launch-script template).

| n | Command | Graphs | CPU | Status |
|---|---|---|---|---|
| 8-12 | `geng_q4 -b -d4 -D6 -u n (3n-4):(3n)` | 0 each | < 0.01 s each | replicated |
| 13 | `geng_q4 -b -d4 -D6 -u 13 35:39` | 0 | 0.00 s | replicated |
| 14 | `geng_q4 -b -d4 -D6 -u 14 38:42` | 0 | 0.01 s | replicated |
| 15 | `geng_q4 -b -d4 -D6 -u 15 41:45` | 0 | 0.08 s | replicated |
| 16 | `geng_q4 -b -d4 -D6 -u 16 44:48` | 0 | 0.92 s | replicated |
| 17 | `geng_q4 -b -d4 -D6 -u 17 47:51` | 0 | 15.94 s | replicated |
| 18 | `geng_q4 -b -d4 -D6 -u 18 50:54` | pilot: shards 0, 13, 26, 39 of 40 → 0 each | 6.7-9.7 s per shard; projected ~340 core-s | projected; `run_f2_n18.sh` |

Second generator, genbg_q4. If e ≥ 3n − 4 and Δ ≤ 6 then each side has at least ⌈(3n − 4)/6⌉
vertices, which fixes the sides: n = 17 → 8 + 9 (e ≤ 48), n = 18 → 9 + 9, n = 19 → 9 + 10
(e ≤ 54), n = 20 → 10 + 10.

| n | Command | Graphs | CPU | Status |
|---|---|---|---|---|
| 17 | `genbg_q4 -u -d4:4 -D6:6 8 9 47:51` and `... 9 8 47:51` | 0, 0 | 3.41 s, 0.17 s | replicated |
| 18 | `genbg_q4 -u -d4:4 -D6:6 9 9 50:54` | 0 | 56.96 s | replicated (second method for n = 18) |
| 19 | `genbg_q4 -u -d4:4 -D6:6 10 9 53:54` | 0 | 82.59 s | extended (one method); see Job 3 |

Verdict: F2 replicated for n ≤ 17 by geng_q4 and for n = 17, 18 by genbg_q4. The geng_q4 run at
n = 18 (~6 core-min) is over the 4 core-min cap and is in `run_f2_n18.sh`. geng_q4 and genbg_q4
share the q4core.h decider; the original F2 used plain geng 2.9.3 + pairc, so each n ≤ 18 now
has two methods with different generators and different deciders.

## Job 2. F1 replication at n = 14 with an independent decider

F1(n): bipartite, δ ≥ 4, Δ ≤ 6, e ≥ 3n − 6 ⇒ 4-regular subgraph. Generator: plain nauty 2.9.3
geng (not the 2.8.9 tree behind geng_q4). Decider: validate_sat.py (pysat CaDiCaL; no q4core.h);
every SAT answer is a witness subgraph checked to be nonempty, 4-regular and inside the graph.

| n | Command | Graphs (total) | SAT (has one) | UNSAT | CPU |
|---|---|---|---|---|---|
| 14 | `geng -b -d4 -D6 14 36:42 f1/f1_n14_e36-42.g6` then `validate_sat.py` | 1798 | 1798 | 0 | geng 0.04 s, SAT 0.31 s |
| 6-13 | `geng -q -b -d4 -D6 n (3n-6):(3n)` then `validate_sat.py` | 0, 0, 0, 0, 3, 6, 41, 98 | all | 0 | < 1 s |
| 14, e = 34:35 | `geng -q -b -d4 -D6 14 34:35` then `validate_sat.py` | 5443 | 5443 | 0 | 0.73 s |

`f1/f1_n14_e36-42.g6` SHA-256 `099fa20c91c2b472baed81bf82e4b47075d3097795e79c6d7c43f6f85b4fde05`.
The graph files for n = 6..13 are in `f1/`.

Verdict: replicated. F1 holds for n ≤ 14 by a second, independent method (different nauty version
and a SAT decider). The extra e = 34, 35 run agrees with geng_q4's maximum of e = 33 = 3n − 9 at
n = 14 (no 4-regular-free graph at 3n − 8 or 3n − 7).

## Job 3. Extensions: F1 at n = 15, 16 (and 17, 18); F2 at n = 19, 20

| Fact, n | Command | Graphs | CPU | Status |
|---|---|---|---|---|
| F1, 15 | `geng_q4 -b -d4 -D6 -u 15 39:45` | 0 | 0.34 s | extended |
| F1, 15 | plain `geng -q -b -d4 -D6 15 39:45` (13330 graphs) then `validate_sat.py` | 13330 SAT, 0 UNSAT | 4.1 s | extended, second method |
| F1, 15 (max e) | `geng_q4 -b -d4 -D6 -u -v 15 33:45` | 23094: e = 33: 5440, 34: 9932, 35: 6289, 36: 1396, 37: 37 | 2.6 s | max e = 37 = 3n − 8 |
| F1, 16 | `geng_q4 -b -d4 -D6 -u 16 42:48` | 0 | 4.9 s | extended |
| F1, 16 | plain `geng -q -b -d4 -D6 16 42:48` (515389 graphs, SHA-256 `729dff74...b2a794`) then `validate_sat.py` in 4 parts | 515389 SAT, 0 UNSAT | 0 + 181 s | extended, second method |
| F1, 16 (max e) | `geng_q4 -b -d4 -D6 -u -v 16 40:41` | 0 | 17.3 s | max e ≤ 39 = 3n − 9 |
| F1, 17 | `genbg_q4 -u -d4:4 -D6:6 9 8 45:48` (sides forced 8 + 9: e ≥ 45 > 6·7) | 0 | 11.3 s | extended (one method) |
| F1, 18, sides 8 + 10 | `genbg_q4 -u -d4:4 -D6:6 10 8 48:48` | 0 | 2.6 s | part of n = 18 |
| F1, 18, sides 9 + 9, e ≥ 50 | `genbg_q4 -u -d4:4 -D6:6 9 9 50:54` (the F2 run) | 0 | 57 s | part of n = 18 |
| F1, 18, sides 9 + 9, e = 48, 49 | `genbg_q4 -u -d4:4 -D6:6 9 9 48:49` | unsplit hit the 240 s cap (220 s CPU); -X-2 shards 0, 100 of 200 → 0 (5.9, 4.9 s), 7 of 20 → 0 (35.2 s) | fit P ≈ 2.1 s, W ≈ 660 s: projected ~700 core-s | projected; `run_f1_n18.sh` |
| F2, 19 | `genbg_q4 -u -d4:4 -D6:6 10 9 53:54` (sides forced 9 + 10) | 0 | 82.6 s | extended (one method) |
| F2, 19 | `geng_q4 -b -d4 -D6 -u 19 53:57` | pilot: shards 0, 133, 266 of 400 → 0 each | 30.4, 33.8, 33.1 s per shard; projected ~13,000 core-s (3.6 core-h) | projected; `run_f2_n19.sh` |
| F2, 20 | `geng_q4 -b -d4 -D6 -u 20 56:60` | pilot: shards 0, 3333, 6666 of 10000 → 0 each | 49.5, 45.8, 42.3 s per shard; projected ~4.6e5 core-s (~127 core-h) | projected only, no script |
| F2, 20 | `genbg_q4 -u -d4:4 -D6:6 10 10 56:60` (sides forced 10 + 10), default split | shards 0, 33, 66 of 100 hit the 240 s cap | prefix-dominated | not usable for projection |
| F2, 20 | `genbg_q4 -u -X-2 -d4:4 -D6:6 10 10 56:60 r/M` | pilot: 0/2000, 1000/2000 → 0; 77/200 → 0 | 27.2, 28.1 s; 199.1 s. Fit t = P + W/M: P ≈ 8.6 s, W ≈ 38,100 s; projected ~40,000 core-s (~11 core-h) with M = 200 | projected; `run_f2_n20.sh` |

Side-size argument for the genbg rows: Δ ≤ 6 gives e ≤ 6·|side| for both sides of any
bipartition, so both sides have at least ⌈e/6⌉ vertices. `genbg_q4 n1 n2` lists every
bicoloured graph with first class of size n1 and second of size n2 (up to color-preserving
isomorphism) that passes the flags, so running every allowed pair of side sizes, in either order,
covers the class. F1 at n = 17 (e ≥ 45): (8, 9). F1 at n = 18 (e ≥ 48): (8, 10) with e = 48, or
(9, 9). F2 at n = 19 (e ≥ 53): (9, 10). F2 at n = 20 (e ≥ 56): (10, 10).

## Job 4. Piece census (outputs in `pieces/`)

genbg syntax (from its help text): `genbg [-d#:#] [-D#:#] n1 n2 [mine[:maxe]] [res/mod] [file]`;
`-dA:B` / `-DA:B` give the min / max degree of the first and second class. In the output graph6
the first class is vertices 0..n1−1.

| Piece | Command | Graphs | CPU | Status |
|---|---|---|---|---|
| X, c = 7 | `genbg_q4 -d2:6 -D6:6 9 7 pieces/xtype_c7.g6` | 0 (file empty) | 0.02 s | run |
| X, c = 7, cross-check | plain `genbg -q -d2:6 -D6:6 9 7` (17044 graphs) then `validate_sat.py` | 17044 SAT, 0 UNSAT | 0.06 + 3.2 s | replicated (independent) |
| X, c = 8 | `genbg_q4 -d2:6 -D6:6 10 8 pieces/xtype_c8.g6` | 0 (file empty) | 3.4 s | run (one method) |
| X, c = 9 | `genbg_q4 -d2:6 -D6:6 11 9` | pilot: shards 0/2000 5.3 s, 0/200 13.7 s, 5/20 124.5 s, 0 graphs | projected 2,000-2,700 core-s | projected; `run_xtype_c9.sh` |
| Q (C1), sides 9, 10, e = 53 | `genbg_q4 -d3:5 -D6:6 10 9 53:53 pieces/qtype_10x9_e53.g6` | 0 (file empty) | 111.7 s | run (one method) |

Notes:
- Class order. For X-type the given order (c+2 first) is the fast one: the reverse
  `genbg_q4 -u -d6:2 -D6:6 8 10` took 54 s against 3.4 s. For Q-type the stated command
  `genbg_q4 -d5:3 -D6:6 9 10 53:53` is slow (its mod-100 shards took 171 s each, prefix-dominated),
  so I ran the same class with the 10-side first. Both orders list the same bicoloured graphs up
  to color-preserving isomorphism; on a nonzero control (`-d4:4 -D6:6 7 8` vs `8 7`) both give 24231.
- Uncapped plain `genbg -d2:6 -D6:6 10 8` has 8,131,539 graphs (29 s), too many for the Python SAT
  decider inside the cap, so X c = 8 has one method.
- Q-type and F2 at n = 19 overlap: a 9 + 10 graph with e = 53 and δ ≥ 4 is a Q-type graph, and
  with e = 54 it is a C0 m = 9 graph. Both runs give 0, consistent with the direct F2(19) run.

## Job 5. C0 at m = 10 (projected; launch script ready)

C0(m): bipartite, sides m and m + 1, the m-side all degree 6, Δ ≤ 6, no 4-regular subgraph.

| Run | Command | Result | CPU | Status |
|---|---|---|---|---|
| m = 8, planned order | `genbg_q4 -u -d6:0 -D6:6 8 9` | 0 | 0.33 s | re-run |
| m = 8, swapped order | `genbg_q4 -u -d0:6 -D6:6 9 8` | 0 | 0.02 s | re-run |
| m = 9, swapped order | `genbg_q4 -u -d0:6 -D6:6 10 9` | 0 | 5.3 s, re-timed 3.4 s | replicated C0-9 by a second generation order (same binary) |
| m = 10, planned order, pilot | `genbg_q4 -u -d6:0 -D6:6 10 11 r/2000`, r = 0, 667, 1334 | each hit the 240 s timeout | > 240 s per shard | projected ~25-40x the swapped order: ~18-29 core-h |
| m = 10, swapped order, pilot | `genbg_q4 -u -d0:6 -D6:6 11 10 r/2000`, r = 0, 667, 1334 | 0 each | 140.3 s each | prefix-dominated |
| m = 10, swapped, -X-1 | `... -X-1 ... r/2000`, r = 0, 500, 1000, 1500 | 0 each | 3.5 s each | |
| m = 10, swapped, -X-2 | `... -X-2 ... r/2000`, r = 0, 1000 | 0 each | 0.95, 0.83 s | |
| m = 10, swapped, -X-2 | `genbg_q4 -u -X-2 -d0:6 -D6:6 11 10 r/20`, r = 0, 7, 14 | 0 each | 131.3, 132.9, 132.4 s | basis of the projection |

Why the split level matters: genbg splits at level maxn2 − 2 (genbg.c 1692-1701), so every
shard regenerates the tree down to that level. For the swapped order the level-8 expansion costs
about 136 s and the default split repeats it in each shard. `-X-2` moves the split to level 6.
Fitting t = P + W/mod to the -X-2 shard times gives W ≈ 2,650 s and P ≈ 0, so the whole run is
about 2,700 core-s (0.75 core-h), consistent with the -X-1 and default-split times
(3.5 s ≈ 2.6 + 2,650/2000; 140 s ≈ 138.6 + 2,510/2000).

Launch script: `run_c0_m10.sh` (swapped order, `-X-2`, 200 shards of ~13 s, 12 at a time under
`nohup nice -n 15`, logs in `logs/c0_m10/`), summed by `sum_c0_m10.sh`. Projection ~2,700 core-s,
about 4-6 minutes of wall time on 12 cores. Expected output 0 graphs; any output is a
4-regular-free C0 member at m = 10 and is re-decided by `validate_sat.py --expect-unsat`.
Controls for the scripted shape: the class-order equivalence (24231 = 24231 on `7 8` / `8 7`),
the -X split sums (485 and 24231), and the `-X-2 ... r/20 FILE` shape (24231 lines in 20 files).

Independent replication of C0 at m ≤ 9 (STATE.md asks for C0-9 to be replicated here). The class
order and split checks above use the same binary, so they do not replicate C0-9 independently.
Independent method: plain nauty 2.9.3 genbg lists the whole C0 class (no pruning) and
`sat_all.py` decides each graph with validate_sat.py's SAT encoding, imported unchanged; every SAT
answer is a checked witness, and UNSAT graphs are written to a file.

| Run | Command | Graphs | Result | CPU | Status |
|---|---|---|---|---|---|
| m = 8 | `genbg -X-1 -d0:6 -D6:6 9 8 r/4` piped to `sat_all.py` (`run_c0_m8_indep_selftest.sh`) | 18963 (= unsplit count) | SAT 18963, UNSAT 0 | 4.2 s | replicated (independent) |
| m = 8 | pairc on the same 18963 graphs | 18963 | all have a pair | 6.5 s | third method |
| m = 9 | plain `genbg -u -d0:6 -D6:6 10 9` | 12,576,934 | count only | 73 s | class size |
| m = 9 | `genbg -X-2 -d0:6 -D6:6 10 9 r/48` piped to `sat_all.py` | pilot: shards 0, 24 have 228,026 and 350,101 graphs | | 1.1, 1.6 s generation | projected ~1 core-h; `run_c0_m9_indep.sh` |

`sat_all.py` controls: on the 290 known 4-regular-free n = 14 graphs it reports UNSAT 290 and
writes all 290; on the C0 m = 8 file it reports SAT 18963.

## Lead addendum (2026-10-05 ~01:10 EDT): F2 at n = 21, projected only

With Δ ≤ 6 and e ≥ 3·21 − 4 = 59, both sides have ≥ 10 vertices, so the sides are 10 + 11 and
e ∈ {59, 60}. e = 60 is exactly the C0 class at m = 10 (done: 0 graphs, `logs/c0_m10/`). e = 59 is the
C1 shape at m' = 10 with δ ≥ 4: `genbg_q4 -u -X-2 -d4:5 -D6:6 11 10 59:59 r/M`.

| Pilot shard | Result | user CPU |
|---|---|---|
| 0/2000 | 0 graphs | 27.5 s |
| 1000/2000 | 0 graphs | 25.1 s |
| 3/600 | 0 graphs | 91.6 s |
| 301/600 | 0 graphs | 91.4 s |
| 7/200 | timed out at 240 s | 237 s |

Fit t = P + W/M: W ≈ 56,000 core-s (≈ 15.5 core-h), P ≈ 0. Not launched: it would raise the C0 bound
from m ≤ 65 (with F2(20)) to m ≤ 68, which is not worth 15.5 core-h this session. Listed as a decision
for Robert. Logs: `logs/pilot_c1_m10/`.
