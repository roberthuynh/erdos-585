# 5-regular graphs on 16 vertices: second-method checks (reg5b)

Lane `reports/585-next/wave8/reg5b/`, 2026-10-06. Rung (b), computed, not reviewed. A pair is two
edge-disjoint cycles on the same vertex set. This lane checks the reg5n16 lane (method 1,
`reports/585-next/wave6/reg5n16/`) with code written here that shares nothing with `reg5n16/code`,
`pairc` or the B-1 tools. Method 1 and B-1 files were only read, as data, for the comparisons named
below.

## Verdicts

| Check | Graphs decided | Count | Pair-free | Coverage |
|---|---|---|---|---|
| 1 | triangle-free 5-regular, n = 16 (`geng -t -d5 -D5 16`) | 388 | 0 | complete |
| 1 | bipartite 5-regular, n = 16 (`geng -b -d5 -D5 16`; `genbg -d5 -D5 8 8` as a second generator) | 41 | 0 | complete |
| 2 | every 5-regular graph, n = 6, 8, 10, 12, 14 (plain `geng -d5 -D5 n`) | 1; 3; 60; 7,849; 3,459,386 | 0 | complete |
| 3 | plain `geng -d5 -D5 16 r/20000`, 28 random shards | 3,612,814 | 0 | 28 of 20,000 shards (0.14%) |

Every graph in checks 1 to 3 got a pair from the SAT decider, and every pair was verified against the
graph by a separate check (`verify_pair`, below). These verdicts therefore do not depend on the SAT
encoding being complete. They depend on the generator output and on that check. No pair-free graph
was found, so there is nothing to certify or freeze (no `FROZEN.sha256`).

## Method

- **Generators.** Stock nauty 2.9.3 binaries in `~/.cache/erdos585/nauty2_9_3/`, built Oct 4 before
  method 1 (SHA-256: geng `588052a8…49fdaca1`, genbg `502f5f46…5f4ef957`, labelg
  `ae8b1e7e…441274a0`; full hashes in `logs/env.txt`). They are unpruned: `geng -d5 -D5 12` gives
  7,849 graphs and n = 14 gives 3,459,386, the B-1 R1 counts. Method 1 ran its own hooked build
  (`reg5n16/code/geng_pp`), not these binaries.
- **Decider, `code/pairsat.py`.** One CNF per vertex count n over all n(n-1)/2 vertex pairs, solved by
  MiniSat 2.2 through PySAT 1.9.dev15 (`m22`). A graph enters only as assumptions `-g[p]` on its
  non-edges, so one solver instance decides a whole shard (learned clauses follow from the CNF alone,
  not from the assumptions, so reuse across graphs is sound). Variables: `x[v]` (v in S), `a[p]`, `b[p]`
  (pair p is an edge of cycle A, of cycle B), a root `r[v]` forced to be the least vertex of S, and
  reachability levels along A and along B. Clauses: a- and b-edges are edges of G with both ends in S;
  no edge is in both; every v in S has exactly two a-edges and two b-edges (at most two by excluding
  every triple, at least two by n-1 clauses); every v in S is reached from the root within ⌊n/2⌋
  steps along A, and along B. Sound: A is 2-regular on S and connected, so it is one cycle through S;
  the same for B. Complete: from any pair take root = min S and the true distances along each cycle,
  which are at most ⌊|S|/2⌋.
- **Checker, `verify_pair` in `code/pairsat.py`.** Each model becomes two vertex sequences. The checker
  requires: each has at least 3 distinct vertices, every consecutive pair and the closing pair is an
  edge of G, the two vertex sets are equal, and the two edge sets are disjoint. G is the graph as
  decoded by networkx 3.6.1. The decider's own graph6 decoder is compared with networkx's on every
  graph, and in checks 1 to 3 every vertex degree is checked to be 5 (0 mismatches in all runs).
  `code/recheck_certs.py` re-checks saved certificates with a second checker (`brute.check_witness`).
- **Second encoding, `code/pairsat_cuts.py`.** A fresh CNF per graph over its own edges, CaDiCaL 1.9.5,
  connectivity by cut clauses added lazily ("S meets T and V-T implies A and B cross the cut of T")
  instead of reachability. Used for cross-checks.
- **Exhaustive search, `code/brute.py`.** For every vertex set S such that G[S] has at least 2|S|
  edges, list every Hamilton cycle of G[S] and look for two edge-disjoint ones. Used for calibration.

## Calibration of the decider, both answers

The checks below exercise the NOPAIR answer too, which checks 1 to 3 never needed.

- **Every graph on 3 to 8 vertices** (4, 11, 34, 156, 1,044, 12,346 graphs): `pairsat.py` and
  `brute.py` give the same verdict on each graph. At n = 8: 1,834 PAIR, 10,512 NOPAIR.
- **The B-1 Δ ≤ 5 ladder** (`geng -d3 -D5 n e:e`, `wave3/census/CALIBRATION.md` R2). `pairsat.py`
  reproduces each count, and its NOPAIR sets equal the B-1 files
  `wave3/census/data/ladder/n<n>-e<e>-pairfree.g6` as canonical sets (labelg):

  | n | e | graphs | pair-free (here) | pair-free (B-1) | canonical sets |
  |---|---|---|---|---|---|
  | 7 | 15 | 14 | 8 | 8 | equal |
  | 8 | 18 | 68 | 19 | 19 | equal |
  | 9 | 21 | 276 | 15 | 15 | equal |
  | 10 | 23 | 8,435 | 1,765 | 1,765 | equal |
  | 11 | 26 | 56,071 | 1,501 | 1,501 | equal |

  The levels above them have pairs throughout, as in B-1: n = 9, e = 22 (28 graphs); n = 10, e = 24
  and 25 (1,188 and 60); n = 11, e = 27 (3,749). `brute.py` agrees graph by graph at (9, 21) and
  (10, 23).
- **The 120 known 5-regular pair-free graphs on 18 vertices** (B-1 R3, `glue18-classes.g6`): both
  encodings answer NOPAIR on all 120 (`logs/glue18/all_pairsat.out`, 25 s;
  `logs/glue18/all_cuts.out`, 4.5 s, at most 5 cut rounds per graph). Positive control at the same
  size: 50 random 5-regular graphs on 18 vertices (networkx `random_regular_graph`, seeds 1 to 50,
  `code/random_reg.py`) all get a verified pair from both encodings.
- **Second encoding against the first.** `pairsat_cuts.py` agrees graph by graph with `brute.py` on
  every graph on 3 to 8 vertices and with `pairsat.py` on all nine ladder levels above, and it finds a
  verified pair in each of the 388 and 41 check-1 graphs (`logs/xcheck/compare.txt`).
- The per-graph timing logs `logs/glue18/pairsat.txt` and `cuts.txt` come from an earlier pass in
  which the two runs shared a temporary file name, so in `cuts.txt` graph 2 read an empty file
  (verdict NONE). `code/glue18.sh` is fixed; the whole-file runs above are the results.

## Check 1: triangle-free and bipartite, n = 16

- `geng -t -d5 -D5 16`: 388 graphs in 3.3 s. `geng -tc -d5 -D5 16` writes the identical file, so all
  388 are connected.
- `geng -b -d5 -D5 16`: 41 graphs. `genbg -d5 -D5 8 8`: 51 bicoloured classes, 41 after canonical
  labeling with labelg. The two canonical sets are equal, and all 41 lie in the triangle-free set.
- Both sets equal method 1's `reg5n16/data/struct/trianglefree-all.g6` and `bipartite-all.g6` as
  canonical sets.
- All 388 and all 41 have a pair, found once by MiniSat and again by CaDiCaL (separate runs, different
  certificates). Every certificate was verified inline and re-verified from the saved file. Cycle
  lengths of the MiniSat pairs: triangle-free 12 (9), 13 (17), 14 (100), 15 (68), 16 (194); bipartite
  14 (23), 16 (18). The genbg-derived 41 were decided as well, with the same result.
- Certificates (graph6, C1, C2 per line): `logs/check1/trianglefree.certs.txt`,
  `logs/check1/bipartite_gengb.certs.txt`, and the `.cd19.certs.txt` files. Graph lists:
  `data/check1/`.

## Check 2: every 5-regular graph on at most 14 vertices

Odd orders have no 5-regular graph. n = 14 ran as 40 shards (`geng -d5 -D5 14 r/40`) on 4 workers,
09:48 to 10:05. A shard counts only if geng's `>Z` count, the file's line count and the decider's
count agree and every graph is PAIR with a verified pair (`code/collect.py`).

| n | graphs (geng `>Z`) | PAIR, verified | pair-free | lengths of the pairs found | decider CPU |
|---|---|---|---|---|---|
| 6 | 1 | 1 | 0 | 5 (1) | <1 s |
| 8 | 3 | 3 | 0 | 7 (1), 8 (2) | <1 s |
| 10 | 60 | 60 | 0 | 5 (1), 8 (3), 9 (24), 10 (32) | <1 s |
| 12 | 7,849 | 7,849 | 0 | 5 (4), 6 (4), 8 (5), 9 (31), 10 (526), 11 (4,173), 12 (3,106) | 4 s |
| 14 | 3,459,386 | 3,459,386 | 0 | 5 (227), 6 (134), 7 (131), 8 (255), 9 (483), 10 (3,263), 11 (32,408), 12 (340,471), 13 (1,934,694), 14 (1,147,320) | 3,136 s |

The counts match B-1 R1. Totals and per-shard rows: `logs/check2_n14.collected.json`,
`logs/check2_n<n>.collected.json`; per-shard input hashes in `logs/check2/*.meta`.

## Check 3: unpruned spot-check at n = 16

- Shards of plain `geng -d5 -D5 16 r/20000`, taken in the order `data/check3_shard_order.txt`
  (Python 3.9.6 `random.Random(20261006).sample(range(20000), 400)`), 4 workers from 10:08:31, no new
  shard after 10:41:30. The first 28 shards of that order ran, and all 28 completed. Residues: 182,
  376, 1052, 2633, 2664, 2814, 3530, 3817, 4398, 5357, 6459, 7134, 7641, 7711, 8432, 9390, 9459,
  12076, 13986, 15128, 16213, 16339, 16705, 17154, 17194, 17855, 18318, 18857.
- 3,612,814 graphs, each PAIR with a verified pair; 0 pair-free. Lengths of the pairs found: 5 (294),
  6 (99), 7 (20), 8 (78), 9 (123), 10 (429), 11 (1,519), 12 (9,057), 13 (62,241), 14 (477,897),
  15 (1,919,999), 16 (1,141,058).
- Coverage: 28 of 20,000 shards, 0.14%. Shard sizes were 113,626 to 140,854 graphs (mean 129,029).
  At that mean the whole census is about 2.58 billion graphs, so by graph count the sample is also
  about 0.14%.
- Cost: about 25 s of geng and 270 s of decider per shard, about 2.1 ms per graph. The whole
  unpruned census at this rate would take about 1,600 core-hours.
- These shard numbers do not correspond to method 1's: the pruned and unpruned generators split the
  search differently.
- Totals and per-shard rows: `logs/check3_n16.collected.json`; per-shard input hashes in
  `logs/check3/*.meta`. The shard files themselves were deleted after each shard completed.

## Limits

- Check 3 samples 0.14% of the n = 16 census. It cannot rule out a pair-free graph elsewhere. The
  coverage claim at n = 16 remains method 1's census.
- Both methods generate with nauty's geng (method 1 compiled its hook into `geng.c` from the same
  nauty 2.9.3 tree, `reg5n16/code/build.sh`). genbg is a second generator only for the bipartite
  family.
- Check 2 agrees with B-1 on counts; check 1 agrees with method 1 on the graph sets themselves.

## Files

- `code/pairsat.py` (decider and checker), `code/pairsat_cuts.py` (second encoding), `code/brute.py`
  (exhaustive search), `code/recheck_certs.py`, `code/compare.py`, `code/collect.py`,
  `code/random_reg.py`.
- Drivers: `code/run_check1.sh`, `code/shard.sh` and `code/run_check2_n14.sh`, `code/shard16.sh` and
  `code/run_check3.sh`, `code/run_calib.sh`, `code/run_xcheck.sh`, `code/glue18.sh`.
- `data/check1/` (graph lists), `data/check3_shard_order.txt`, `data/glue18-classes.input.g6`
  (copied from `wave3/census/data/glue18/glue18-classes.g6`), `data/random5reg_n18_seeds1-50.g6`.
- `logs/`: per-check logs, summaries (`*.summary.json`, `*.collected.json`), certificates
  (`*.certs.txt`; the two n = 11, e = 26 files are gzipped), `env.txt`.
- The n = 14 and n = 16 shard files were written to the session scratchpad, not to the repository;
  each shard's SHA-256 is in its `.meta` file.

## Reproduce

```
cd [local path]
bash code/run_check1.sh
nohup bash code/run_check2_n14.sh > logs/check2_n14_driver.log 2>&1 &
for n in 6 8 10 12; do bash code/shard.sh check2 $n 0 1; done
nohup bash code/run_check3.sh <CUTOFF_EPOCH_SECONDS> > logs/check3_driver.log 2>&1 &
bash code/run_calib.sh
bash code/run_xcheck.sh
~/.cache/erdos585/venv/bin/python code/pairsat.py data/glue18-classes.input.g6 logs/glue18/all_pairsat --solver m22 --n 18 --deg 5 --certs
~/.cache/erdos585/venv/bin/python code/pairsat_cuts.py data/glue18-classes.input.g6 logs/glue18/all_cuts
~/.cache/erdos585/venv/bin/python code/collect.py check2 14
~/.cache/erdos585/venv/bin/python code/collect.py check3 16
```

The scripts write graph6 files to this session's scratchpad (the `SP` variable in the scripts that
set one); change `SP` to rerun elsewhere. `run_xcheck.sh` reads the files `run_calib.sh` writes there.

## Budget

About 3.6 core-hours (wall time times workers), never more than 4 workers at once. Check 2 at
n = 14 took 1.15 h (09:48 to 10:05) and check 3 took 2.35 h (10:08 to 10:43). Check 1, the
calibration, the cross-checks, the 18-vertex tests and the benchmarks took about 0.15 h together.
Nothing was sent off this machine, and check.sh was not run.

`code/pairsat.py` gained the `--phase-x` option at 09:52, during the n = 14 run, so shards started
after that ran the new file. The option is off by default, it had no effect in a benchmark, and no
reported run used it. Code hashes are in `logs/env.txt`.
