# S6 at |B| = 22: run result (collector output)

Written by `code/collect.py` at 2026-10-06 03:22:51 EDT from the slices with a done marker. Rung (b) computation; nothing here is reviewed. Definitions and method: `JOBS.md`.

## Coverage

- Slices done: **10000 of 10000** (`genbg -X-3 -d6:6 -D6:6 11 11 r/10000`, r in `data/slices_done.txt`; the run takes slices in the fixed random order `data/order.txt`).
- Colored graphs generated in those slices (genbg class count, classes A = 0..10, B = 11..21; a graph and its side swap are separate genbg classes unless isomorphic, so each uncoloured graph is tested once per orientation): **156473848**; read by s6n22: 156473848; bad input: 0.
- **All slices done: the test is exhaustive over every simple bipartite 6-regular graph on 11+11 vertices.**

## Counts

| quantity | value |
|---|---|
| E10 graphs (min essential cut >= 10) | 156473845 |
| non-E10 graphs (skipped) | 3 |
| tests (E10 graph, edge oy); 66 per graph | 10327273770 |
| solved, all tiers (verified pair) | 10327273770 |
| DFS first pass solves (tests outside the AM sample) | 7745063780 |
| AM fallback solves (after a DFS budget-out) | 143998 |
| DFS large-budget solves | 0 |
| AM sample: tests (graphs with index % AMS == 0, AM walk first) | 2582065992 |
| AM sample: solved within the short budget (recoloring solves) | 2581732084 |
| AM sample: stalls at the short budget (frames saved) | 333908 |
| AM sample: stalls then solved by continuing the walk | 333908 |
| AM sample: stalls then solved by DFS | 0 |
| AM sample: no frame built | 0 |
| survivors sent to SAT (SAT calls) | 0 |
| SAT answers: SPAN / NOSPAN / TIMEOUT | 0 / 0 / 0 |
| SAT witness check failures | 0 |
| DFS exhausted with no pair (exact NO by DFS) | 0 |
| **failures (S6 counterexample candidates, NOSPAN by two SAT deciders)** | 0 |
| verify failures (a tool bug, not a result) | 0 |
| stall lines saved | 333908 |
| slices with a failed run (logs/failed.txt lines) | 0 |

## Timing (CPU seconds inside s6n22, summed over slices)

| part | seconds | per test or graph |
|---|---|---|
| E10 test | 14837 | 94.8 us per graph |
| DFS first pass | 10776 | 1.39 us per test |
| AM sample (walk + its fallbacks) | 78787 | 30.5 us per test |
| fallbacks after DFS budget-out | 3.8 | |
| SAT (python, survivors) | 0.0 | |
| s6n22 wall, summed | 109788 | |
| slice wall incl. genbg, summed | 110454 (30.7 core-hours) | |

## Histograms

- min essential cut over graphs: 6: 1, 8: 2, 10: 156473845
- AM sample, Phi of the initial frame: 2: 645680513, 3: 1209068666, 4: 643291776, 5: 81844000, 6: 2168277, 7: 12740, 8: 20
- AM sample, iterations to Phi = 2 (bucket b = [2^(b-1), 2^b), 0 = none needed): 0: 645680513, 1: 241141073, 2: 400217618, 3: 543257883, 4: 498851793, 5: 224041516, 6: 28493795, 7: 47893
- AM sample, Phi at the stall: 3: 320018, 4: 12546, 5: 1323, 6: 21
- AM sample, extra iterations when a stalled walk was continued and escaped: 1: 42019, 2: 69115, 3: 93097, 4: 85475, 5: 39167, 6: 4970, 7: 65

## Stalled frames (for the S6 proof lane)

`data/stall_frames.txt`: 333908 lines, one per AM-sample test whose walk did not reach Phi = 2 within the short budget. Format: `slice=<r> <graph6 of B> o=<o> y=<y> phi_stall=<Phi at the stall> phi_min=<min Phi seen> moves_short=<budget> cont_moves=<extra iterations to escape, -1 if the continuation did not escape> solved_by=<am_continued|dfs|survivor> lam=<p-q:c,...> col=<colours of the 55 Y edges>`. The frame is the stalled one (before the continuation). Y edges are ordered by (A-vertex, B-vertex) in B's labels with o, y removed; Lambda edges are listed as (P-end in N(o)-y, Q-end in N(y)-o, color 4 or 5); colors 0-3 are the two factors under the pairing that gives Phi (min over the three pairings).
SAT on the stalled tests (`code/sat_stalls.sh`, run after the slices): lines=333908 SPAN=333908 NOSPAN=0 TIMEOUT=0 witness_fail=0 candidate_failure=0 sec=542.5


Run parameters (from the first slice): {"AMS": "4", "MS": "64", "MX": "1000", "MF": "1000", "RF": "3", "NA": "50000", "NB": "5000000", "dfs": "1", "testall": "0", "seed": "1"}

