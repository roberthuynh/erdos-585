# L5B: a second, independent method for census L5

Lane: L5B, October 5, 2026. Log: `LOG.md`. Resume notes: `RESUME.md`. Code: `code/`. Data:
`data/census/` (17 MB, one certificate line per graph), `data/superset/`, `data/validation/`.
No `check.sh`, no Lean. Rung (b).

## Verdict

**No pair-free graph found.** All 1,357,397 isomorphism classes of bipartite graphs with δ ≥ 4,
Δ ≤ 6 and e = 3n − 5 on at most 17 vertices (geng, no color classes) have a pair. Each pair is an
explicit certificate, and separate code re-checked every one of them. The decider never answered
UNSAT, so there were no exceptions to re-decide.

Converted to genbg's color-preserving classes, the counts equal the original's at every side split,
1,471,650 in all (SCOUT §2.4; the referee checked the same sum). L5 now has two independent methods
at every order through 17, not just through 6+7.

## Statement checked

L5 (wave3/pairs/SCOUT.md, table row L5 and §2.4): there is no pair-free bipartite graph with minimum
degree ≥ 4, maximum degree ≤ 6 and exactly 3n − 5 edges on at most 17 vertices. A pair is two
edge-disjoint cycles with the same vertex set. This is the form PAIRS Proposition 5 uses (the 4-core K
is bipartite, pair-free, δ ≥ 4, Δ ≤ 6, e(K) = 3|K| − 5). Proposition 5 feeds Corollary B
(wave4/theory/ADDENDUM-B.md, Lemma B2) and Theorem C at n = 23 (wave4/c1type/PAPER.md, (F3)).

## How the original was done (SCOUT §2.4, `run_l5s8.sh`)

- **Generator:** nauty 2.9.3 `genbg -q -d4:4 -D6:6 a b 3n-5:3n-5`, for the side splits 5+5, 6+6,
  7+7, 8+8, 4+5, 5+6, 6+7, 7+8 and 8+9 (8+9 in 12 shards). genbg generates bicoloured graphs up to
  color-preserving isomorphism. So for a = b, a graph is listed twice unless it has an automorphism
  that exchanges the sides.
- **Decider:** `pairc f` (585-fable/tools/pairc.c). It tries every vertex subset S with min degree
  ≥ 4 in G[S], enumerates every Hamilton cycle C1 of G[S] through min S by DFS, then runs a DFS for a
  Hamilton cycle of G[S] − E(C1).
- **Referee** (wave3/pairs/REVIEW.md §3): own generator and own cycle-grouping tester, through 6+7
  only.

## This method

Nothing below calls or copies pairc, ptool, mpair or the referee's genbip, rpair or hd. All code is in
`code/`.

1. **Generator: nauty `geng -b`, not genbg.** geng builds all graphs on n vertices one vertex at a
   time by canonical augmentation, and with `-b` keeps only bipartite graphs at every level. It
   outputs one graph per isomorphism class, with no color classes. One run per order covers every
   side split; the split is read off each output graph.
   - Command per order: `geng -b -d4 -D6 n 3n-5:3n-5 [r/mod]`, for n = 5..17.
   - n = 17 runs in 64 shards (`r/64`) and n = 16 in 8 shards (`r/8`). Smaller orders run unsplit.
   - Shared ground: geng and genbg come from the same nauty release. They are different programs with
     different generation schemes (uncoloured graphs plus a bipartite filter, versus bicoloured graphs
     with fixed classes).
2. **Exact class filter.** `class_check` in `l5b_sat.py` uses its own graph6 parser. It checks
   e = 3n − 5, every degree in [4, 6], and bipartiteness by a BFS 2-coloring of every component,
   and it records connectivity and the side sizes. `verify.py` repeats these checks with networkx.
   The superset checks below run geng with a degree flag dropped, then apply the same filter.
3. **Pair decider: SAT.** The encoding is `encode` in `l5b_sat.py`, solved by PySAT with
   MiniSat 2.2.
   - *Variables:*
     - x_v: v is in S.
     - r_e, b_e: edge e is on the red cycle C1, or on the blue cycle C2.
     - o_v: v is the root, the least vertex of S.
     - R^c_{v,k}, for color c and 0 ≤ k ≤ K = ⌊n/2⌋: v is joined to the root by a c-path of length
       ≤ k. R^c_{v,0} is o_v itself.
     - t^c_{u,v,k}: R^c_{u,k−1} holds and uv has color c.
   - *Clauses:*
     - r_e → x_u, x_w and b_e → x_u, x_w; ¬(r_e ∧ b_e).
     - For each v and each color: at most 2 incident c-edges, and x_v → at least 2.
     - Exactly one root; o_v → x_v; o_v → ¬x_u for u < v.
     - R^c_{v,k} → R^c_{v,k−1} ∨ ⋁_u t^c_{u,v,k}; t^c_{u,v,k} → R^c_{u,k−1}; t^c_{u,v,k} → c_{uv}.
     - x_v → R^c_{v,K}.
   - *Sound:* in a model each color class is 2-regular on S and absent outside S. The R chain gives
     every vertex of S a path of that color to the root. So each color class is one cycle through
     all of S, which is a pair.
   - *Complete:* given a pair (C1, C2) on S, take the root min S and set
     R^c_{v,k} = [dist_{Cc}(root, v) ≤ k]. A cycle of length |S| ≤ n has distances at most
     ⌊n/2⌋ = K. Set t as forced; every clause holds. So UNSAT would mean pair-free.
4. **Certificates.** Each model is decoded into two cycles (vertex sequences) and checked inside the
   decider. It is written to `data/census/*.out.gz` as one line per graph, `<graph6> P <|S|> <C1>
   <C2>`, with vertex i written as the letter chr(97 + i).
   - `verify.py` re-checks every certificate with separate code. It uses the networkx graph6 parser
     and checks that consecutive vertices are adjacent, the closing edge is present, no vertex
     repeats, V(C1) = V(C2) has size |S|, and E(C1) ∩ E(C2) = ∅.
   - So a "has a pair" verdict does not depend on the encoding or the solver.
5. **Reconciliation.** geng counts uncoloured classes (U); genbg counts color-preserving ones.
   - Odd n = 2a + 1: every graph is connected with sides a and a + 1. It has exactly one coloring with
     the a-side first, so the two counts agree.
   - Even n = 2a: the color-preserving count is 2U − W. W is the number of graphs with an automorphism
     that exchanges the sides, found by `verify.py` (networkx VF2++ with side labels).
6. **Distinctness.** At each order the graph6 strings are pairwise distinct, and so are their
   canonical forms. The canonical forms come from nauty `labelg`, used only for this check. So no
   class is counted twice.

**Why only the splits a+a and a+(a+1), and why every graph is connected.**
- e ≤ 6 × (smaller side) gives 3n − 5 ≤ 6a, so 3(b − a) ≤ 5 and the sides differ by at most 1. This
  holds under every bipartition.
- δ ≥ 4 forces at least 4 vertices on each side of each component. So a nonempty class needs n ≥ 9
  (at n = 8 the only candidate is K_{4,4}, with 16 < 19 edges).
- A disconnected member needs at least 16 vertices. At n = 16 that is 2K_{4,4} (32 < 43 edges); at
  n = 17 it is K_{4,4} + K_{4,5} (36 < 46 edges). The run confirms it: 0 disconnected graphs.

## Commands

```
cd [local path]
JOBS=6 nohup nice -n 10 bash code/run_census.sh all > logs/driver.out 2>&1 < /dev/null &
#   each shard ("bash code/run_census.sh one n mod r"):
#   geng -b -d4 -D6 n 3n-5:3n-5 [r/mod] | python code/l5b_sat.py --solver m22 --summary B.sat.json | gzip -9 > B.out.gz
#   python code/verify.py B.out.gz --exceptions B.exc > B.verify.json
#   stage 0: geng -u -b -d4 -D6 n 3n-5:3n-5 for n = 15, 16, 17 (data/census/count_n*.txt)
nohup nice -n 15 bash code/run_superset.sh > logs/superset.out 2>&1 &
~/.cache/erdos585/venv/bin/python code/collect.py          # -> data/census/SUMMARY.json, logs/collect.out
~/.cache/erdos585/venv/bin/python code/validate.py --random 3000 --pairfree \
    ../../wave3/pairs/data/t1_Z.g6 ../../../585-fable/data/frontier-n{7,8,9,10}-level-5.g6
~/.cache/erdos585/venv/bin/python code/validate.py --brute data/validation/<file>.g6
```

`geng` is `~/.cache/erdos585/nauty2_9_3/geng`. The run took place on October 5, 21:40 to 21:59 EDT,
with 83 shards and 0 failures (`logs/shards.log`).

## Counts by stage and side split

The stages are:
1. geng output (uncoloured classes);
2. the class filter;
3. SAT;
4. certificate re-check (`verify.py`);
5. distinct canonical forms;
6. conversion to color-preserving counts.

Stage 0 is an unsplit `geng -u` count, run at n = 15, 16 and 17. At n = 5..8 every stage is 0.

| n | split | geng -u | geng output | in class | SAT: pair | certificates OK | pair-free | distinct canonical | side-swap W | color-preserving | original | match |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| 9 | 4+5 | | 0 | 0 | 0 | 0 | 0 | 0 | | 0 | 0 | yes |
| 10 | 5+5 | | 1 | 1 | 1 | 1 | 0 | 1 | 1 | 1 | 1 | yes |
| 11 | 5+6 | | 2 | 2 | 2 | 2 | 0 | 2 | | 2 | 2 | yes |
| 12 | 6+6 | | 9 | 9 | 9 | 9 | 0 | 9 | 5 | 13 | 13 | yes |
| 13 | 6+7 | | 29 | 29 | 29 | 29 | 0 | 29 | | 29 | 29 | yes |
| 14 | 7+7 | | 448 | 448 | 448 | 448 | 0 | 448 | 77 | 819 | 819 | yes |
| 15 | 7+8 | 2,895 | 2,895 | 2,895 | 2,895 | 2,895 | 0 | 2,895 | | 2,895 | 2,895 | yes |
| 16 | 8+8 | 116,035 | 116,035 | 116,035 | 116,035 | 116,035 | 0 | 116,035 | 2,157 | 229,913 | 229,913 | yes |
| 17 | 8+9 | 1,237,978 | 1,237,978 | 1,237,978 | 1,237,978 | 1,237,978 | 0 | 1,237,978 | | 1,237,978 | 1,237,978 | yes |
| total | | | 1,357,397 | 1,357,397 | 1,357,397 | 1,357,397 | 0 | | | 1,471,650 | 1,471,650 | yes |

Other checks:
- The class filter rejected 0 graphs. Every graph is connected, and its split is exactly the
  predicted one. `verify.py` found 0 bad certificates and 0 F or X lines.
- Pair sizes |S| found by the solver are listed below. The solver returns some pair, not a smallest
  one.
  - n = 16: 8: 1,642; 10: 6,376; 12: 48,511; 14: 55,411; 16: 4,095.
  - n = 17: 8: 13,908; 10: 34,559; 12: 190,688; 14: 773,938; 16: 224,885.

## Superset checks (exact degree and edge filter)

geng was rerun with one or both degree flags dropped, and `superset_filter.py` (the same rule as
`class_check`) counted the class in its output.

| n | geng flags | generated | rejected (min degree / max degree) | in class | equals the exact-flag count |
|---|---|---|---|---|---|
| 9..15 | `-b` only | 0, 1, 4, 37, 549, 14,176, 592,620 | n = 15: 480,247 / 109,478 | 0, 1, 2, 9, 29, 448, 2,895 | yes |
| 16 | `-b -D6` (no `-d4`) | 181,327 | 65,292 / 0 | 116,035 | yes |
| 16 | `-b -d4` (no `-D6`) | 6,083,736 | 0 / 5,967,701 | 116,035 | yes |
| 17 | `-b -D6` (no `-d4`), 4 shards | 2,557,932 | 1,319,954 / 0 | 1,237,978 | yes |

At n = 17, `-b -d4` without `-D6` was not run. It would generate about 614 million graphs (about 1.5
core-hours for geng plus about 5 for the Python filter). At that order the max-degree flag is checked
only by the count match with genbg.

## Validation of the decider

| Test | Graphs | Result |
|---|---|---|
| Named graphs (K4, K5, K_{3,3}, K_{4,4}, K_{4,4} − e, Petersen, octahedron) | 7 | SAT = brute force = expected |
| Random G(n, p), n = 4..9, and random bipartite graphs with sides 3..5 (seed 585) | 3,000 | SAT = brute force on all; 623 with a pair, 2,377 without |
| Known pair-free general graphs: the 17 level −5 cores (585-fable/data/frontier-n7..10-level-5.g6) and wave3/pairs/data/t1_Z.g6 | 5,642 | all UNSAT |
| Bipartite brute force, geng -b at n = 12, 13 with δ ≥ 3, 30 to 34 edges, and the class itself at n = 12, 13 (`logs/validate2.json`) | 378 | SAT = brute force on all (all have a pair) |
| Bipartite brute force, geng -b -d4 -D6 14 36:36 (`logs/validate3.json`) | 1,144 | SAT = brute force on all (all have a pair) |
| Verifier negative test (`data/validation/corrupt14.txt`) | 40 | 30 corrupted certificates rejected; 10 rotated (still valid) accepted |

The brute force (`validate.py`) enumerates every cycle once and looks for two edge-disjoint cycles
with the same vertex set. It is written here and shares no code with the census path. Its method
resembles the referee's rpair (cycle grouping), but the code is independent.

No UNSAT answer occurred in the census. So the verdict rests on the certificates and on the
generator's completeness. It does not rest on the encoding or the solver.

## Binaries and code (SHA-256)

| File | SHA-256 |
|---|---|
| `~/.cache/erdos585/nauty2_9_3/geng` (nauty 2.9.3) | 588052a87e5313f331aa145a0a641702b6c13b6e2387dd3c4807bf7f49fdaca1 |
| `~/.cache/erdos585/nauty2_9_3/labelg` (distinctness check only) | ae8b1e7ef173c1665725e708bd7abd00b08ee4230ba2bd04117ec63d441274a0 |
| `~/.cache/erdos585/nauty2_9_3/genbg` (not used; listed for contrast) | 502f5f46e613f9eefa905a2c521f06f45d0737854374bbd60e6929f45f4ef957 |
| CPython 3.11.15 (`~/.local/share/uv/python/cpython-3.11.15-macos-aarch64-none/bin/python3.11`) | 7e470bc0e4889177f9acb5f62208fae2825aba9ccd6a67b7c3378f522aa8f148 |
| PySAT 1.9.dev15 solvers (`venv/.../pysolvers.cpython-311-darwin.so`, MiniSat 2.2 = `m22`) | fa1383ba0fb5cc94a009d9f5c06cf36b896f1b3a3fd5d7b57f73541f289f1784 |
| networkx 3.6.1 | (pure Python, venv) |
| `code/l5b_sat.py` | 99676a56964d1c1e724b6d1bd7fd0026bda559fcdd9022ab21f5b706e640d1a3 |
| `code/verify.py` | 03c15fbb2809de11970c31ba959edaff67dc720def79f30bc612aaaa4487dd87 |
| `code/run_census.sh` | eb4bdc91ca53ed6b46e16d9296110914d1b5efc4672afd110eb48a14d7fe6c35 |
| `code/collect.py` | a4e6994b7b289989de87dffbb3f7663102f3cfeaedf76eb4d6d55ff2c6947cc2 |
| `code/validate.py` | abd7c566ee4e3a89f450ef758163532c0b98bd2cbd4211fd9e9c3dcd428a3197 |
| `code/superset_filter.py` | a0d6f9d6fa927b7cf55bd777bbeca190d6a070cda08a0e2f6ca531928235be51 |
| `code/run_superset.sh` | fd02123a14c0bbd5b836a2f52a10f9a572759dfd962404cdd0ee71c2985300f7 |
| `data/census/SUMMARY.json` | 07b3a1ff13c0cdc1ae0cb1a18efe0eb68bec445b7815eef60c06a70f98485eea |

## Cost

- **Pilot:** at n = 17, 2,001 graphs took 5.8 s CPU (2.9 ms per graph), and geng took about 1.25 s
  per 1/50 slice. That projected about 1.1 core-hours, well under the 25 core-hour cap.
- **Actual run:** 6 workers at nice 10, while the machine load ran at 80 to 135 on 18 cores. Decider
  process time summed over shards was 5,787 s (wall, so an upper bound on CPU), and shard wall time
  summed to 6,461 s. The census itself took 19 minutes. The superset checks took about 10 minutes of
  CPU.

## Caveats

- **nauty is common ground.** geng, genbg and labelg are all nauty 2.9.3 programs. Three things guard
  the generator step:
  - the generation schemes differ;
  - the counts agree with genbg's after the color conversion at every split;
  - the superset checks reproduce the class with a degree flag dropped, except the max-degree flag at
    n = 17 (see above).
- **The SAT solver would matter only for UNSAT answers, and there were none.** If the solver erred
  toward "pair", the certificate re-check would catch it; none failed.
- The census path shares no code with pairc, ptool, mpair or the referee's tools. The test inputs
  t1_Z.g6 and the frontier cores are the author's data, used as test cases only.
