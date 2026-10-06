# S6 at |B| = 22: independent spot-check of wave6/s6n22

Lane wave8/s6spot, 2026-10-06. Rung (b) computation. Nothing here is reviewed. No `check.sh`, no
Lean, nothing sent off this machine. Run record: `JOBS.md`; code in `code/`; data in `data/`.

**Verdict: s6n22 checks out on the sample.** On 50 random slices (588,094 colored graphs, 0.3758% of the 156,473,848 classes; 38,814,204 (graph, edge) tests, 0.3758% of s6n22's 10,327,273,770) every compared count matches s6n22's per-slice record (genbg count, E10 count, min-cut histogram, tests), and every test has two edge-disjoint Hamilton cycles in Y = B - o - y, found by a SAT encoding written here and checked edge by edge against the graph: 38,814,204 SPAN, 0 NO, 0 witness failures. The three non-E10 graphs are confirmed not E10 by two methods (min essential cuts 8, 6, 8, as recorded). S6's conclusion fails on each of them, exactly on the edges of the minimum cut (8 + 6 + 8 of 198 tests), so S6 needs its E10 hypothesis already at |B| = 22.

## What was checked, and what is shared with s6n22

S6 (wave4/va6/SCOUT.md §7): if Γ = B - o is sparse, every port y of o has two edge-disjoint Hamilton
cycles in B - o - y. For a 6-regular B, g(S) = |δ_B(S)| for S avoiding o, so "B - o sparse" for
one o, or for all o, is the same as "B is E10" (every edge cut with at least 2 vertices on each side
has at least 10 edges). The test for an edge oy does not depend on which end is called o, so a
colored graph has 66 tests, as in s6n22; a graph and its side swap are separate genbg classes and
each is tested in its own slice, as in s6n22 (JOBS.md there).

- **Shared with s6n22:** the genbg binary `~/.cache/erdos585/nauty2_9_3/genbg` (SHA-256
  `502f5f46e613f9ee…`) and its command line `genbg -X-3 -d6:6 -D6:6 11 11 r/10000` (read from
  s6n22's `run_shard.sh`); the PySAT library (s6n22 used it, through wave4/va6's
  `span_oracle.py`, only for its 0 survivors and its post-run SAT check of the 333,908 stalled AM
  tests; its decisions came from its own C tool, a DFS and the AM walk).
- **Written here, sharing no code with `wave6/s6n22/code`:** `code/e10cut.c` (graph6 decoder and
  exact minimum essential cut), `code/spantest.py` (graph6 decoder, SAT encoding, witness checker),
  `code/validate.py`, `code/nonE10.py`, `code/collect.py`, the driver scripts. Nothing in s6n22's
  `code/` was imported or run.

## Sample

- Slice order: a uniform random permutation of 0..9999 from Python's `random.Random(seed)` with
  seed **1931695848**, drawn from `os.urandom` and recorded in `data/sample_seed.txt` before any
  slice ran; order in `data/sample_order.txt` (`code/pick_sample.py`). (The date seed 20261006 was
  tried first and reproduced s6n22's own `order.txt` exactly, so it was dropped.)
- **The sample is the first 50 slices of that order** (the number was fixed from the pilot timing,
  before any results): 7797, 1881, 5108, 7664, 7309, 8947, 7007, 9698, 2401, 6151, 3827, 3043, 1641, 3182, 7188, 1469, 6975, 2378, 9328, 1185, 9822, 3788, 8948, 1032, 5337, 3371, 685, 7574, 5602, 5646, 9666, 5355, 592, 8837, 8741, 4397, 8653, 871, 6745, 5888, 8652, 4846, 3855, 3616, 7366, 4584, 9153, 2158, 9111, 1546. Done: 50 of 50.
  Slice 1881, second in the order, was the pilot (same pipeline, run in the foreground just
  before the launch; the driver skipped it).
- Not random, checked separately: slices 5491, 7913, 8360, the three where s6n22 recorded one
  non-E10 graph each (E10 check on every graph, SAT only on the non-E10 graph).

## Counts compared, per slice

"now" = this lane's regeneration; "s6n22 sum" and "s6n22 genbg" = s6n22's `s<r>.sum` and
`s<r>.genbg.err`. "stall g6 found": every graph6 string in s6n22's `s<r>.stall` for that slice also
occurs in the regenerated slice (a content check beyond the counts).

| slice | graphs: genbg now / lines / s6n22 sum / s6n22 genbg | E10 now / s6n22 | min-cut hist now = s6n22 | stall g6 found | tests now / s6n22 | SPAN | NO | witness fail | match |
|---|---|---|---|---|---|---|---|---|---|
| 5491 (E10 only) | 35501 / 35501 / 35501 / 35501 | 35500 / 35500 | 8:1,10:35500 = | 81/81 | - / 2343000 | - | - | 0 | yes |
| 7913 (E10 only) | 12572 / 12572 / 12572 / 12572 | 12571 / 12571 | 6:1,10:12571 = | 23/23 | - / 829686 | - | - | 0 | yes |
| 8360 (E10 only) | 14213 / 14213 / 14213 / 14213 | 14212 / 14212 | 8:1,10:14212 = | 26/26 | - / 937992 | - | - | 0 | yes |
| 7797 | 44452 / 44452 / 44452 / 44452 | 44452 / 44452 | 10:44452 = | 104/104 | 2933832 / 2933832 | 2933832 | 0 | 0 | yes |
| 1881 | 1656 / 1656 / 1656 / 1656 | 1656 / 1656 | 10:1656 = | 4/4 | 109296 / 109296 | 109296 | 0 | 0 | yes |
| 5108 | 10866 / 10866 / 10866 / 10866 | 10866 / 10866 | 10:10866 = | 18/18 | 717156 / 717156 | 717156 | 0 | 0 | yes |
| 7664 | 19200 / 19200 / 19200 / 19200 | 19200 / 19200 | 10:19200 = | 42/42 | 1267200 / 1267200 | 1267200 | 0 | 0 | yes |
| 7309 | 4454 / 4454 / 4454 / 4454 | 4454 / 4454 | 10:4454 = | 7/7 | 293964 / 293964 | 293964 | 0 | 0 | yes |
| 8947 | 11753 / 11753 / 11753 / 11753 | 11753 / 11753 | 10:11753 = | 31/31 | 775698 / 775698 | 775698 | 0 | 0 | yes |
| 7007 | 12603 / 12603 / 12603 / 12603 | 12603 / 12603 | 10:12603 = | 23/23 | 831798 / 831798 | 831798 | 0 | 0 | yes |
| 9698 | 15993 / 15993 / 15993 / 15993 | 15993 / 15993 | 10:15993 = | 25/25 | 1055538 / 1055538 | 1055538 | 0 | 0 | yes |
| 2401 | 2107 / 2107 / 2107 / 2107 | 2107 / 2107 | 10:2107 = | 3/3 | 139062 / 139062 | 139062 | 0 | 0 | yes |
| 6151 | 9009 / 9009 / 9009 / 9009 | 9009 / 9009 | 10:9009 = | 18/18 | 594594 / 594594 | 594594 | 0 | 0 | yes |
| 3827 | 2911 / 2911 / 2911 / 2911 | 2911 / 2911 | 10:2911 = | 9/9 | 192126 / 192126 | 192126 | 0 | 0 | yes |
| 3043 | 19070 / 19070 / 19070 / 19070 | 19070 / 19070 | 10:19070 = | 35/35 | 1258620 / 1258620 | 1258620 | 0 | 0 | yes |
| 1641 | 35478 / 35478 / 35478 / 35478 | 35478 / 35478 | 10:35478 = | 84/84 | 2341548 / 2341548 | 2341548 | 0 | 0 | yes |
| 3182 | 6562 / 6562 / 6562 / 6562 | 6562 / 6562 | 10:6562 = | 15/15 | 433092 / 433092 | 433092 | 0 | 0 | yes |
| 7188 | 12628 / 12628 / 12628 / 12628 | 12628 / 12628 | 10:12628 = | 38/38 | 833448 / 833448 | 833448 | 0 | 0 | yes |
| 1469 | 15960 / 15960 / 15960 / 15960 | 15960 / 15960 | 10:15960 = | 52/52 | 1053360 / 1053360 | 1053360 | 0 | 0 | yes |
| 6975 | 16597 / 16597 / 16597 / 16597 | 16597 / 16597 | 10:16597 = | 23/23 | 1095402 / 1095402 | 1095402 | 0 | 0 | yes |
| 2378 | 15779 / 15779 / 15779 / 15779 | 15779 / 15779 | 10:15779 = | 30/30 | 1041414 / 1041414 | 1041414 | 0 | 0 | yes |
| 9328 | 3877 / 3877 / 3877 / 3877 | 3877 / 3877 | 10:3877 = | 6/6 | 255882 / 255882 | 255882 | 0 | 0 | yes |
| 1185 | 2819 / 2819 / 2819 / 2819 | 2819 / 2819 | 10:2819 = | 10/10 | 186054 / 186054 | 186054 | 0 | 0 | yes |
| 9822 | 12100 / 12100 / 12100 / 12100 | 12100 / 12100 | 10:12100 = | 18/18 | 798600 / 798600 | 798600 | 0 | 0 | yes |
| 3788 | 9564 / 9564 / 9564 / 9564 | 9564 / 9564 | 10:9564 = | 17/17 | 631224 / 631224 | 631224 | 0 | 0 | yes |
| 8948 | 3032 / 3032 / 3032 / 3032 | 3032 / 3032 | 10:3032 = | 9/9 | 200112 / 200112 | 200112 | 0 | 0 | yes |
| 1032 | 12517 / 12517 / 12517 / 12517 | 12517 / 12517 | 10:12517 = | 24/24 | 826122 / 826122 | 826122 | 0 | 0 | yes |
| 5337 | 8919 / 8919 / 8919 / 8919 | 8919 / 8919 | 10:8919 = | 21/21 | 588654 / 588654 | 588654 | 0 | 0 | yes |
| 3371 | 17374 / 17374 / 17374 / 17374 | 17374 / 17374 | 10:17374 = | 37/37 | 1146684 / 1146684 | 1146684 | 0 | 0 | yes |
| 685 | 7980 / 7980 / 7980 / 7980 | 7980 / 7980 | 10:7980 = | 16/16 | 526680 / 526680 | 526680 | 0 | 0 | yes |
| 7574 | 5476 / 5476 / 5476 / 5476 | 5476 / 5476 | 10:5476 = | 10/10 | 361416 / 361416 | 361416 | 0 | 0 | yes |
| 5602 | 11311 / 11311 / 11311 / 11311 | 11311 / 11311 | 10:11311 = | 26/26 | 746526 / 746526 | 746526 | 0 | 0 | yes |
| 5646 | 5620 / 5620 / 5620 / 5620 | 5620 / 5620 | 10:5620 = | 11/11 | 370920 / 370920 | 370920 | 0 | 0 | yes |
| 9666 | 11306 / 11306 / 11306 / 11306 | 11306 / 11306 | 10:11306 = | 28/28 | 746196 / 746196 | 746196 | 0 | 0 | yes |
| 5355 | 9585 / 9585 / 9585 / 9585 | 9585 / 9585 | 10:9585 = | 15/15 | 632610 / 632610 | 632610 | 0 | 0 | yes |
| 592 | 5169 / 5169 / 5169 / 5169 | 5169 / 5169 | 10:5169 = | 13/13 | 341154 / 341154 | 341154 | 0 | 0 | yes |
| 8837 | 43632 / 43632 / 43632 / 43632 | 43632 / 43632 | 10:43632 = | 95/95 | 2879712 / 2879712 | 2879712 | 0 | 0 | yes |
| 8741 | 4894 / 4894 / 4894 / 4894 | 4894 / 4894 | 10:4894 = | 14/14 | 323004 / 323004 | 323004 | 0 | 0 | yes |
| 4397 | 6753 / 6753 / 6753 / 6753 | 6753 / 6753 | 10:6753 = | 16/16 | 445698 / 445698 | 445698 | 0 | 0 | yes |
| 8653 | 8445 / 8445 / 8445 / 8445 | 8445 / 8445 | 10:8445 = | 33/33 | 557370 / 557370 | 557370 | 0 | 0 | yes |
| 871 | 13071 / 13071 / 13071 / 13071 | 13071 / 13071 | 10:13071 = | 32/32 | 862686 / 862686 | 862686 | 0 | 0 | yes |
| 6745 | 7499 / 7499 / 7499 / 7499 | 7499 / 7499 | 10:7499 = | 13/13 | 494934 / 494934 | 494934 | 0 | 0 | yes |
| 5888 | 15656 / 15656 / 15656 / 15656 | 15656 / 15656 | 10:15656 = | 27/27 | 1033296 / 1033296 | 1033296 | 0 | 0 | yes |
| 8652 | 16531 / 16531 / 16531 / 16531 | 16531 / 16531 | 10:16531 = | 43/43 | 1091046 / 1091046 | 1091046 | 0 | 0 | yes |
| 4846 | 8867 / 8867 / 8867 / 8867 | 8867 / 8867 | 10:8867 = | 16/16 | 585222 / 585222 | 585222 | 0 | 0 | yes |
| 3855 | 3906 / 3906 / 3906 / 3906 | 3906 / 3906 | 10:3906 = | 10/10 | 257796 / 257796 | 257796 | 0 | 0 | yes |
| 3616 | 36256 / 36256 / 36256 / 36256 | 36256 / 36256 | 10:36256 = | 80/80 | 2392896 / 2392896 | 2392896 | 0 | 0 | yes |
| 7366 | 23712 / 23712 / 23712 / 23712 | 23712 / 23712 | 10:23712 = | 60/60 | 1564992 / 1564992 | 1564992 | 0 | 0 | yes |
| 4584 | 3104 / 3104 / 3104 / 3104 | 3104 / 3104 | 10:3104 = | 12/12 | 204864 / 204864 | 204864 | 0 | 0 | yes |
| 9153 | 1597 / 1597 / 1597 / 1597 | 1597 / 1597 | 10:1597 = | 2/2 | 105402 / 105402 | 105402 | 0 | 0 | yes |
| 2158 | 3191 / 3191 / 3191 / 3191 | 3191 / 3191 | 10:3191 = | 4/4 | 210606 / 210606 | 210606 | 0 | 0 | yes |
| 9111 | 2527 / 2527 / 2527 / 2527 | 2527 / 2527 | 10:2527 = | 5/5 | 166782 / 166782 | 166782 | 0 | 0 | yes |
| 1546 | 4726 / 4726 / 4726 / 4726 | 4726 / 4726 | 10:4726 = | 14/14 | 311916 / 311916 | 311916 | 0 | 0 | yes |

Totals over the 50 random slices: **588,094 graphs, 588,094 E10,
38,814,204 tests, 38,814,204 SPAN, 0 NO, 0 witness
failures**; every row matches: **yes**.

## Method

**E10 (`code/e10cut.c`).** For each graph, the exact minimum of |δ(S)| over all S with
2 <= |S| <= 20, by enumerating all 2^21 sets S that contain vertex 0 in reflected Gray-code order
(each bipartition once), updating |δ(S)| by deg(v) - 2|N(v) ∩ S| per step. Per graph it also checks
6-regularity, that every edge joins {0..10} to {11..21}, and recomputes |δ(S)| directly for the
final set and the argmin. Second method on a random subset (`code/flowsample.py`,
`data/val/flow_sample.log`): min over vertex-disjoint edge pairs (e, f) of the max-flow between e
and f (networkx), which equals the minimum essential cut for these graphs (an essential S with
|δ(S)| <= 10 < 12 <= 6|S| has an edge on each side). Result: 103/103 agree
(2 random graphs per random slice plus the 3 non-E10 graphs).

**Two edge-disjoint Hamilton cycles (`code/spantest.py`, PySAT MiniSat 2.2).** One incremental
solver per graph B: variables a_v (vertex active) and x(e, c) (edge e of B in cycle c = 0, 1);
clauses: x(e, c) implies both ends active; no edge in both cycles; at most 2 color-c edges at a
vertex (every 3-subset); an active vertex has at least 2 (every 5-subset of its 6 edges). Test
(o, y) solves under the assumptions "o, y inactive, all others active". A model gives two 2-factors
of Y; if either has several cycles, the cut "some vertex of S inactive, or some edge of δ_B(S) has
color c" is added for every such cycle S and both colors, and the solver runs again. Every cut
is valid for every test (if S avoids o and y it is a proper subset of V(Y), so a Hamilton cycle
leaves it; otherwise its guard holds), so UNSAT means no pair. Every SPAN answer is accepted only
after `verify_pair` checks the two cyclic vertex sequences against B: both are permutations of
V(B) - o - y, consecutive vertices are adjacent in B, and the 40 edges are distinct. A NO answer is
re-decided by a second encoding (Y alone, no activation literals, CaDiCaL 1.5.3). Each graph is
decoded twice (C and Python) and the two edge-list hashes are compared on every graph. SAT rounds
per test over the sample: median 2, max 14; CPU in spantest 152 us per
test.

## Tool validation (`data/val/`)

- Controls built here: K_(6,6) (36 tests: all SPAN, witnesses verified; min cut 10) and NEG24, two
  copies of K_(6,6) minus an edge joined by two edges (min cut 2 by both E10 methods; all 72 tests NO
  by both encodings).
- Witness checker: seven corrupted witnesses (same cycle twice, reversed copy, o included, vertex
  dropped or repeated, non-edge, swapped entries) rejected; 20,000 shuffled sequences agree with a
  direct recount (`witness.log`).
- Pilot: 100 graphs of slice 7797, 6,600 tests, the same answers with MiniSat, Glucose 4 and
  CaDiCaL (`pilot100_*.span.json`).

## The three non-E10 graphs

Found by regenerating slices 5491, 7913 and 8360 and running e10cut on all of their graphs
(5491: 35,501 graphs, E10 35,500 (s6n22: 35,501, 35,500), 7913: 12,572 graphs, E10 12,571 (s6n22: 12,572, 12,571), 8360: 14,213 graphs, E10 14,212 (s6n22: 14,213, 14,212)). graph6 in `data/nonE10.g6`,
details in `data/nonE10.txt`. Each is confirmed not E10 by both methods (e10cut and max-flow). On
each, the S6 conclusion fails exactly on the edges of its minimum cut, and every NO is certified
three ways: the incremental SAT, the second SAT encoding, and a counting argument that needs no
solver (`code/nonE10.py`). Take T = S - o - y (S the minimum cut set), let a and b count the edges
of δ_Y(T) whose end in T is on side A, resp. B, and d = |T_A| - |T_B|. A Hamilton cycle of Y meets T
in paths (possibly single vertices), each entered and left along crossing edges; a path with both
ends on A has one more A- than B-vertex, so d = p_AA - p_BB. Hence one Hamilton cycle uses at least
(mA, mB) crossing edges with A-, resp. B-ends, where (mA, mB) = (1, 1) if d = 0, (2d, 0) if d > 0,
(0, -2d) if d < 0. If a < mA or b < mB, Y has no Hamilton cycle; if a < 2mA or b < 2mB, Y has no two
edge-disjoint ones. Example: graph 13715 of slice 8360, edge (0, 11): d = 0 and only b = 1 crossing
edge ends on side B, but each of the two cycles needs one.

```
slice 5491 (mode e10only) graph index 33070: min essential cut 8, S = [0, 5, 6, 8, 9, 10, 12, 14, 16, 18, 20] (|S_A| = 6, |S_B| = 5), cut edges [(0, 11), (5, 11), (5, 15), (6, 13), (7, 12), (8, 17), (9, 19), (10, 21)]
  tests: 58 SPAN (witness verified), 8 NO (both SAT encodings): [(0, 11), (5, 11), (5, 15), (6, 13), (7, 12), (8, 17), (9, 19), (10, 21)]
  NO edges are exactly the cut edges: True
  NO (0,11): second encoding NO; one Hamilton cycle in Y: exists; counting certificate: no two edge-disjoint Hamilton cycles: T=[5, 6, 8, 9, 10, 12, 14, 16, 18, 20], a=5, b=1, d=0
  NO (5,11): second encoding NO; one Hamilton cycle in Y: exists; counting certificate: no two edge-disjoint Hamilton cycles: T=[0, 6, 8, 9, 10, 12, 14, 16, 18, 20], a=4, b=1, d=0
  NO (5,15): second encoding NO; one Hamilton cycle in Y: exists; counting certificate: no two edge-disjoint Hamilton cycles: T=[0, 6, 8, 9, 10, 12, 14, 16, 18, 20], a=5, b=1, d=0
  NO (6,13): second encoding NO; one Hamilton cycle in Y: exists; counting certificate: no two edge-disjoint Hamilton cycles: T=[0, 5, 8, 9, 10, 12, 14, 16, 18, 20], a=6, b=1, d=0
  NO (7,12): second encoding NO; one Hamilton cycle in Y: exists; counting certificate: no two edge-disjoint Hamilton cycles: T=[0, 5, 6, 8, 9, 10, 14, 16, 18, 20], a=7, b=0, d=2
  NO (8,17): second encoding NO; one Hamilton cycle in Y: exists; counting certificate: no two edge-disjoint Hamilton cycles: T=[0, 5, 6, 9, 10, 12, 14, 16, 18, 20], a=6, b=1, d=0
  NO (9,19): second encoding NO; one Hamilton cycle in Y: exists; counting certificate: no two edge-disjoint Hamilton cycles: T=[0, 5, 6, 8, 10, 12, 14, 16, 18, 20], a=6, b=1, d=0
  NO (10,21): second encoding NO; one Hamilton cycle in Y: exists; counting certificate: no two edge-disjoint Hamilton cycles: T=[0, 5, 6, 8, 9, 12, 14, 16, 18, 20], a=6, b=1, d=0
slice 7913 (mode e10only) graph index 12216: min essential cut 6, S = [0, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20] (|S_A| = 6, |S_B| = 5), cut edges [(0, 11), (6, 13), (7, 15), (8, 17), (9, 19), (10, 21)]
  tests: 60 SPAN (witness verified), 6 NO (both SAT encodings): [(0, 11), (6, 13), (7, 15), (8, 17), (9, 19), (10, 21)]
  NO edges are exactly the cut edges: True
  NO (0,11): second encoding NO; one Hamilton cycle in Y: none (UNSAT); counting certificate: no Hamilton cycle: T=[6, 7, 8, 9, 10, 12, 14, 16, 18, 20], a=5, b=0, d=0
  NO (6,13): second encoding NO; one Hamilton cycle in Y: none (UNSAT); counting certificate: no Hamilton cycle: T=[0, 7, 8, 9, 10, 12, 14, 16, 18, 20], a=5, b=0, d=0
  NO (7,15): second encoding NO; one Hamilton cycle in Y: none (UNSAT); counting certificate: no Hamilton cycle: T=[0, 6, 8, 9, 10, 12, 14, 16, 18, 20], a=5, b=0, d=0
  NO (8,17): second encoding NO; one Hamilton cycle in Y: none (UNSAT); counting certificate: no Hamilton cycle: T=[0, 6, 7, 9, 10, 12, 14, 16, 18, 20], a=5, b=0, d=0
  NO (9,19): second encoding NO; one Hamilton cycle in Y: none (UNSAT); counting certificate: no Hamilton cycle: T=[0, 6, 7, 8, 10, 12, 14, 16, 18, 20], a=5, b=0, d=0
  NO (10,21): second encoding NO; one Hamilton cycle in Y: none (UNSAT); counting certificate: no Hamilton cycle: T=[0, 6, 7, 8, 9, 12, 14, 16, 18, 20], a=5, b=0, d=0
slice 8360 (mode e10only) graph index 13715: min essential cut 8, S = [0, 6, 7, 8, 9, 10, 12, 14, 15, 18, 20] (|S_A| = 6, |S_B| = 5), cut edges [(0, 11), (0, 16), (1, 20), (6, 13), (7, 17), (8, 19), (9, 21), (10, 21)]
  tests: 58 SPAN (witness verified), 8 NO (both SAT encodings): [(0, 11), (0, 16), (1, 20), (6, 13), (7, 17), (8, 19), (9, 21), (10, 21)]
  NO edges are exactly the cut edges: True
  NO (0,11): second encoding NO; one Hamilton cycle in Y: exists; counting certificate: no two edge-disjoint Hamilton cycles: T=[6, 7, 8, 9, 10, 12, 14, 15, 18, 20], a=5, b=1, d=0
  NO (0,16): second encoding NO; one Hamilton cycle in Y: exists; counting certificate: no two edge-disjoint Hamilton cycles: T=[6, 7, 8, 9, 10, 12, 14, 15, 18, 20], a=5, b=1, d=0
  NO (1,20): second encoding NO; one Hamilton cycle in Y: exists; counting certificate: no two edge-disjoint Hamilton cycles: T=[0, 6, 7, 8, 9, 10, 12, 14, 15, 18], a=7, b=0, d=2
  NO (6,13): second encoding NO; one Hamilton cycle in Y: exists; counting certificate: no two edge-disjoint Hamilton cycles: T=[0, 7, 8, 9, 10, 12, 14, 15, 18, 20], a=6, b=1, d=0
  NO (7,17): second encoding NO; one Hamilton cycle in Y: exists; counting certificate: no two edge-disjoint Hamilton cycles: T=[0, 6, 8, 9, 10, 12, 14, 15, 18, 20], a=6, b=1, d=0
  NO (8,19): second encoding NO; one Hamilton cycle in Y: exists; counting certificate: no two edge-disjoint Hamilton cycles: T=[0, 6, 7, 9, 10, 12, 14, 15, 18, 20], a=6, b=1, d=0
  NO (9,21): second encoding NO; one Hamilton cycle in Y: exists; counting certificate: no two edge-disjoint Hamilton cycles: T=[0, 6, 7, 8, 10, 12, 14, 15, 18, 20], a=5, b=1, d=0
  NO (10,21): second encoding NO; one Hamilton cycle in Y: exists; counting certificate: no two edge-disjoint Hamilton cycles: T=[0, 6, 7, 8, 9, 12, 14, 15, 18, 20], a=5, b=1, d=0
```

So S6's conclusion does not hold there anyway: 22 of the 198 tests on non-E10 graphs fail.

## Coverage

- Random slices: 50 of 10,000 (0.50% of the slices), 588,094 of
  156,473,848 colored graphs (0.3758%), 38,814,204 of 10,327,273,770 tests
  (0.3758%).
- Plus the three non-random slices for counts and E10 (62,286 graphs).

## Cost

At most 3.71 core-hours: 13,368 worker wall-seconds summed from the done markers
(genbg, e10cut, spantest per slice; nice 10 on a machine at load 40-60, so this bounds the CPU used
from above). Of it, 5,263 s in e10cut; spantest's own CPU time was 5,890 s.
Validation and the max-flow sample added a few CPU-minutes. 4 workers, 09:53:28 to 10:52:26 EDT.

## Files

- `code/`: `e10cut.c`, `spantest.py`, `validate.py`, `flowsample.py`, `nonE10.py`,
  `pick_sample.py`, `run_slice.sh`, `driver.sh`, `launch.py`, `collect.py`, `report.py`.
- `data/sample_seed.txt`, `data/sample_order.txt`, `data/jobs.txt`, `data/collect.json`,
  `data/compare.md`, `data/nonE10.g6`, `data/nonE10.txt`, `data/val/`.
- `data/slices/s<r>.*`: regenerated graph6 (`.g6.gz`), genbg stderr, e10cut output (`.cut.gz`,
  one line per graph: index, min cut, |argmin|, argmin mask, edge hash), spantest summary
  (`.span.json`), NO lines (`.no`), done markers. The `.g6` and `.cut` files were gzipped after
  the report was built (gunzip before rerunning `collect.py`, `flowsample.py` or `nonE10.py`);
  `data/slices/SHA256SUMS` lists the uncompressed files.
