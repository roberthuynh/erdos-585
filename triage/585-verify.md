# Erdos 585, small n: independent check of f(7) = 16 and f(8) = 19

Written from scratch in `triage/erdos585_verify.py` (Python 3 standard library only). `triage/erdos585_small.py` was not imported, copied or consulted for its search code.
Definitions as in `585-small-n.md`: a graph is **bad** if it has two edge-disjoint cycles (simple, >= 3 vertices) on the same vertex set, **good** otherwise. Adding edges keeps a bad graph bad, so f(n) = m holds exactly when some m-edge graph is good (lower bound) and every (m+1)-edge graph is bad (upper bound).

Method:
- Checker: DFS from the minimum vertex s of each cycle through vertices > s (vertex and edge bitmasks), closing back to s only when the last vertex exceeds the second, so each cycle appears once; cycles are grouped by vertex-set mask and a pair is two disjoint edge masks in one group.
- Every bad verdict carries a witness that a separate routine re-checks: both edge sets lie in G, are disjoint, and are each 2-regular and connected on exactly the shared vertex set.
- Brute-force cross-check: every vertex subset S and every cyclic order of S (min(S) first, one direction), then an all-pairs test (literal over the whole cycle list for n <= 7 random tests and the Petersen graph, within vertex-set buckets for n = 8 and the reported lists).
- Isomorphism reduction: colour refinement from degrees, then the minimum edge mask over all relabellings that keep the colour classes in colour order; the number of relabellings that reach the minimum is |Aut|. Class lists are cross-checked by sum n!/|Aut| = number of labelled graphs and against OEIS A008406.
- Times are wall-clock seconds, CPython 3.14.7, one core.

Sections are appended as each step finishes.

## 1. Self-tests

- K5 has a pair: **PASS**; witness 0-3-1-2-4-0 and 0-1-4-3-2-0
- K5 minus an edge has no pair (DFS and brute force): **PASS**
- K6 minus a perfect matching (octahedron) has a pair of Hamiltonian cycles: **PASS**; witness 0-3-4-2-1-5-0 and 0-2-5-3-1-4-0; brute force finds no pair on fewer than 6 vertices
- Petersen graph: DFS cycle list equals the brute-force list: **PASS**; 57 cycles
- Petersen graph (report): cycles by length 5: 12, 6: 10, 8: 15, 9: 20, 57 total; pair: none (DFS), none (brute force); expected none, since it is 3-regular and a pair on S needs degree >= 4 inside S; 0.25 s
- random graphs, DFS checker vs brute force (literal all-pairs for n <= 7, bucketed all-pairs for n = 8): **PASS**; 1.4 s
  - n = 4: 60 graphs (60 good, 0 bad); cycle lists equal 60/60, verdicts agree 60/60, witnesses valid 60/60
  - n = 5: 200 graphs (162 good, 38 bad); cycle lists equal 200/200, verdicts agree 200/200, witnesses valid 200/200
  - n = 6: 200 graphs (135 good, 65 bad); cycle lists equal 200/200, verdicts agree 200/200, witnesses valid 200/200
  - n = 7: 150 graphs (68 good, 82 bad); cycle lists equal 150/150, verdicts agree 150/150, witnesses valid 150/150
  - n = 8: 80 graphs (36 good, 44 bad); cycle lists equal 80/80, verdicts agree 80/80, witnesses valid 80/80
- canonical form invariant under random relabelling: **PASS**; 160/160 graphs on 6-8 vertices
- |Aut| from canon equals brute force over all n! permutations: **PASS**; 126/126 graphs; 1.6 s
- self-test total 3.3 s; overall **PASS**

## 2. Lower bounds: the edge lists in 585-small-n.md

- n = 7: 2 list(s) parsed (1 |Aut| lines); all have 16 edges and are good by both checkers: **yes**; |Aut| lines pairwise non-isomorphic: yes (1 classes, reported 1); sum 7!/|Aut| = 252 (reported 252); reported |Aut| all match: yes
  - edge-list line: 16 edges, good by DFS, good by brute force; |Aut| = 20
  - |Aut| line: 16 edges, good by DFS, good by brute force; |Aut| = 20 (reported 20, match)
  - C5 join K2 built here: 16 edges, good, |Aut| = 20, isomorphic to a reported class: yes
- n = 8: 13 list(s) parsed (12 |Aut| lines); all have 19 edges and are good by both checkers: **yes**; |Aut| lines pairwise non-isomorphic: yes (12 classes, reported 12); sum 8!/|Aut| = 175560 (reported 175560); reported |Aut| all match: yes
  - edge-list line: 19 edges, good by DFS, good by brute force; |Aut| = 16
  - |Aut| line: 19 edges, good by DFS, good by brute force; |Aut| = 16 (reported 16, match)
  - |Aut| line: 19 edges, good by DFS, good by brute force; |Aut| = 4 (reported 4, match)
  - |Aut| line: 19 edges, good by DFS, good by brute force; |Aut| = 4 (reported 4, match)
  - |Aut| line: 19 edges, good by DFS, good by brute force; |Aut| = 2 (reported 2, match)
  - |Aut| line: 19 edges, good by DFS, good by brute force; |Aut| = 4 (reported 4, match)
  - |Aut| line: 19 edges, good by DFS, good by brute force; |Aut| = 1 (reported 1, match)
  - |Aut| line: 19 edges, good by DFS, good by brute force; |Aut| = 2 (reported 2, match)
  - |Aut| line: 19 edges, good by DFS, good by brute force; |Aut| = 24 (reported 24, match)
  - |Aut| line: 19 edges, good by DFS, good by brute force; |Aut| = 4 (reported 4, match)
  - |Aut| line: 19 edges, good by DFS, good by brute force; |Aut| = 2 (reported 2, match)
  - |Aut| line: 19 edges, good by DFS, good by brute force; |Aut| = 4 (reported 4, match)
  - |Aut| line: 19 edges, good by DFS, good by brute force; |Aut| = 2 (reported 2, match)
  - C6 join K2 built here: 19 edges, good, |Aut| = 24, isomorphic to a reported class: yes
- lower-bound step 0.1 s

## 3. Upper bound n = 7: every 17-edge graph is bad

- enumerated all C(21,4) = 5985 labelled 4-edge sets (5985 seen); canonical forms give 10 isomorphism classes (OEIS A008406: 10); every class has exactly 7!/|Aut| labelled members: yes; 0.23 s
  - complement of [(1, 6), (2, 6), (3, 5), (4, 5)] (|Aut| 8, 630 labelled): bad, witness verified, pair on 7 vertices: 0-5-1-3-2-4-6-0 and 0-3-6-5-2-1-4-0
  - complement of [(3, 5), (3, 6), (4, 5), (4, 6)] (|Aut| 48, 105 labelled): bad, witness verified, pair on 7 vertices: 0-4-1-3-2-5-6-0 and 0-3-4-2-6-1-5-0
  - complement of [(1, 2), (3, 6), (4, 5), (5, 6)] (|Aut| 4, 1260 labelled): bad, witness verified, pair on 7 vertices: 0-5-1-3-2-4-6-0 and 0-3-5-2-6-1-4-0
  - complement of [(0, 3), (1, 2), (4, 6), (5, 6)] (|Aut| 16, 315 labelled): bad, witness verified, pair on 7 vertices: 0-5-4-2-3-1-6-0 and 0-2-6-3-5-1-4-0
  - complement of [(2, 5), (3, 4), (4, 6), (5, 6)] (|Aut| 4, 1260 labelled): bad, witness verified, pair on 7 vertices: 0-4-5-3-2-1-6-0 and 0-3-6-2-4-1-5-0
  - complement of [(1, 2), (3, 6), (4, 6), (5, 6)] (|Aut| 12, 420 labelled): bad, witness verified, pair on 5 vertices: 0-4-2-3-5-0 and 0-2-5-4-3-0
  - complement of [(2, 5), (3, 6), (4, 6), (5, 6)] (|Aut| 4, 1260 labelled): bad, witness verified, pair on 6 vertices: 0-4-1-2-3-5-0 and 0-2-4-5-1-3-0
  - complement of [(2, 6), (3, 6), (4, 6), (5, 6)] (|Aut| 48, 105 labelled): bad, witness verified, pair on 5 vertices: 0-4-2-3-5-0 and 0-2-5-4-3-0
  - complement of [(2, 3), (4, 5), (4, 6), (5, 6)] (|Aut| 24, 210 labelled): bad, witness verified, pair on 7 vertices: 0-5-3-4-2-1-6-0 and 0-3-6-2-5-1-4-0
  - complement of [(3, 6), (4, 5), (4, 6), (5, 6)] (|Aut| 12, 420 labelled): bad, witness verified, pair on 6 vertices: 0-3-4-2-1-5-0 and 0-2-5-3-1-4-0
- class check: 10/10 complements bad with verified witnesses; 0.00 s
- labelled cross-check with no isomorphism reduction: 5985/5985 labelled 17-edge graphs bad with verified witnesses; 0.95 s
- upper bound n = 7 (f(7) <= 16): **confirmed**; step 1.2 s

## 4. Upper bound n = 8: every 20-edge graph is bad
- progress n = 8, level 1 edges: 1 classes from 28 extensions; sum 8!/|Aut| = 28 vs C(28,1) = 28 (match); 0.05 s
- progress n = 8, level 2 edges: 2 classes from 27 extensions; sum 8!/|Aut| = 378 vs C(28,2) = 378 (match); 0.01 s
- progress n = 8, level 3 edges: 5 classes from 52 extensions; sum 8!/|Aut| = 3276 vs C(28,3) = 3276 (match); 0.02 s
- progress n = 8, level 4 edges: 11 classes from 125 extensions; sum 8!/|Aut| = 20475 vs C(28,4) = 20475 (match); 0.05 s
- progress n = 8, level 5 edges: 24 classes from 264 extensions; sum 8!/|Aut| = 98280 vs C(28,5) = 98280 (match); 0.02 s
- progress n = 8, level 6 edges: 56 classes from 552 extensions; sum 8!/|Aut| = 376740 vs C(28,6) = 376740 (match); 0.04 s
- progress n = 8, level 7 edges: 115 classes from 1232 extensions; sum 8!/|Aut| = 1184040 vs C(28,7) = 1184040 (match); 0.09 s
- progress n = 8, level 8 edges: 221 classes from 2415 extensions; sum 8!/|Aut| = 3108105 vs C(28,8) = 3108105 (match); 0.29 s
- 8-edge graphs on 8 vertices up to isomorphism: 221 classes (OEIS A008406: 221); sum 8!/|Aut| = 3108105 vs C(28,8) = 3108105: match
- class check: 221/221 complements (20 edges) bad with verified witnesses; witness vertex-set sizes 5: 19, 6: 49, 7: 69, 8: 84; 0.07 s
- random labelled sample: 3000/3000 random 20-edge labelled graphs bad with verified witnesses; 1.25 s
- upper bound n = 8 (f(8) <= 19): **confirmed**; this run 1.9 s (level generation times in the progress lines above)

## 5. Extremal graphs n = 7 (16 edges)

- 5-edge graphs on 7 vertices: 21 classes from all 20349 labelled sets (OEIS A008406: 21), orbit sizes 7!/|Aut|: yes
- good 16-edge classes: 1, 252 labelled (sum 7!/|Aut|); all other complements bad with verified witnesses: yes; same class set as 585-small-n.md: yes; 3.99 s
  - good: complement of [(2, 5), (2, 6), (3, 4), (3, 6), (4, 5)], |Aut| = 20
- labelled cross-check: 252 of 20349 labelled 16-edge graphs are good (reported 252); every bad one has a verified witness: yes; 14.09 s

## 6. Extremal graphs n = 8 (19 edges)
- progress n = 8, level 9 edges: 402 classes from 4420 extensions; sum 8!/|Aut| = 6906900 vs C(28,9) = 6906900 (match); 1.14 s
- 9-edge graphs on 8 vertices: 402 classes (OEIS A008406: 402); sum 8!/|Aut| = 6906900 vs C(28,9) = 6906900: match
- good 19-edge classes: 12 (brute force agrees on 12), 175560 labelled (sum 8!/|Aut|); all other complements bad with verified witnesses: yes; same class set as the 12 lists in 585-small-n.md: yes; 0.99 s
  - good: complement of [(2, 5), (2, 6), (2, 7), (3, 4), (3, 6), (3, 7), (4, 5), (4, 7), (5, 6)], |Aut| = 24
  - good: complement of [(0, 1), (2, 6), (2, 7), (3, 4), (3, 5), (4, 6), (4, 7), (5, 6), (5, 7)], |Aut| = 16
  - good: complement of [(1, 3), (2, 4), (2, 5), (3, 6), (3, 7), (4, 5), (4, 7), (5, 6), (6, 7)], |Aut| = 2
  - good: complement of [(0, 7), (1, 7), (2, 3), (2, 6), (3, 5), (4, 5), (4, 6), (5, 7), (6, 7)], |Aut| = 4
  - good: complement of [(0, 7), (1, 7), (2, 3), (2, 4), (3, 6), (4, 5), (5, 6), (5, 7), (6, 7)], |Aut| = 4
  - good: complement of [(0, 1), (2, 4), (2, 6), (3, 4), (3, 5), (4, 7), (5, 6), (5, 7), (6, 7)], |Aut| = 4
  - good: complement of [(1, 7), (2, 4), (2, 6), (3, 4), (3, 5), (4, 7), (5, 6), (5, 7), (6, 7)], |Aut| = 2
  - good: complement of [(1, 3), (2, 4), (2, 5), (3, 4), (3, 6), (4, 7), (5, 6), (5, 7), (6, 7)], |Aut| = 1
  - good: complement of [(2, 3), (2, 4), (3, 6), (3, 7), (4, 5), (4, 7), (5, 6), (5, 7), (6, 7)], |Aut| = 4
  - good: complement of [(1, 7), (2, 3), (2, 5), (3, 4), (4, 6), (4, 7), (5, 6), (5, 7), (6, 7)], |Aut| = 2
  - good: complement of [(1, 3), (2, 3), (2, 4), (3, 5), (4, 6), (4, 7), (5, 6), (5, 7), (6, 7)], |Aut| = 2
  - good: complement of [(1, 2), (2, 3), (3, 4), (3, 5), (4, 6), (4, 7), (5, 6), (5, 7), (6, 7)], |Aut| = 4

## 7. Labelled cross-check n = 8: all C(28,8) = 3,108,105 labelled 20-edge graphs, no isomorphism reduction
- progress: 13/231 prefix tasks done, 978405 of 3108105 labelled graphs checked (2129700 remaining), 978405 bad with verified witnesses; this chunk 218.5 s on 16 processes; rerun `labelled8` to resume
- 8662 prefix tasks, 3108105 labelled 20-edge graphs checked (C(28,8) = 3108105); bad with verified witnesses: 3108105; graphs not shown bad: 0; last chunk 183.8 s on 16 processes
- labelled cross-check n = 8 (f(8) <= 19 without the canonical form): **confirmed**

## Status

| n | claim | lower bound: reported good graph(s) re-checked | upper bound: all (claim+1)-edge graphs bad | classes checked | status |
|---|---|---|---|---|---|
| 7 | f(7) = 16 | yes | yes | 10 classes of 4-edge complements, plus all 5,985 labelled | **f(7) = 16 confirmed** |
| 8 | f(8) = 19 | yes | yes | 221 classes of 8-edge complements, plus all 3,108,105 labelled | **f(8) = 19 confirmed** |

- extremal class counts: n = 7: 1 good 16-edge class(es), 252 labelled (reported 1 and 252); n = 8: 12 good 19-edge classes, 175560 labelled (reported 12 and 175560)
- self-tests: PASS
- discrepancies with 585-small-n.md: none; f(7) = 16, f(8) = 19, the extremal class counts (1 and 12), labelled counts (252 and 175560) and every reported |Aut| reproduce
- step times (s): self-test 3.31, lower 0.07, upper7 1.19, upper8 1.91 (class check 0.07), extremal7 18.09, extremal8 2.13; labelled8 about 400 s over two chunks on 16 processes of a shared, heavily loaded machine
