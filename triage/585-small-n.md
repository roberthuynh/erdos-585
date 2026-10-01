# Erdos 585, small n: exact f(n)

f(n) = max edges of a simple graph on n labelled vertices with no two edge-disjoint cycles (>= 3 vertices) on the same vertex set.
Produced by `triage/erdos585_small.py` (Python 3, stdlib only); each section is appended as soon as that n finishes.

- self-test n=5: 907 random (good graph, new edge) cases, incremental test agrees with the from-scratch test (0.1s)
- self-test n=6: 929 random (good graph, new edge) cases, incremental test agrees with the from-scratch test (0.3s)
- self-test n=7: 965 random (good graph, new edge) cases, incremental test agrees with the from-scratch test (0.9s)
## n = 1

- f(1) = **0** (C(1,2) = 0, gap 0); search: all extremal graphs enumerated; 0.00 s, 1 nodes, 0 incremental tests
- extremal graph (edge list): []; degrees [0]
- extremal graphs: 1 isomorphism classes (deduplicated by canonical form), 1 labelled graphs (sum of n!/|Aut|); 1 labelled representatives met under symmetry breaking
  - |Aut| = 1: []
- brute force over all 2^0 labelled graphs (from-scratch test): f = 0, 1 labelled extremal graphs, 0.00 s; MATCHES the backtracking

## n = 2

- f(2) = **1** (C(2,2) = 1, gap 0); search: all extremal graphs enumerated; 0.00 s, 1 nodes, 0 incremental tests
- extremal graph (edge list): [(0, 1)]; degrees [1, 1]
- extremal graphs: 1 isomorphism classes (deduplicated by canonical form), 1 labelled graphs (sum of n!/|Aut|); 1 labelled representatives met under symmetry breaking
  - |Aut| = 2: [(0, 1)]
- brute force over all 2^1 labelled graphs (from-scratch test): f = 1, 1 labelled extremal graphs, 0.00 s; MATCHES the backtracking

## n = 3

- f(3) = **3** (C(3,2) = 3, gap 0); search: all extremal graphs enumerated; 0.00 s, 3 nodes, 1 incremental tests
- extremal graph (edge list): [(0, 1), (0, 2), (1, 2)]; degrees [2, 2, 2]
- extremal graphs: 1 isomorphism classes (deduplicated by canonical form), 1 labelled graphs (sum of n!/|Aut|); 1 labelled representatives met under symmetry breaking
  - |Aut| = 6: [(0, 1), (0, 2), (1, 2)]
- brute force over all 2^3 labelled graphs (from-scratch test): f = 3, 1 labelled extremal graphs, 0.00 s; MATCHES the backtracking

## n = 4

- f(4) = **6** (C(4,2) = 6, gap 0); search: all extremal graphs enumerated; 0.00 s, 7 nodes, 3 incremental tests
- extremal graph (edge list): [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]; degrees [3, 3, 3, 3]
- extremal graphs: 1 isomorphism classes (deduplicated by canonical form), 1 labelled graphs (sum of n!/|Aut|); 1 labelled representatives met under symmetry breaking
  - |Aut| = 24: [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
- brute force over all 2^6 labelled graphs (from-scratch test): f = 6, 1 labelled extremal graphs, 0.00 s; MATCHES the backtracking

## n = 5

- f(5) = **9** (C(5,2) = 10, gap 1); search: all extremal graphs enumerated; 0.00 s, 20 nodes, 10 incremental tests
- extremal graph (edge list): [(0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (3, 4)]; degrees [3, 3, 4, 4, 4]
- extremal graphs: 1 isomorphism classes (deduplicated by canonical form), 10 labelled graphs (sum of n!/|Aut|); 1 labelled representatives met under symmetry breaking
  - |Aut| = 12: [(0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (3, 4)]
- brute force over all 2^10 labelled graphs (from-scratch test): f = 9, 10 labelled extremal graphs, 0.00 s; MATCHES the backtracking

## n = 6

- f(6) = **12** (C(6,2) = 15, gap 3); search: all extremal graphs enumerated; 0.01 s, 230 nodes, 110 incremental tests
- extremal graph (edge list): [(0, 1), (0, 2), (0, 5), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (2, 5), (3, 4), (3, 5), (4, 5)]; degrees [3, 4, 4, 4, 4, 5]
- extremal graphs: 3 isomorphism classes (deduplicated by canonical form), 380 labelled graphs (sum of n!/|Aut|); 9 labelled representatives met under symmetry breaking
  - |Aut| = 4: [(0, 1), (0, 2), (0, 5), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (2, 5), (3, 4), (3, 5), (4, 5)]
  - |Aut| = 4: [(0, 2), (0, 4), (0, 5), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (2, 5), (3, 4), (3, 5), (4, 5)]
  - |Aut| = 36: [(0, 3), (0, 4), (0, 5), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (2, 5), (3, 4), (3, 5), (4, 5)]
- brute force over all 2^15 labelled graphs (from-scratch test): f = 12, 380 labelled extremal graphs, 0.07 s; MATCHES the backtracking

## n = 7

- f(7) = **16** (C(7,2) = 21, gap 5); search: all extremal graphs enumerated; 0.05 s, 1137 nodes, 613 incremental tests
- extremal graph (edge list): [(0, 1), (0, 2), (0, 5), (0, 6), (1, 3), (1, 5), (1, 6), (2, 4), (2, 5), (2, 6), (3, 4), (3, 5), (3, 6), (4, 5), (4, 6), (5, 6)]; degrees [4, 4, 4, 4, 4, 6, 6]
- extremal graphs: 1 isomorphism classes (deduplicated by canonical form), 252 labelled graphs (sum of n!/|Aut|); 12 labelled representatives met under symmetry breaking
  - |Aut| = 20: [(0, 1), (0, 2), (0, 5), (0, 6), (1, 3), (1, 5), (1, 6), (2, 4), (2, 5), (2, 6), (3, 4), (3, 5), (3, 6), (4, 5), (4, 6), (5, 6)]
- top-level brute force (from-scratch test on all C(21,17) + C(21,16) labelled graphs): 0 good graphs with 17 edges, 252 good graphs with 16 edges, 11.70 s; MATCHES the backtracking
- level-wise check (good graphs up to isomorphism, one edge at a time, from-scratch test, no symmetry breaking or bound): f = 16, 1 extremal classes, 252 labelled, 14.76 s; good classes per edge count [1, 1, 2, 5, 10, 21, 41, 65, 97, 131, 147, 146, 126, 89, 50, 21, 1]; MATCHES the backtracking

## n = 8

- f(8) = **19** (C(8,2) = 28, gap 9); search: all extremal graphs enumerated; 5.62 s, 44720 nodes, 23623 incremental tests
- extremal graph (edge list): [(0, 1), (0, 4), (0, 6), (0, 7), (1, 4), (1, 6), (1, 7), (2, 3), (2, 5), (2, 6), (2, 7), (3, 5), (3, 6), (3, 7), (4, 5), (4, 6), (4, 7), (5, 6), (5, 7)]; degrees [4, 4, 4, 4, 5, 5, 6, 6]
- extremal graphs: 12 isomorphism classes (deduplicated by canonical form), 175560 labelled graphs (sum of n!/|Aut|); 396 labelled representatives met under symmetry breaking
  - |Aut| = 16: [(0, 1), (0, 4), (0, 6), (0, 7), (1, 4), (1, 6), (1, 7), (2, 3), (2, 5), (2, 6), (2, 7), (3, 5), (3, 6), (3, 7), (4, 5), (4, 6), (4, 7), (5, 6), (5, 7)]
  - |Aut| = 4: [(0, 1), (0, 2), (0, 6), (0, 7), (1, 4), (1, 6), (1, 7), (2, 5), (2, 6), (2, 7), (3, 4), (3, 5), (3, 6), (3, 7), (4, 5), (4, 6), (4, 7), (5, 6), (5, 7)]
  - |Aut| = 4: [(0, 1), (0, 2), (0, 6), (0, 7), (1, 5), (1, 6), (1, 7), (2, 5), (2, 6), (2, 7), (3, 4), (3, 5), (3, 6), (3, 7), (4, 5), (4, 6), (4, 7), (5, 7), (6, 7)]
  - |Aut| = 2: [(0, 4), (0, 5), (0, 7), (1, 2), (1, 4), (1, 6), (1, 7), (2, 5), (2, 6), (2, 7), (3, 4), (3, 5), (3, 6), (3, 7), (4, 6), (4, 7), (5, 6), (5, 7), (6, 7)]
  - |Aut| = 4: [(0, 3), (0, 4), (0, 5), (1, 3), (1, 4), (1, 6), (1, 7), (2, 3), (2, 5), (2, 6), (2, 7), (3, 6), (3, 7), (4, 5), (4, 6), (4, 7), (5, 6), (5, 7), (6, 7)]
  - |Aut| = 1: [(0, 1), (0, 3), (0, 5), (0, 7), (1, 2), (1, 6), (1, 7), (2, 4), (2, 6), (2, 7), (3, 5), (3, 6), (3, 7), (4, 5), (4, 6), (4, 7), (5, 6), (5, 7), (6, 7)]
  - |Aut| = 2: [(0, 1), (0, 2), (0, 5), (0, 7), (1, 3), (1, 6), (1, 7), (2, 4), (2, 6), (2, 7), (3, 5), (3, 6), (3, 7), (4, 5), (4, 6), (4, 7), (5, 6), (5, 7), (6, 7)]
  - |Aut| = 24: [(0, 1), (0, 2), (0, 6), (0, 7), (1, 3), (1, 6), (1, 7), (2, 4), (2, 6), (2, 7), (3, 5), (3, 6), (3, 7), (4, 5), (4, 6), (4, 7), (5, 6), (5, 7), (6, 7)]
  - |Aut| = 4: [(0, 3), (0, 4), (0, 5), (1, 2), (1, 3), (1, 6), (1, 7), (2, 4), (2, 6), (2, 7), (3, 5), (3, 6), (3, 7), (4, 5), (4, 6), (4, 7), (5, 6), (5, 7), (6, 7)]
  - |Aut| = 2: [(0, 4), (0, 5), (0, 7), (1, 2), (1, 3), (1, 6), (1, 7), (2, 4), (2, 6), (2, 7), (3, 5), (3, 6), (3, 7), (4, 5), (4, 6), (4, 7), (5, 6), (5, 7), (6, 7)]
  - |Aut| = 4: [(0, 5), (0, 6), (0, 7), (1, 2), (1, 3), (1, 6), (1, 7), (2, 4), (2, 6), (2, 7), (3, 5), (3, 6), (3, 7), (4, 5), (4, 6), (4, 7), (5, 6), (5, 7), (6, 7)]
  - |Aut| = 2: [(0, 1), (0, 2), (0, 3), (0, 7), (1, 4), (1, 6), (1, 7), (2, 5), (2, 6), (2, 7), (3, 5), (3, 6), (3, 7), (4, 5), (4, 6), (4, 7), (5, 6), (5, 7), (6, 7)]
- level-wise check (good graphs up to isomorphism, one edge at a time, from-scratch test, no symmetry breaking or bound): f = 19, 12 extremal classes, 175560 labelled, 20.22 s; good classes per edge count [1, 1, 2, 5, 11, 24, 56, 115, 221, 402, 662, 978, 1305, 1539, 1605, 1470, 1138, 695, 270, 12]; MATCHES the backtracking

## Summary

| n | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 |
|---|---|---|---|---|---|---|---|---|
| f(n) | 0 | 1 | 3 | 6 | 9 | 12 | 16 | 19 |
| C(n,2) | 0 | 1 | 3 | 6 | 10 | 15 | 21 | 28 |
| C(n,2) - f(n) | 0 | 0 | 0 | 0 | 1 | 3 | 5 | 9 |

- The constraint first bites at n = 5: two edge-disjoint cycles on the same k vertices need 2k <= C(k,2) edges, so k >= 5, and at k = 5 they use all 10 edges of K5 (the two 5-cycles of a Hamiltonian decomposition). So f(5) = 9 and K5 minus an edge is the only extremal graph up to isomorphism (10 labelled copies).
- n = 6: extremal graphs are K6 minus a triangle, minus a P4, or minus P3+K2; K6 minus a perfect matching (the octahedron, 12 edges, 4-regular) splits into two Hamiltonian 6-cycles, so it is bad.
- n = 7 and n = 8: C5 join K2 (16 edges) is the unique extremal class at n = 7; C6 join K2 (19 edges, |Aut| = 24) is one of the 12 classes at n = 8.
- Lower-bound step used as the search seed: f(n) >= f(n-1) + 2 (a new vertex of degree 2 lies only on cycles that share both of its edges). It is tight at n = 5, 6, 8, not at n = 7.  [Correction 2026-10-01: the table's own steps are 1, 2, 3, 3, 3, 4, 3; the +2 claim in this line is wrong and superseded by triage/585-n9.md.]
