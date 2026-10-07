# FLAW: the C1 port method cannot prove P_4 or P_3

Lane P4 (wave 3, step B1 of `reports/585-next/CONTINUE.md`), October 5, 2026.

## The step that fails

The C1 proof (`reports/585-next/G110/C1-PAPER.md`, Theorem 4.3, two referee ACCEPTs) ends with a
minimality-free core lemma (its Lemma 4.4): in a *sparse* C1 instance, the ports y for which G - y has
no 4-factor carry total deficiency at most 2. A minimal counterexample is sparse and has every port bad,
so it cannot exist.

The plan for P_4 (CONTINUE.md B1) was to run the same argument inside each of the 58 barrier types of a
minimal P_4 counterexample. The general-graph analog of the core lemma would be:

> (CL) Let G have maximum degree at most 6, e = 3n - c, and g(U) = 6|U| - 2e(U) >= 2c + 2 for every
> proper U with |U| >= 2 (c = 4 for P_4, c = 3 for P_3). If G has no 4-factor, then some port
> (vertex of degree at most 5) y has a 4-factor in G - y.

(CL) is false for c = 4 and for c = 3, and even the stronger hypothesis "G - y has no 4-factor for
*every* vertex y" is consistent with sparsity. So no argument that uses only sparsity, the absence of a
4-factor in G, and the absence of a 4-factor in every G - y can reach P_4 or P_3.

## Failing cases (all verified twice: exact DFS in `checks/deep.c`, and SAT with an own encoding plus
brute-force sparsity in `checks/check_deep.py`, output `checks/data/out_deep.json`)

| Class | n | e | graph6 | What holds |
|---|---|---|---|---|
| P_4 | 9 | 23 | `HCXf~z{` | sparse (proper U span <= 3\|U\| - 5); no 4-factor in G or in any G - y |
| P_4 | 11 | 29 | `JCOfuzsnCf_` | same |
| P_4 | 12 | 32 | `K?AFfrw^Fw^_`, `K?AFbx{^Fw^_`, `K?ABvbw~Fw^_`, `K?ABrrw~Fw^_`, `K?ABvrw\|Fw^_`, `K?ABvrw^Fw^_`, `K?AFvrw^Bw^_`, `K?AFvrs}Bw^_`, `K?B@nrw}Fw^O` | same (these are all such graphs at n = 12) |
| P_3 | 12 | 33 | `K?ABvrw~Fw^_`, `K?AFvrw^Fw^_` | sparse (proper U span <= 3\|U\| - 4); no 4-factor in G or in any G - y |
| QB(5) | 15 | 40 | `N???FbKickNo^_^_No?`, `N???FaM{C[No^_^_No?`, `N???FaMyCkNo^_^_No?` | bipartite, sides 7 and 8, proper U with \|U\| >= 3 span <= 3\|U\| - 6; every port y has no 4-factor in B - y |

Each graph does contain a 4-regular subgraph on fewer vertices (SAT witness in `out_deep.json`), as it
must: P_4 and P_3 hold for n <= 13 by the census.

The smallest case by hand. `HCXf~z{` is the join of an independent set T = {6, 7, 8} with the graph
F = K2 + C4 on S = {0, ..., 5} (edges 03, 14, 15, 24, 25). It has 18 + 5 = 23 = 3n - 4 edges and degrees
4, 4, 5, 5, 5, 5, 6, 6, 6. Barriers (delta(S', T') = 4(|T'| - |S'|) + 2e(S') + e(S', R) - q <= -2):
- G: (S, T) gives 4(3 - 6) + 10 = -2.
- G - 0 and G - 3: the other end of the edge 03 has degree 3; ({3}, {}) gives -4 + 3 - 1 = -2.
- G - y for y in {1, 2, 4, 5}: (S - y, T) gives 4(3 - 5) + 2 * 3 = -2.
- G - y for y in T: (S, T - y) gives 4(2 - 6) + 10 = -6.
Sparsity by hand: a set U with i vertices in S and j in T spans e_F(U_S) + ij edges, and the maximum of
e_F over i-subsets of S is 0, 1, 2, 4, 4, 5 for i = 1..6, which gives e(U) <= 3(i + j) - 5 for every
proper U with i + j >= 2. Its 4-regular subgraphs avoid at least two vertices: G - y - z has a 4-factor for five pairs {y, z},
and the octahedron on {1, 2, 4, 5, 6, 7} avoids three.

## Why it fails (Lemma 2.2 of PAPER.md)

For a barrier (S, T) of G - Y with Q = V - S - T, delta = -(ex + e(S, Y) + q), where
ex = 4(|S| - |T|) - 2e(S) - e(S, Q) and q counts odd components of G[Q - Y]. The C1 rigidity comes only
from barriers with ex >= 1 (in a bipartite graph the flow criterion always supplies one). In a general
graph the obstruction can be carried entirely by e(S, Y) (a neighbor of y dropping to degree 3, or y
adjacent to S) and by the parity count q; for P_3, every barrier of G - y - z with y, z ports has
ex <= 0 (PAPER.md Corollary 2.4), so the rigid case never occurs there at all.

## Status

Main approach: failed, with the certificates above. One repair was attempted (barrier-type reductions
plus gluing across tight sets); it is recorded with its exact residual in `PAPER.md`.
