# quartic-subgraph lane report

> **Lead note (2026-10-04).** Written by the lane itself. Review status:
> - The two n = 12 graphs: checked by the lead (`../../LOG.md` Entry 23). pair_oracle and brute.py
>   return NOPAIR, and an independent SAT test finds no 4-regular subgraph. The census program's
>   positive control (`gen585 12 31 6 3 4`) finds exactly these two graphs.
> - The 3n - 4 column of the census is implied by S10 for n <= 13, which is reviewed separately.
> - Theory: reviewed (`../../reviews/QUARTIC-REVIEW.md`, FINAL): ACCEPT WITH FIXES, no mathematical
>   defect. Theorem 5's 1 / 12 / 58 types were reproduced exactly by independent code. Fixes,
>   applied inline and marked [review fix]: the Tutte citation (Lemma 1), one clause (Lemma 4), the
>   reduction sizes and the full sub-case statement (section 5.1). Corollary 3 is correct but follows
>   at once from Petersen's 2-factor theorem, so it is not new. P_2 is still open at that sub-case.

Question (i): does every graph with max degree <= 6, min degree >= 4 and e >= 3n - 4 contain a
4-regular subgraph? K2 ∨ C5 (n = 7, e = 16 = 3n - 5) has none, so the bound would be sharp.

Notation used throughout: for a vertex set X, the deficiency is D_X = sum over v in X of (6 - deg v),
and D = D_V = 6n - 2e. So e >= 3n - c means D <= 2c, and excess = e - (3n - 6) = 6 - D/2.

## 1. Bottom line

- **(i) holds for every n <= 13, by exhaustive enumeration (rung b).** For n = 13 the e = 35 = 3n - 4
  run is complete (none of about 4.4e9 graphs lacks a 4-regular subgraph); e >= 36 follows by
  Lemma A of the evolve lane (a direct e = 36..39 run was stopped after 48 of 100 slices, 0 found).
  This is consistent with the sms-census S10 result: a pair is a 4-regular subgraph, so S10 at n
  implies (i) at n. Our run is an independent check with a different property and a different
  program.
- **The excess-1 class does not die out after n = 10.** Exact counts of graphs with min degree
  >= 4, max degree <= 6, e = 3n - 5 and no 4-regular subgraph: n = 7: 1, 8: 2, 9: 3, 10: 11,
  **11: 0, 12: 2 (new), 13: 0**. The n <= 10 graphs are exactly the 17 known ones (isomorphism-checked).
  The two n = 12 graphs are new excess-1, min-degree-4 avoiders (no 4-regular subgraph, hence no
  pair). Both are (3,5)-tight: every proper vertex set U spans at most 3|U| - 5 edges.
- **Theory (rung a):** an exact identity for Tutte's f-factor quantity (Lemma 2) gives:
  max degree <= 6 and e >= 3n - 1 force a spanning 4-regular subgraph (Corollary 3); and a
  minimal counterexample to (i) has a Tutte barrier of one of 58 explicit parameter types, all
  "near-bipartite": |S| - |T| in {1, 2, 3}, T almost independent and saturated, almost all edges
  of T going to S. The weaker form with e >= 3n - 2 reduces to one bipartite statement (Lemma C0),
  which reduces in turn to a slightly stronger one (C1) except in one sub-case. (i) itself is not proved.

## Status log

- 03:47 Folder created; exact C search, filter and PRUNE geng built.
- 03:50 Controls passed (section 2). Census n = 7..11 done.
- 04:02 n = 12 done: (i) holds; 2 new excess-1 graphs. n = 13 started (2 workers).
- 04:46 n = 13, e = 35 done (100 of 100 slices, 3189 CPU-s): no graph without a 4-regular
  subgraph. e = 34 (excess 1) running.
- 05:37 n = 13, e = 34: 136 of 200 slices done, none found so far (machine shared with other lanes).
- 06:05 n = 13, e = 34 done (200 of 200 slices): **no excess-1 graph without a 4-regular subgraph
  at n = 13.** e = 36..39 stopped after 48 slices (0 found); totals sampled; F3 probe t = 5: 0.

## 2. Method and validation (computation)

- **Exact test** (`q4core.h`). Depth-first search for a nonempty subgraph with every degree in
  {0, 4}. A root vertex is forced in; an open vertex (in H, H-degree < 4) with the fewest
  completions is branched over every choice of its remaining H-edges among edges to non-frozen
  vertices; a vertex outside H whose available degree drops below 4 is removed. Every 4-regular
  subgraph containing the root is a branch, so the search is exact. The full test tries each root
  r with vertices < r removed.
- **Enumeration** (`geng_q4`). nauty 2.8.9 `geng` (source read from the sms-census tree, which was
  not modified; compiled by `build.sh` in this lane's scratch directory) compiled with `-DPRUNE=q4prune`. geng builds
  each graph by adding vertex n-1 to a graph that already passed PRUNE (geng.c, PRUNE notes), so
  a 4-regular subgraph of the new graph must use vertex n-1, and `q4prune` searches only with
  that root. "No 4-regular subgraph" passes to induced subgraphs, so pruning is sound and the
  output is exactly the graphs with no 4-regular subgraph within geng's bounds.
  Options: `geng_q4 -d4 -D6 n e:e res/mod`. Totals use the unmodified `geng -u -d4 -D6 n e:e`.
- **Controls, all passed:**
  - Pruned geng versus plain geng piped into the full test (`crosscheck.sh`), identical counts:
    all graphs on 8 and 9 vertices (10512 and 201680 without a 4-regular subgraph); max degree 6
    on 10 vertices (4154668 of 5203135); `-d4 -D6 10 20:30` (7503); `-d3 -D6 10 22:30` (544934);
    `-d4 -D6 11 26:33` (65612 of 8355911); and n = 7, 8, 9 windows. The `Q4FULLCHECK` build
    re-ran the full test on every output graph with no mismatch.
  - Known graphs: K5, K6, K4,4 and C9(1,2) have one; K2 ∨ C5 and all 17 known excess-1 avoiders
    have none.
  - The 6-regular counts in the census (e = 3n: 1, 1, 4, 21, 266, 7849 for n = 7..12) match the
    known numbers of 6-regular graphs (OEIS A006821).
  - Every graph reported without a 4-regular subgraph was re-decided by an independent SAT
    encoding (`validate_sat.py`, pysat CaDiCaL: x_e per edge, y_v per vertex, "at most 4" and
    "y_v implies at least 4" clauses, nonempty): all UNSAT. The n <= 10 ones were matched one to
    one, by networkx isomorphism, with the 17 graphs of `data/avoiders/k{7,8,9}_D6_m4_def10.json`
    (classes) and `lanes/evolve/data_n10_excess1_mindeg4.json`.

## 3. Census (rung b)

Graphs with min degree >= 4 and max degree <= 6, all isomorphism classes (connected or not).
Each cell: total number of graphs / number with no 4-regular subgraph.

| n | e = 3n-5 (excess 1) | 3n-4 | 3n-3 | 3n-2 | 3n-1 | 3n |
|---|---|---|---|---|---|---|
| 7 | 7 / **1** | 6 / 0 | 4 / 0 | 2 / 0 | 1 / 0 | 1 / 0 |
| 8 | 76 / **2** | 60 / 0 | 32 / 0 | 12 / 0 | 3 / 0 | 1 / 0 |
| 9 | 1,620 / **3** | 1,157 / 0 | 525 / 0 | 146 / 0 | 25 / 0 | 4 / 0 |
| 10 | 53,886 / **11** | 35,724 / 0 | 14,314 / 0 | 3,230 / 0 | 362 / 0 | 21 / 0 |
| 11 | 2,360,506 / **0** | 1,477,185 / 0 | 555,762 / 0 | 114,103 / 0 | 10,398 / 0 | 266 / 0 |
| 12 | 125,193,936 / **2** | 74,610,309 / 0 | 26,910,262 / 0 | 5,271,490 / 0 | 442,828 / 0 | 7,849 / 0 |
| 13 | ~7.7e9 (est.) / **0** | ~4.4e9 (est.) / **0** | Lemma A | Lemma A | Lemma A | Lemma A |

- n = 13 "without" counts are exact (all 200 slices of e = 34 and all 100 of e = 35; 8874 and 3189
  CPU-s). The n = 13 totals are estimates from 20 random plain-geng slices of 1000
  (`sample_totals.sh`): e = 34: 7.71e9 +- 0.21e9, e = 35: 4.43e9 +- 0.09e9 (1 s.e.). For
  e >= 36 at n = 13 the table relies on Lemma A; a direct run covered 48 of 100 slices of
  e = 36..39 and found 0.
- Per-slice logs: `out/slices_<tag>.log` (n = 12, 13) and `census.tsv` (n <= 11). Graphs without a
  4-regular subgraph: `out/q4free_n{n}_e{e}.g6` (n <= 11) and `out/found_<tag>.g6` (n >= 12).
- **(i) holds for n <= 13** (rung b): n <= 12 by the 3n-4 to 3n columns; n = 13 by the 3n-4 column
  and Lemma A (evolve lane), which reduces e > 3n - 4 to e = 3n - 4 for n >= 8. For n <= 6 (i) is
  vacuous or immediate (n = 6 needs e >= 14, and K6 minus an edge contains K5).
- To reproduce one cell: `cd lanes/quartic-subgraph && ./geng_q4 -d4 -D6 12 31:31 > x.g6` (about
  2.5 CPU-min) then `[temporary path] validate_sat.py --expect-unsat x.g6`.

## 4. New extremal graphs at n = 12 (rung b)

Saved in `data_n12_excess1_no4reg.json` (graph6 and edge lists). Both have 12 vertices, 31 edges
(3n - 5), max degree 6, min degree 4, no 4-regular subgraph (q4 search, SAT), and no pair
(`tools/pair_oracle.decide`: NOPAIR for both). Both are (3,5)-tight: brute force over all proper
U with |U| >= 2 gives max e(U) - 3|U| = -5.

- `K?r@daMZq}Fw`. Seven hubs of degree 6 forming K4,3 (A = {4,5,6,7}, B = {9,10,11}, no edges
  inside A or B); five degree-4 vertices L = {0,1,2,3,8} with one edge 0-8.
  Edges: 0-4 0-5 0-7 0-8 1-4 1-5 1-9 1-10 2-6 2-7 2-9 2-11 3-6 3-7 3-10 3-11 4-8 4-9 4-10 4-11
  5-8 5-9 5-10 5-11 6-8 6-9 6-10 6-11 7-9 7-10 7-11.
- `K?`CRbt^d{Vo`. Four independent hubs {8,9,10,11}; eight vertices 0..7 of degrees
  5,4,5,5,5,5,5,4 spanning 7 edges.
  Edges: 0-4 0-6 0-8 0-10 0-11 1-5 1-7 1-8 1-9 2-7 2-8 2-9 2-10 2-11 3-7 3-8 3-9 3-10 3-11 4-6
  4-9 4-10 4-11 5-8 5-9 5-10 5-11 6-9 6-10 6-11 7-8.
- In both, a Tutte barrier for a spanning 4-factor is T = four independent hubs sending all 24
  of their edges into S = the other 8 vertices, with e(S) = 7 and delta(S,T) = -2. This is the
  Case-0 type of section 5 at D = 10. K2 ∨ C5 instead has S = the pentagon, T = one hub, and the
  other hub as a single odd component.
- Validation: `[temporary path] validate_sat.py --expect-unsat
  out/found_n12_e31_q4.g6` (exit 0).

## 5. Theory

Throughout, G is simple with max degree <= 6. For X ⊆ V: D_X = sum_{v in X} (6 - deg v),
D = D_V = 6n - 2e, e(X) = edges inside X, e(X,Y) = edges between disjoint X and Y.
P_c is the statement "max degree <= 6, n >= 2 and e >= 3n - c imply a 4-regular subgraph".
(i) is P_4 (min degree >= 4 may be added or dropped: peeling a vertex of degree <= 3 keeps
e - 3n >= -c, and a 3-degenerate graph has e <= 3n - 6).

### Lemma 1 (Tutte's condition with f = deg - 4), rung (a)

Let min degree >= 4 and f(v) = deg(v) - 4. A spanning 4-regular subgraph is the complement of an
f-factor. Tutte's f-factor theorem ([review fix] Tutte, Canad. J. Math. 6 (1954), Theorem C; Tutte
assumes f > 0, so for f >= 0 cite the Belck/Tutte criterion as stated in Kostochka, Raspaud, Toft,
West, Zirlin, Graphs Combin. 2021, Theorem 1.4 with l = 4, or Qu-West 2023, Theorem 1.1): an f-factor exists iff
delta(S,T) = f(S) - f(T) + sum_{v in T} deg_{G-S}(v) - q(S,T) >= 0 for all disjoint S, T, where
q(S,T) counts components C of G - S - T with f(C) + e(C,T) odd; delta(S,T) ≡ f(V) (mod 2).
- Since sum_{v in T} deg_{G-S}(v) = sum_T deg - e(S,T) and sum_T deg - f(T) = 4|T|:
  **delta(S,T) = f(S) + 4|T| - e(S,T) - q(S,T)** (the task's formula, confirmed).
- Parity: f(C) + e(C,T) ≡ sum_C deg + e(C,T) = 2e(C) + e(C,S) + 2e(C,T) ≡ e(C,S). So **q(S,T)
  counts the components C with e(C,S) odd.**
- f(V) = 2e - 4n is even, so delta is even, and a barrier has delta <= -2.

I did not re-read Tutte's 1952 paper ([review fix] the reviewer did: the form is Tutte 1954 Theorem C,
the parity is Tutte 1952 Theorem I); the formula as used was checked numerically:
`identity_check.py` evaluates delta for all 3^n pairs (S,T) on 40 random graphs (n = 6..9,
degrees in [4,6]) and its verdict (min delta >= 0) matched a SAT test for a spanning 4-regular
subgraph on 40 of 40.

### Lemma 2 (budget identity), rung (a)

With s = |S|, t = |T|, R = V - S - T and its components C:

    3·delta(S,T) + 2D = 2e(S) + 4e(T) + 4D_T + sum_C w(C),
    w(C) = 2D_C + e(C,S) + 2e(C,T) - 3·[e(C,S) odd].

Proof. f(S) = 2s - D_S. Degree sums: 6t - D_T = 2e(T) + e(S,T) + e(T,R) and
6s - D_S = 2e(S) + e(S,T) + e(S,R). Substituting each into Lemma 1:
(*)  delta = 2(s - t) - D_S + D_T + 2e(T) + e(T,R) - q,
(**) delta = 4(t - s) + 2e(S) + e(S,R) - q.
Then 2(*) + (**) gives 3·delta = 2e(S) + 4e(T) + 2D_T - 2D_S + e(S,R) + 2e(T,R) - 3q; substitute
D_S = D - D_T - sum_C D_C and split e(S,R), e(T,R), q over components. ∎

Every term on the right is >= 0. For C with e(C,S) odd, the degree count
6|C| - D_C = 2e(C) + e(C,S) + e(C,T) shows D_C + e(C,T) is odd, so w(C) >= 2 + 1 - 3 = 0. For a
single vertex x with a = e(x,S): w = 12 - a - 3[a odd] >= 4. The identity was checked on every
(S,T) of the same 40 random graphs.

Also from (**): a barrier has 4(s - t) >= 2e(S) + e(S,R) - q + 2 >= 2, so **|S| > |T| always**.

### Corollary 3, rung (a)

**Max degree <= 6 and e >= 3n - 1 imply a spanning 4-regular subgraph.** Here D <= 2, so every
degree is >= 4 and 3·delta >= -2D >= -4; delta is even, so delta >= 0 for all (S,T).

[review fix] Not new: this follows at once from Petersen's 2-factor theorem. With D = 2, add the
missing edge (parallel if needed) or a loop to get a 6-regular multigraph, split it into three
2-factors, and drop the one that contains the added edge. A citable form that allows loops is
van den Heuvel-Toft, arXiv:2510.11486v2, Theorem 1.2.

Sharp for spanning subgraphs at D = 4: take T = {t1..t6}, S = {s0..s6}, ti adjacent to every sj
except si, plus the edge s1s2 (n = 13, e = 37 = 3n - 2). A spanning 4-regular H would need
4|S| - 4|T| = 2e_H(S) <= 2, impossible. It still has a 4-regular subgraph: K5,5 minus the perfect
matching {ti si}, on {t1..t5} ∪ {s1..s5}.

### Lemma 4 (minimal counterexample), rung (a)

Let c <= 4 and let G be a counterexample to P_c with n minimal, then e minimal. Then n >= 7,
min degree >= 4, e = 3n - c (so D = 2c), and **every proper U with |U| >= 2 has
D_U + e(U, V-U) >= 2c + 2**, equivalently e(G[U]) <= 3|U| - c - 1 (G[U] has no 4-regular
subgraph and is smaller). In particular, for any barrier (S, T) ([review fix]: not any G - S - T; a barrier has S nonempty),
every component C with |C| >= 2 of G - S - T has
D_C + e(C,S) + e(C,T) >= 2c + 2, so w(C) >= 2c - 1 (odd) or >= 2c + 2 (even).

### Theorem 5 (barrier types of a minimal counterexample), rung (a)

A minimal counterexample to P_c has no spanning 4-regular subgraph, so it has a barrier with
delta in {-2, -4}, and by Lemma 2: 2e(S) + 4e(T) + 4D_T + sum_C w(C) = 3·delta + 4c <= 4c - 6.
Together with (*), (**) and the w bounds this leaves finitely many parameter types
(`obstruction_types.py`, output in `out/obstruction_types.txt`):

- **c = 2: one type.** delta = -2, |S| = |T| + 1, e(S) = 1, e(T) = 0, D_T = 0, D_S = 4, R empty.
  So G = B + (one edge inside S), where B is bipartite with sides S and T, every vertex of T has
  degree 6, and |S| = |T| + 1.
- **c = 3: 12 types.** One is G bipartite with T 6-regular into S, |S| = |T| + 1 (delta = -4).
- **c = 4, that is (i): 58 types.** In all of them 1 <= |S| - |T| <= 3, e(S) <= 5,
  e(T) + D_T <= 2, e(S,T) >= 6|T| - 5, D_S >= 5 (S carries at least 5 of the 8 units of
  deficiency), and G - S - T has at most two components (single vertices, or one piece with
  w <= 10; such a piece C has e(C,S) >= 7, e(C,T) + D_C <= 3). So T is a nearly independent set of nearly saturated vertices sending almost all
  their edges to S, and G is a bipartite S-T graph plus at most 5 edges inside S, at most 2
  inside T, and at most two outside vertices or one outside piece.

Check of the enumerator's arithmetic (`types_crosscheck2.py`, sparsity switched off): every
barrier of every graph with D = 8 and no spanning 4-regular subgraph among the geng output for
n = 9 (8 graphs, 21 barriers) and the first 4 such graphs for n = 10 (28 barriers) has a listed
type. (All graphs with D = 8 at n = 8 and with D = 6 at n = 8, 9 have spanning 4-regular
subgraphs.)

This explains the extremal graphs: at D = 10 the budget is 14 instead of 10, which admits
|S| - |T| = 4 with e(S) = 7 (both n = 12 graphs) or one odd outside hub (K2 ∨ C5).

To finish (i) one must show that each of the 58 near-bipartite configurations, under the
sparsity of Lemma 4, contains a 4-regular subgraph. Section 5.1 does this for c = 2 up to one
bipartite statement.

### 5.1 The case c = 2 (e >= 3n - 2) reduced to bipartite statements, rung (a) with one gap

By Theorem 5, P_2 follows from **Lemma C0**: every bipartite graph with sides X, Y, |Y| = |X| + 1,
every X-vertex of degree 6 and max degree <= 6, has a 4-regular subgraph. Define the classes
- C_j: sides X (size m, D_X <= j) and Y (size m + 1), max degree <= 6;
- E_d: balanced (both sides of size m), max degree <= 6, deficiency <= d on each side.

**Bipartite criterion.** (Max-flow min-cut.) A balanced bipartite graph has a 4-factor iff
e(A,C) >= 4(|A| + |C| - m) for all A ⊆ P, C ⊆ Q. Writing C' = Q - C and A' = P - A, the slack is
exactly Φ(A,C') = 2|A| - 2|C'| - D_A + D_C' + e(A',C'), and Φ >= 4(|C'| - |A|). So a violation has
k = |A| - |C'| >= 1 and D_A >= 2k + 1 + ε, where ε = D_C' + e(A',C'). It splits off two pieces:
B[A ∪ C'] (C' side has deficiency ε, the other side is k larger) and B[A' ∪ C].

Proved reductions (the pieces used are nonempty; [review fix] C0 and C1 pieces have size m' < m,
while E_3 and E_4 pieces may have size m, and the induction is still well founded because E_3(m)
and E_4(m) reduce to sizes < m):
- **E_3(m) <= C0(m')**: a violation has k = 1, ε = 0, D_A = 3, and both pieces are C0
  instances.
- **E_4(m) <= C1(m')**: a violation has k = 1, ε <= 1, and both pieces are C1 instances.
- **C0(m) <= E_3 and C1(m')**: delete y0 in Y of minimum degree d0 <= 5. If d0 <= 3, B - y0 is
  in E_3. Otherwise a violation of B - y0 with k = 1 leaves B[(X - C') ∪ (Y - A)], which is
  balanced with deficiency 6 - D_A + ε <= 3; with k = 2 (forcing d0 = 5, D_A = 5, ε = 0) it
  leaves a C1 instance.
- **C1(m) <= E_4 and C1(m')**, except in one sub-case. [review fix] Stated in full: B in C1(m) with
  D_X = 1 (x1 the degree-5 vertex of X), y0 in Y of minimum degree d0, and a violation (A in
  Y - y0, C' in X) of B - y0 with k = |A| - |C'| = 2, D_A = 5 + ε (ε in {0, 1}, so d0 >= 4 + ε)
  and x1 not in C'. Then B[(X - C') ∪ (Y - A)] is a C_2 instance (its X side is Y - A, which
  contains y0, with deficiency exactly 2 and size m - |C'| - 1) **and** B[A ∪ C'] has
  |A| = |C'| + 2 with C'-side deficiency ε <= 1. Neither piece is covered by C0, C1, E_3 or E_4.
  The reviewer's partial progress on this case is in `../../reviews/QUARTIC-REVIEW.md`.

So **P_2 holds if C1 holds**, and C1 is open only in that sub-case.

**Bipartite census (rung b), computational support.** `geng_q4 -b -d4 -D6 n 3n-12:3n` lists every
bipartite graph with min degree >= 4, max degree <= 6 and no 4-regular subgraph in that edge
window. Counts by e: n <= 10 none; n = 11: e = 24 (2), 25 (1); n = 12: 25 (2), 26 (2);
n = 13: 28 (28), 29 (50), 30 (37), 31 (9); n = 14: 30 (94), 31 (108), 32 (77), 33 (11). So for
n <= 14 such bipartite graphs have at most 3n - 8 edges, while C0 and C1 instances have 3n - 3
and at least 3n - 4 edges (their 4-cores are bipartite with the same bound). Hence C0 and C1
hold for |X| <= 6. Separately, `genbg_q4 -u -d6:0 -D6:6 m m+1` (the C0 class, exactly) outputs
no graph for m = 5, 6, 7, 8 (m = 9 did not finish in 200 s); with X-degrees in [4,6] and
|Y| = |X| + 1, the least X-deficiency of a 4-regular-free graph is 5 for m = 5 and m = 6.

**Why the method stalls at c = 4.** At D = 8 the barrier pieces need not be denser than the
sparsity bound: a minimal counterexample has D_U + e(U, V-U) >= 10 > D for every proper U. So no
proper induced subgraph satisfies the hypothesis of an induction. Any 4-regular subgraph must be
found inside a near-bipartite configuration from Theorem 5 by local structure, as in the
K5,5-minus-matching example of Corollary 3. Also, Chevalley-Warning in the Alon-Friedland-Kalai
style needs more edges than sum of degrees of the mod-4 polynomials (3n over F_2), so it needs
e > 3n and cannot apply at max degree 6.

## 6. Where the excess-1 graphs come from (rung b)

Barrier types of the extremal (D = 10) graphs, computed by brute force over all (S,T) for
n <= 9 and by the structured probe below for n = 10, 12. Notation (delta, |S|-|T|, e(S), e(T), D_T).

| family | n = 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 |
|---|---|---|---|---|---|---|---|---|
| F4: (-2, 4, 7, 0, 0), R empty: t independent saturated hubs, all edges into S, |S| = t+4, e(S) = 7 | - | 2 (t=2) | - | **11 (t=3)** | - | **2 (t=4)** | - | **0 (t=5)** |
| F3: (-2, 3, 5, e(T)+D_T = 1), R empty | 1 (K2∨C5) | - | 3 | - | 0 | - | 0 | - |

- All 11 graphs at n = 10 and both at n = 12 are in F4; F4 needs n = 2t + 4 even, which is
  why n = 11 has none and n = 13 cannot have F4 graphs. K2 ∨ C5 and all three n = 9 graphs are
  in F3. The n = 8 graphs are in F4 (t = 2).
- **Structured probe** (`genbg_q4` = nauty genbg with a 4-regular-subgraph PRUNE1 hook, then
  `extend_s` adds the S-edges with incremental pruning, then `labelg` dedup):
  `./genbg_q4 -q -d6:0 -D6:6 t t+4 | ./extend_s t 7 | labelg -q | sort -u`.
  - t = 3: 11 classes, identical (canonical forms) to the n = 10 census output.
  - t = 4: 2 classes, identical to the n = 12 census output. These two checks validate the probe.
  - **t = 5 (n = 14): 331 hub bases, 7.4M search nodes, no graph.** F4 is extinct at t = 5.
  - t = 6 (n = 16): 39,513 hub bases; not run (estimated hours).
- `probe_f3.sh t` (F3 analog: genbg with T-degrees 5..6, one T-edge or one degree-5 hub, then 5
  S-edges, then a full `q4filter` pass) gives 1, 3, 0, 0 classes for t = 2, 3, 4, 5, matching
  the census at n = 7, 9, 11, 13.
- So the excess-1 class is a finite union of near-bipartite hub families at these sizes, and
  the largest family F4 grows (2, 11, 2) then stops. This is evidence, not proof, that
  e <= 3n - 6 holds for 4-regular-free graphs with max degree <= 6 for all large n.

## 7. What was tried, and open gaps

Tried:
- Exhaustive census with a PRUNE-modified geng, cross-checked against plain geng plus a filter,
  SAT, isomorphism with the known 17, and known 6-regular counts.
- Tutte's f-factor theorem with f = deg - 4, reduced to an exact identity (Lemma 2) and a
  finite list of barrier types for minimal counterexamples (Theorem 5).
- An induction on near-bipartite pieces via the bipartite (Ore, max-flow) 4-factor criterion
  (section 5.1). It closes for the balanced and unbalanced-by-one classes up to one sub-case.
- Structured enumeration of the barrier families that produce the extremal graphs (section 6).
- Chevalley-Warning in the Alon-Friedland-Kalai style: needs e > 3n, so it gives nothing at max
  degree 6 (section 5.1).

Open:
1. **(i) in general.** Not proved. A proof must show that each of the 58 barrier types of
   Theorem 5 contains a 4-regular subgraph, using the sparsity of Lemma 4. No proper induced
   subgraph is dense enough for induction (D_U + e(U, V-U) >= 10 > 8 = D), so the subgraph must
   be found inside the near-bipartite configuration.
2. **P_2 (e >= 3n - 2).** Reduced to the bipartite Lemma C0, which reduces to C1; C1 is open in
   one sub-case (section 5.1). Computationally C0 has no counterexample with |X| <= 8 (genbg
   with the PRUNE hook: `./genbg_q4 -u -d6:0 -D6:6 m m+1` outputs 0 graphs for m = 5..8).
3. **Excess 1 for large n.** The census shows 0 at n = 11, 2 at n = 12 and 0 at n = 13. Family F4
   is empty at t = 5 (n = 14), but other barrier types at D = 10 were not probed beyond n = 13.
4. The census does not cover n = 14 (estimated over 50 CPU-hours with this method).

## 8. Single most promising next step

Use Theorem 5 to drive an exact search. A minimal counterexample to (i) at order n realizes one of
the 58 barrier types: |T| saturated hubs sending all but at most 5 of their 6|T| edge-ends into S,
|S| - |T| <= 3, at most 5 edges inside S and 2 inside T, and at most two outside vertices or one
outside piece. Generate these near-bipartite structures with genbg plus small extensions, as
`probe_f3.sh` and the F4 probe already do. Both probes reproduce the census exactly at
n = 7, 9, 10, 11, 12. This should reach n near 18 to 20 in CPU-hours, where plain geng needs over
50 CPU-hours for n = 14. The 9 types with an outside piece need that piece to be a 4-regular-free
block with e(C,S) >= 7 and D_C + e(C,T) <= 3, so the search recurses there. In parallel, closing
the C1 sub-case of section 5.1 would prove e >= 3n - 2 outright.

## 9. Files (all in this folder; large outputs in `out/`)

- Search and enumeration: `q4core.h` (exact search), `q4filter.c` (graph6 filter),
  `q4prune.c` and `geng_q4` (geng PRUNE), `q4prune_bg.c` and `genbg_q4` (genbg PRUNE1),
  `extend_s.c` (adds S-edges), `build.sh`, `crosscheck.sh`, `census_small.sh`,
  `run_slices.sh`, `workerA.sh`, `workerB.sh`, `probe_f3.sh`. `geng_plain` is a copy of the
  sms-census geng binary.
- Validation: `validate_sat.py` (independent SAT decider with witness check),
  `identity_check.py` (Lemma 2 and Tutte criterion on random graphs), `types_crosscheck.py`,
  `types_crosscheck2.py`, `obstruction_types.py` (Theorem 5 enumerator; output
  `out/obstruction_types.txt`).
- Data: `census.tsv` (n <= 11), `out/slices_*.log` (n = 12, 13 per slice),
  `out/q4free_n*_e*.g6` and `out/found_*.g6` (all graphs without a 4-regular subgraph),
  `out/excess1_all17.g6`, `data_n12_excess1_no4reg.json` (the two new graphs),
  `out/ext_t{3,4,5}*.g6` and `out/f3_t*.g6` (probe outputs).

## 10. Independent checks to run, and review flag

- Every graph claimed to have no 4-regular subgraph:
  `cd lanes/quartic-subgraph && [temporary path] validate_sat.py --expect-unsat out/excess1_all17.g6 out/found_n12_e31_q4.g6`
  (exit 0). Pair check of the new graphs: `tools/pair_oracle.decide` gave NOPAIR for both.
- Census controls: `./crosscheck.sh "-d4 -D6 11 26:33"` (plain geng plus filter versus PRUNE geng).
- Lemma 2 numerics: `[temporary path] identity_check.py 40 7`.
- Note: our census counts graphs with no 4-regular subgraph. An excess-1 graph can avoid pairs
  while containing a 4-regular subgraph, so "0 at n = 11" is not a statement about all
  excess-1 avoiders.

**Review flag: independent review needed** for Lemma 2, Corollary 3 and Theorem 5 (rung a, numerically
checked here but not read by a second party), for the reductions in section 5.1, and for the
two new n = 12 graphs (validated three ways). The census numbers are reproducible with the
commands above.
