# P_4 and P_3 for general graphs: where the C1 method stops (residual record)

Author lane P4, wave 3 of pass 3 (step B1 of `reports/585-next/CONTINUE.md`), October 5, 2026.
Status: frozen residual record (SHA-256 in `FROZEN.sha256`). Not reviewed. No Lean, no `check.sh`, so
nothing here is a project-oracle PASS. Rungs: (a) for the lemmas and reductions of §2 and §4-§5,
(b) for the counter-instances and computations of §3 and Appendix A.

## 0. Results at a glance

**P_4 is not proved, and neither is the fallback P_3.** The main approach fails for a reason that
can be certified, and one repair was carried out; this file records both and the exact residual.

| Item | Statement | Verdict | Where |
|---|---|---|---|
| Lemma 2.1 | partition identity: g(Q) = 2D − D_Q − e(T,Q) − 3ex − 2e(S) − 4e(T) − 4D_T | proved, checked on 937,659 partitions | §2 |
| Lemma 2.2 | a barrier of G − Y has ex + e(S,Y) + q ≥ 2 | proved | §2 |
| Cor 2.3 | rigid barriers at a port (ex ≥ 1): exact structure for P_3 and P_4 | proved | §2 |
| Cor 2.4 | P_3: a port of degree 4, or two ports, never has a rigid barrier | proved | §2 |
| Thm 3.1 | the general-graph analog of C1's core lemma is false for P_4 and P_3; for QB(5) it is false at ports | certified by two independent deciders | §3, `FLAW.md` |
| Thm 4.2 | gluing across a tight set: a cut of size c + 2 + a (a ≤ 2) has no matching of size 4 + a | proved | §4 |
| Thm 5.2 | P_3: no barrier of types 1, 4, 7, 9, 12; types 5, 6 give type 3; 2 ↔ 8; types 10, 11 only with small cut matchings | proved | §5 |
| Thm 5.3 | P_4: no barrier of types 31, 51, 54, 57; types 41, 42 only with small cut matchings | proved | §5 |
| Cor 5.4 | QB(7) ⟹ P_3; QB(7) leaves P_4 only at 14 types; QB(8) is false | proved (conditional) | §5 |
| Census | no minimal counterexample to P_4 with n ≤ 13, nor to P_3 with n ≤ 12 (sparsity + quartic pruning) | computed | App. A |

The residual (§6): P_3 is open exactly at barrier types 2, 3, 10, 11 (with the restrictions of
Theorem 5.2); P_4 at 52 of its 58 types, and at 41, 42 with small cut matchings.

**Where a referee should attack first.**
1. Lemma 2.1 and its use in Corollaries 2.3 and 2.4 (all signs, and the claim S ≠ ∅).
2. Theorem 3.1: the hand verification of the n = 9 graph in `FLAW.md`, and whether the stated
   hypotheses really are everything the C1 core lemma used.
3. Lemma 4.1 and Theorem 4.2: simplicity and Δ ≤ 6 of the glued instances, the order count, and
   vertex-disjointness of the two halves.
4. Proposition 5.1 and the type tables: the deletion-number formula, the move computations of
   Theorem 5.2(b), and the type-number conventions (order of `out/obstruction_types.txt`).
5. Corollary 5.4(a): that every P_3 type has deletion number ≤ 7 with at least 4 vertices left.

## 1. Setting, notation, tools

All graphs are finite and simple. For X, Y ⊆ V disjoint: e(X) edges inside X, e(X,Y) edges between,
∂X = e(X, V − X), D_X = Σ_{v∈X} (6 − deg v), g(X) = 6|X| − 2e(X). A *port* is a vertex of degree at
most 5. Summing degrees over X gives, for every graph,

    g(X) = D_X + ∂X.                                                        (1.1)

**P_c** (REPORT.md line 136): every graph with Δ ≤ 6, n ≥ 2 and e ≥ 3n − c has a nonempty 4-regular
subgraph. **QB(m)** (this file): every *bipartite* graph with Δ ≤ 6, n ≥ 4 and e ≥ 3n − m has one.
QB(4) holds even with n ≥ 2 (C1-PAPER Corollary 5.3).

**4-factor criterion** (Belck, Tutte; Kostochka–Raspaud–Toft–West–Zirlin, Graphs Combin. 2021,
Theorem 1.4 with ℓ = 4 and the names S, T exchanged, as quoted in QUARTIC-REVIEW.md lines 64-71). A graph
G has a 4-factor (spanning 4-regular subgraph) iff for all disjoint S, T ⊆ V

    δ_G(S,T) = 4(|T| − |S|) + 2e(S) + e(S,R) − q_G(S,T) ≥ 0,

where R = V − S − T and q_G(S,T) is the number of components C of G[R] with e(C,S) odd. No degree
condition is needed (the statement is for multigraphs and ℓ-factors). δ is even: q ≡ Σ_C e(C,S) =
e(S,R) (mod 2). A pair with δ ≤ −2 is a *barrier*. For a barrier, q ≤ e(S,R) gives 4(|S| − |T|) ≥ 2,
so S ≠ ∅.

**Minimal counterexample** (REPORT.md Lemma 4, lines 196-204, reviewed: QUARTIC-REVIEW.md lines
82-104). For c ≤ 4, a counterexample to P_c with n minimal, then e minimal, has n ≥ 7, δ ≥ 4,
e = 3n − c (so D_V = g(V) = 2c), and

    g(U) ≥ 2c + 2 for every U with 2 ≤ |U| ≤ n − 1                          (sparsity)

because G[U] has no 4-regular subgraph and fewer vertices. Call such a set U *tight* if
g(U) = 2c + 2.

**Barrier types** (REPORT.md Theorem 5, lines 205-221; reproduced exactly by independent code,
QUARTIC-REVIEW.md lines 105-121). A minimal counterexample to P_c has a barrier with δ ∈ {−2, −4} whose
tuple (δ, s − t, e(S), e(T), D_T, D_S, components of G[R] with their (D_C, e(C,S), e(C,T))) is one of
12 types for c = 3 and 58 for c = 4. Type numbers here are the positions in
`reports/585-fable-wildcard/lanes/quartic-subgraph/out/obstruction_types.txt` (P_3 block, P_4 block),
reproduced in `checks/data/type_table.txt`. A component with |C| ≥ 2 is a *piece*.

**Proved tools used** (`reports/585-next/G110/C1-PAPER.md`, accepted by two independent referees,
`C1-REVIEW.md` and `C1-CORRECTIONS.md`): C1 (Theorem 4.3: a bipartite graph with sides s and s + 1,
Δ ≤ 6 and deficiency at most 1 on the smaller side has a 4-regular subgraph), hence C0, E4
(Corollary 5.2), QB(4) (Corollary 5.3) and P_2 (Corollary 5.4).

## 2. Identities for barriers of G − Y

**Lemma 2.1 (partition identity).** Let G be a graph, D = D_V, and V = S ⊔ T ⊔ Q, s = |S|, t = |T|.
Put ex = 4(s − t) − 2e(S) − e(S,Q). Then

    (a) D_S = 2(s − t) + D_T + 2e(T) + e(T,Q) + ex,
    (b) D_Q + e(T,Q) = D − 2(s − t) − 2D_T − 2e(T) − ex,
    (c) g(Q) = D + 2(s − t) − 2ex − 2e(S) − 2e(T) − 2D_T,
    (d) g(Q) = 2D − D_Q − e(T,Q) − 3ex − 2e(S) − 4e(T) − 4D_T.

*Proof.* Degree sums: 6s − D_S = 2e(S) + e(S,T) + e(S,Q) and 6t − D_T = 2e(T) + e(S,T) + e(T,Q).
Subtract and substitute e(S,Q) = 4(s − t) − 2e(S) − ex:
6(s − t) − D_S + D_T = 4(s − t) − ex − 2e(T) − e(T,Q), which is (a). D_Q = D − D_S − D_T gives (b).
By (1.1), g(Q) = D_Q + e(Q,S) + e(Q,T); insert (b) and e(S,Q): g(Q) = D − 2(s − t) − 2D_T − 2e(T) − ex
+ 4(s − t) − 2e(S) − ex, which is (c). Solving (b) for 2(s − t) and inserting it in (c) gives (d). ∎

For a bipartite G with S = A ⊆ W, T = C ⊆ U this is C1-PAPER Lemma 3.1 (there ex = −σ).

**Lemma 2.2 (barriers of G − Y).** Let Y ⊆ V and let S, T be disjoint subsets of V − Y; put
Q = V − S − T ⊇ Y and let q be the number of components of G[Q − Y] with an odd number of edges to S.
Then δ_{G−Y}(S,T) = −(ex + e(S,Y) + q), with ex computed in G as in Lemma 2.1. Hence (S,T) is a barrier
of G − Y iff ex + e(S,Y) + q ≥ 2.

*Proof.* δ_{G−Y}(S,T) = 4(t − s) + 2e(S) + e(S, Q − Y) − q and e(S,Q) = e(S, Q − Y) + e(S,Y). ∎

So a barrier of G − Y is carried by three terms: the "flow" term ex (the only one present in a
bipartite flow violation, where ex = −σ ≥ 1), the edges from S to the deleted set, and parity.

**Corollary 2.3 (rigid barriers at a port).** Let G be a minimal counterexample to P_c, c ∈ {3, 4},
y a port, (S,T) a barrier of G − y with Q = V − S − T, |Q| ≥ 2, and suppose ex ≥ 1.
- (c = 3) Then ex = 1, deg y = 5, D_{Q−y} = 0, e(T,Q) = e(S) = e(T) = D_T = 0, s − t = 2,
  e(S,Q) = 7, g(Q) = 8 and D_S = 5. Moreover (S,T) is a barrier of G of type 11 with piece Q.
- (c = 4) Then ex = 1, e(T) = D_T = 0, and either (i) s − t = 2, e(S) = 0, D_Q + e(T,Q) = 3,
  g(Q) = 10 (the C1 petal shape), or (ii) s − t = 3, D_Q = D_y = 1, e(T,Q) = 0, e(S) ≤ 1,
  g(Q) = 12 − 2e(S).

*Proof.* S ≠ ∅ (§1), so Q is a proper subset with |Q| ≥ 2 and sparsity gives g(Q) ≥ 2c + 2. With
D = 2c, Lemma 2.1(d) becomes

    D_Q + e(T,Q) + 3ex + 2e(S) + 4e(T) + 4D_T ≤ 2c − 2,                      (2.1)

where D_Q ≥ D_y ≥ 1 and ex ≥ 1.
c = 3: the left side is at least 1 + 3 = 4 = 2c − 2, so equality holds termwise: D_Q = 1, ex = 1,
e(T,Q) = e(S) = e(T) = D_T = 0. Then D_y = 1, deg y = 5, D_{Q−y} = 0. Lemma 2.1(b): 1 = 6 − 2(s − t) − 1,
so s − t = 2; e(S,Q) = 8 − 0 − 1 = 7; D_S = 6 − 1 − 0 = 5; (d) gives g(Q) = 8. In G,
δ_G(S,T) = −8 + 0 + 7 − q_G = −1 − q_G is even, so q_G is odd and δ_G ≤ −2. By the budget identity
(REPORT.md Lemma 2, lines 160-180) 3δ_G + 12 = 2e(S) + 4e(T) + 4D_T + Σ_C w(C) = Σ_C w(C) over the
components C of G[Q], where w(C) = 2D_C + e(C,S) + 2e(C,T) − 3[e(C,S) odd] and here e(C,T) = 0,
Σ D_C = 1, Σ e(C,S) = 7. A singleton x has D_x = 6 − e(x,S) ≤ 1, so e(x,S) ∈ {5, 6} and w ∈ {4, 6};
a piece has w ≥ 2c = 6 (REPORT.md Lemma 4 with QUARTIC-REVIEW.md lines 99-104). As Σ w ≤ 3(−2) + 12 = 6
and Σ e(C,S) = 7 > 6, G[Q] is a single piece with w = 2 + 7 − 3 = 6 and δ_G = −2: type 11.
c = 4: (2.1) with ex ≥ 2 would need the rest ≤ 0 while D_Q ≥ 1; so ex = 1 and
D_Q + e(T,Q) + 2e(S) + 4e(T) + 4D_T ≤ 3, giving e(T) = D_T = 0, e(S) ≤ 1. Lemma 2.1(b):
D_Q + e(T,Q) = 7 − 2(s − t), which is odd, so it is 3 (s − t = 2, then e(S) = 0 and (d) gives
g(Q) = 10) or 1 (s − t = 3, D_Q = D_y = 1, e(T,Q) = 0, g(Q) = 12 − 2e(S)). ∎

**Corollary 2.4 (no rigid barriers after deleting enough deficiency).** Let G be a minimal
counterexample to P_c, c ∈ {3, 4}, Y a set of ports with D_Y ≥ 2c − 4, and (S,T) a barrier of G − Y with
|Q| ≥ 2. Then ex ≤ 0, so e(S,Y) + q ≥ 2. For P_3 this covers every port of degree 4 and every pair of
ports; for P_4, any set of ports with total deficiency at least 4.

*Proof.* In (2.1), D_Q ≥ D_Y ≥ 2c − 4 leaves 3ex ≤ 2. ∎

So for P_3, after two ports are deleted every remaining obstruction is an adjacency or parity
obstruction, and the C1 rigidity gives no information at all.

## 3. The port method cannot reach P_3 or P_4

The C1 core lemma (C1-PAPER Lemma 4.4) is minimality-free: it uses only sparsity and, for each port y,
that G − y has no 4-factor. Its general-graph analog fails.

**Theorem 3.1 (counter-instances).**
(a) There are graphs with Δ ≤ 6, δ ≥ 4, e = 3n − 4, sparse for c = 4 (every proper U with |U| ≥ 2 spans
at most 3|U| − 5 edges), such that neither G nor any G − y (y ∈ V) has a 4-factor: one with n = 9
(`HCXf~z{`), one with n = 11 (`JCOfuzsnCf_`), and nine with n = 12 (listed in `FLAW.md`), which are all
such graphs with n ≤ 12 (none for n ≤ 8 or n = 10).
(b) There are graphs with e = 3n − 3, sparse for c = 3 (proper U span at most 3|U| − 4), with the same
property: `K?ABvrw~Fw^_` and `K?AFvrw^Fw^_` (n = 12), which are all such graphs with n ≤ 12.
(c) There are bipartite graphs with sides 7 and 8, e = 40 = 3n − 5, δ ≥ 4, Δ ≤ 6, sparse for QB(5)
(proper U with |U| ≥ 3 span at most 3|U| − 6), in which B − y has no 4-factor for every port y:
`N???FbKickNo^_^_No?`, `N???FaM{C[No^_^_No?`, `N???FaMyCkNo^_^_No?`.
Every graph listed has a 4-regular subgraph on fewer vertices.

*Proof.* (a) for n = 9 by hand in `FLAW.md` (the graph is the join of an independent triple with
K2 + C4; four explicit barriers; sparsity from the maximum of e_F over i-subsets). All cases by exact
DFS (`checks/deep.c` with the search of `q4core.h` restricted to spanning subgraphs) over all sparse
graphs of each order (generated by `checks/geng_sp35`, `geng_sp34`, `genbg_bsp6`), and again by an
independent SAT encoding with brute-force sparsity (`checks/check_deep.py`, output
`checks/data/out_deep.json`, 16 of 16 claims confirmed). ∎

In the QB(5) graphs of (c) the smaller side has one vertex u0 of degree 4, adjacent to all four ports,
so every port is trivially bad (u0 drops to degree 3); the good vertices are the W-vertices of degree 6.
B − u0 is then a bipartite graph with sides differing by 2, the smaller side saturated, and e = 3n − 6.

**Consequence 3.2.** No argument whose only inputs are sparsity, "G has no 4-factor" and "G − y has no
4-factor for every vertex y" can prove P_4 or P_3, and the port-only version cannot prove QB(5). The
graphs of Theorem 3.1(a), (b) are not counterexamples: each has a 4-regular subgraph avoiding at least
two vertices (for `HCXf~z{`, 4-factors of G − y − z exist for five pairs {y, z}, and the octahedron on
{1, 2, 4, 5, 6, 7} avoids three; for the n = 12 P_3 graphs, a K_{4,4}).
Data on pairs: for n ≤ 12, every sparse graph of the P_4 class without a 4-factor has a vertex y or a
pair {y, z} with a 4-factor in G − y or G − y − z (`checks/data/deep_n*.txt`, column good2 ≥ 1). By
Corollary 2.4 a proof along these lines must control adjacency and parity obstructions, for which the
C1 method has no tool.

## 4. Gluing across tight sets

**Lemma 4.1 (realizing defects).** Let G be a minimal counterexample to P_c (c ∈ {3, 4}) and X ⊆ V with
|X| ≥ 2, |V − X| ≥ 2 and g(X) = 2c + 2 + 2a, where 0 ≤ a ≤ 2. Let x_1, ..., x_{4+a} ∈ X be distinct,
each incident with an edge of ∂X. Then there are I ⊆ {1, ..., 4 + a} with |I| = 4 and a subgraph
H ⊆ G[X] with deg_H(x_i) = 3 for i ∈ I and deg_H(v) = 4 for every other vertex v of H.

*Proof.* Let G' = G[X] + z, z a new vertex adjacent to x_1, ..., x_{4+a}. G' is simple; deg z =
4 + a ≤ 6 and deg_{G'}(x_i) = deg_{G[X]}(x_i) + 1 ≤ deg_G(x_i) ≤ 6 because x_i has an edge leaving X;
so Δ(G') ≤ 6. |V(G')| = |X| + 1 ≤ n − 1. e(X) = (6|X| − g(X))/2 = 3|X| − c − 1 − a, so
e(G') = 3(|X| + 1) − c. By minimality G' has a nonempty 4-regular subgraph H'. If z ∉ V(H') then
H' ⊆ G, impossible; so z has H'-degree 4. Let I index its four H'-neighbors and H = H' − z. ∎

**Theorem 4.2 (gluing).** Let G be a minimal counterexample to P_c (c ∈ {3, 4}), X tight with
|X| ≥ 2 and |V − X| ≥ 2, and a = ∂X − c − 2. Then a ≥ 0, and if a ≤ 2 the cut ∂X contains no matching
of size 4 + a.

*Proof.* g(V − X) = g(V) + 2∂X − g(X) = 2∂X − 2 (from g(X) + g(V − X) = g(V) + 2∂X), so sparsity of
V − X gives ∂X ≥ c + 2 and g(V − X) = 2c + 2 + 2a. Suppose {x_i y_i : 1 ≤ i ≤ 4 + a} is a matching in
∂X with x_i ∈ X. Lemma 4.1 for V − X and y_1, ..., y_{4+a} gives I and H_Y ⊆ G[V − X]; Lemma 4.1 for X
(a = 0) and {x_i : i ∈ I} gives H_X ⊆ G[X]. Then H_X ∪ H_Y ∪ {x_i y_i : i ∈ I} is a nonempty subgraph
of G in which x_i and y_i (i ∈ I) have degree 3 + 1 and every other vertex degree 4: a contradiction. ∎

**Corollary 4.3 (piece types).** In a minimal counterexample, with C the piece of the barrier:
- P_4, type 42 (D_C = 3, e(C,S) = 7, e(C,T) = 0): ∂C has no matching of size 5.
- P_4, type 41 (D_C = 2, e(C,S) = 7, e(C,T) = 1): ∂C has no matching of size 6.
- P_3, type 11 (D_C = 1, e(C,S) = 7, e(C,T) = 0): E(S,C) has no matching of size 5.
- P_3, type 10 (D_C = 0, e(C,S) = 7, e(C,T) = 1): E(S,C) has no matching of size 6.

*Proof.* In each, g(C) = D_C + ∂C = 2c + 2 (tight), |C| ≥ 2, |V − C| = s + t ≥ 2 (s ≥ t + 2). Types 42
and 41 have ∂C = 7, 8, that is a = 1, 2: Theorem 4.2. Types 11 and 10: S and T are independent,
D_T = 0, and every edge at T goes to S except the e(C,T) edges, so G[S ∪ T] is bipartite with T of
deficiency e(C,T) inside it. Let M be a matching in E(S,C) of size 5 (type 11) or 6 (type 10) and let
B* = G[S ∪ T] + c*, c* a new vertex adjacent to the S-ends of M. B* is bipartite with sides S (t + 2)
and T ∪ {c*} (t + 1), deficiency of T ∪ {c*} equal to e(C,T) + 6 − |M| = 1, Δ(B*) ≤ 6 (each S-end of M
has an edge to C). By C1 (Theorem 4.3 of C1-PAPER) B* has a 4-regular subgraph H*; it uses c*, since
otherwise H* ⊆ G; let s_1, ..., s_4 be its H*-neighbors and c_1, ..., c_4 their M-partners (distinct).
Lemma 4.1 for X = C (tight, |V − C| ≥ 2) with c_1, ..., c_4 gives H_C ⊆ G[C] with defects exactly at
c_1, ..., c_4. (H* − c*) ∪ H_C ∪ {s_i c_i} is 4-regular in G. ∎

In a minimal counterexample every vertex is incident with at most 3 edges of the cut of a tight set X
with |X| ≥ 3 (for v ∈ X: g(X − v) ≥ 2c + 2 gives deg_X(v) ≥ 3; for v ∉ X: g(X + v) ≥ 2c + 2 gives
e(v, X) ≤ 3, when X + v ≠ V). So the residual cases of Corollary 4.3 are cuts whose 7 or 8 edges are
concentrated on few vertices.

## 5. Barrier-type reductions

**Proposition 5.1 (deletion number).** Let (S,T) be a barrier of G with components C of G[R]. Choose
for each singleton component x a side: drop, T (keep its edges to S) or S (keep its edges to T). Let B'
be the bipartite subgraph of G with sides S ∪ {x on S} and T ∪ {x on T} and only the edges between the
two sides. Then

    m := 3|V(B')| − e(B') = 3(s − t) + D_T + 2e(T) + e(T,R) + Σ_{x on T} (3 − e(x,S)) + Σ_{x on S} (3 − e(x,T)).

*Proof.* e(S,T) = 6t − D_T − 2e(T) − e(T,R) from the degree sum over T; distinct singleton components
are not adjacent, so B' is bipartite with e(B') = e(S,T) + Σ_{x on T} e(x,S) + Σ_{x on S} e(x,T). ∎

So if QB(m) holds and |V(B')| ≥ 4, G has a 4-regular subgraph. The minimum of m over placements is a
function of the type alone; it is tabulated in `checks/data/type_table.txt` (`checks/type_table.py`,
which imports the reviewed enumerator unchanged). For c = 4, sparsity gives e(B') ≤ 3|V(B')| − 5 unless
B' = G, so m = 4 is possible only when G itself is a bipartite C1 instance.

**Theorem 5.2 (P_3).** Let G be a minimal counterexample to P_3.
(a) G has no barrier of type 1, 4, 7, 9 or 12.
(b) A barrier of type 5 or 6 yields one of type 3 (move the singleton x into S); one of type 2 yields one
of type 8 (move an end of the T-edge into R) and conversely (move x into T).
(c) A barrier of type 3 does not have E(G[S]) a star whose center has exactly one neighbor in T.
(d) Corollary 4.3 holds for types 10 and 11.
(e) Hence G has a barrier of type 2, 3, 10 or 11, and every barrier of G is of type 2, 3, 5, 6, 8, 10
or 11.

*Proof.* (a) Deletion numbers 4, 4, 4, 3, 3 (table): type 1 drop (B' = G − f, sides S, T, smaller
side T of deficiency 1: a C1 instance); type 4 drop (B' = G − x, T-deficiency e(x,T) = 1); type 7 x on
T (B' = G − f with sides S, T ∪ {x}, x of degree 5); type 9 x on T (B' = G, a C0 instance); type 12
(G is C0). In each case QB(4), that is C1/C0, gives a 4-regular subgraph of B' ⊆ G.
(b) Moving a singleton component x of R into S changes δ by −4 + 2e(x,S) − e(x,S) + [e(x,S) odd]; for
types 5, 6 (e(x,S) = 3, δ = −2) this gives δ = −2 with s − t = 2, e(S) = 3, e(T) = 0, D_T = 0,
D_S = 6, R = ∅: type 3. In type 2 the T-edge t_1t_2 is the only edge inside T and D_T = 0, so t_1 has
5 edges to S; with R = {t_1}, δ(S, T − t_1) = 4(−2) + 2 + 5 − 1 = −2, and the tuple is type 8. In type 8,
moving x into T gives δ = 4(−1) + 2 + 0 = −2 with e(T) = 1: type 2.
(c) If E(G[S]) is a star with center x, moving x into R gives δ(S − x, T) = 4(−1) + 0 + 3 − 1 = −2 with
singleton (D_x, 3, e(x,T)); if e(x,T) = 1 this is type 4, excluded by (a).
(d) Corollary 4.3. (e) Theorem 5 (REPORT.md) supplies a barrier; (a) and (b). ∎

**Theorem 5.3 (P_4).** Let G be a minimal counterexample to P_4. It has no barrier of type 31, 51, 54
or 57, and Corollary 4.3 holds for types 41 and 42.

*Proof.* Types 31, 51, 54, 57 have deletion number 4 with every singleton on the T side: in each, e(S) =
e(T) = 0, every singleton has e(x,T) = 0, and the tuple makes G itself bipartite with sides S and
T ∪ R, the smaller side T ∪ R of size |S| − 1 and deficiency 1 (type 31: D_T = 1, x saturated; 51: x_0
of degree 5, x_1 saturated; 54: D_T = 1; 57: x of degree 5). So G is a C1 instance. Types 41, 42:
Corollary 4.3. ∎

**Corollary 5.4 (bipartite statements behind P_3 and P_4).**
(a) QB(7) implies P_3.
(b) If QB(7) holds, every barrier of a minimal counterexample to P_4 is of one of the 14 types
5, 18, 20, 30, 38, 48 (deletion number 8), 6, 21, 34, 36, 39, 40 (9), 35, 37 (10).
(c) QB(8) is false: `J?BvfRguFo?` is bipartite with sides 5 and 6, 25 = 3·11 − 8 edges, degrees 4 to 6,
and no 4-regular subgraph (exact DFS and SAT, `checks/data/qb8_counterexample.g6`). So for the 14 types of
(b), deleting the non-bipartite edges and appealing to an unrestricted bipartite statement cannot work.
(d) If QB(5) holds, a minimal counterexample to P_3 has no barrier of type 2, 5 or 8, and each type-3
barrier has E(G[S]) a triangle or a star whose center has degree 6.

*Proof.* (a) The P_3 deletion numbers are 4, 5, 6, 4, 5, 6, 4, 5, 3, 7, 6, 3 for types 1-12 (table),
all at most 7. B' has at least 4 vertices: for types without a piece |V(B')| ≥ n − 1 ≥ 6; for types
10, 11, B' = G[S ∪ T] with s = t + 2 and t ≥ 1 (if t = 0 the two S-vertices carry all 7 edges to C, but
each carries at most 3 by sparsity of C + s). So B' has a 4-regular subgraph. (b) The same with the
P_4 table. (c) Computation. (d) Types 2, 5: B' = G[S, T] is a C2 instance (T-side deficiency 2),
e(B') = 3n' − 5; type 8 via (b) of Theorem 5.2. Type 3 with two disjoint S-edges ab, cd: B' + c* with c*
on the T side adjacent to a, b, c, d has e = 3n' − 5 and Δ ≤ 6, so QB(5) gives H; if c* ∈ H then
H − c* + ab + cd is 4-regular in G. Three edges with no two disjoint form a triangle or a star; a star
center x has e(x,T) ≥ 1 (degree ≥ 4), e(x,T) = 1 is excluded by Theorem 5.2(c) and e(x,T) = 2 gives
type 5. ∎

The census supports QB(7): for n ≤ 18 every bipartite graph with δ ≥ 4, Δ ≤ 6 and no 4-regular subgraph
has e ≤ 3n − 8 (F1 and its extensions, `reports/585-next/STATE.md` lines 18, 31, 33). A proof of QB(7)
would need the C1 method two levels above where it works (Theorem 3.1(c) already breaks it at QB(5)).

## 6. Exact residual

**P_3.** A minimal counterexample has a barrier of type 2 (equivalently 8), 3, 10 or 11, none of types 1,
4, 7, 9, 12, and:
- type 3: E(G[S]) is not a star whose center has one T-neighbor;
- type 10: E(S,C) has no matching of size 6; type 11: no matching of size 5.
Closing types 2 and 3 would follow from QB(5) except for type 3 with E(G[S]) a triangle or a star
centered at a degree-6 vertex (Corollary 5.4(d)); everything would follow from QB(7) (5.4(a)).

**P_4.** A minimal counterexample has no barrier of types 31, 51, 54, 57, and its type-41 and type-42
barriers have small cut matchings (Corollary 4.3). The other 52 types are open. By deletion number:
m = 5 for 11 types (1, 10, 13, 22, 25, 32, 43, 49, 53, 55, 58), m = 6 for 16 (2, 7, 8, 9, 11, 12, 14, 16,
23, 26, 28, 33, 44, 45, 50, 56), m = 7 for 11 (3, 4, 15, 17, 19, 24, 27, 29, 46, 47, 52), m ≥ 8 for 14
(Corollary 5.4(b)); for the last group a deletion proof would need a bipartite statement restricted to
the class that arises (Corollary 5.4(c)), and in the examples the 4-regular subgraph uses edges inside S,
as the octahedron of `HCXf~z{` (type 6 of the P_4 list, m = 9) does.

**How far the reductions reach on data** (`checks/typeclass.c`, every barrier of every sparse graph with
no 4-factor, minimum deletion number per graph):

| Class | n | graphs without a 4-factor | min m = 3, 4 | 5 | 6 | 7 | 8 | 9 |
|---|---|---|---|---|---|---|---|---|
| P_4 | 9 | 8 | 0 | 0 | 0 | 1 | 0 | 7 |
| P_4 | 10 | 27 | 0 | 0 | 2 | 9 | 16 | 0 |
| P_4 | 11 | 352 | 1 | 8 | 16 | 48 | 58 | 221 |
| P_4 | 12 | 2,426 | 0 | 12 | 61 | 590 | 1,763 | 0 |
| P_3 | 10 | 4 | 0 | 0 | 4 | 0 | 0 | 0 |
| P_3 | 11 | 7 | 3 | 4 | 0 | 0 | 0 | 0 |
| P_3 | 12 | 87 | 2 | 4 | 81 | 0 | 0 | 0 |

For P_4 the deletion route is far from enough even on small data, and most graphs need m = 8 or 9.

## 7. What was tried, and where to go next

Tried, in order: (1) the C1 port argument on general graphs via Lemma 2.2 (fails: §3); (2) the same
with pairs of ports (all obstructions become adjacency or parity ones, Corollary 2.4); (3) per-type
reductions to C0, C1, E4, QB(4) by deletion and by moving singletons between S, T and R (§5);
(4) gluing across tight pieces with P_c-minimality on one side (§4); (5) a sanity check of the bipartite
statement QB(5) needed next (port method fails at n = 15, Theorem 3.1(c); a quartic search finds no
counterexample in its sparse class for n ≤ 16, and F1 covers n ≤ 18).

Suggested next steps, in order of expected value:
1. **QB(5) with all W-vertices.** In the n = 15 graphs the degree-6 W-vertices are good. A C1-type
   argument over every W-vertex (not only ports), plus the E5 case (every violation splits V into two
   tight blocks joined by 7 edges, closed by gluing whenever the 7 edges contain a 4-matching), is the
   natural next theorem; with Corollary 5.4(d) it reduces P_3 to two shapes of type 3 and the small-
   matching cases of types 10 and 11.
2. **Heavy types of P_4.** Types with deletion number ≥ 8 are where 4-regular subgraphs must use
   non-bipartite edges (octahedra in the n = 9, 11 graphs, F3/F4 families of REPORT.md §6). A structural
   statement about the S-side graph F = E(G[S]) under sparsity (for example, that F with s − t = 3,
   e(S) = 5 must contain a cycle whose vertices have two common T-neighbors) is the missing piece.
3. **Parity.** Corollary 2.4 shows that deleting two ports (P_3) leaves only obstructions with
   e(S, Y) + q ≥ 2. Any port-based proof needs a lemma that controls odd components under sparsity.

## Appendix A. Computations

All code is in `reports/585-next/wave3/P4/checks/`; outputs in `checks/data/`. Interpreter
`/private/tmp/erdos585-research-venv/bin/python` (networkx, pysat with CaDiCaL 1.5.3). C tools built by
`checks/build.sh` with `/usr/bin/clang -O3` against nauty 2.9.3 sources in `~/.cache/erdos585/nauty2_9_3`
(read only). Every Python check exits nonzero on a mismatch.

| Check | What | Result |
|---|---|---|
| A.1 `check_identity.py` | Lemma 2.1 (a)-(d) and Lemma 2.2 on 400 random graphs with Δ ≤ 6 (no sparsity), all partitions for n ≤ 8, 3,000 random ones above, random Y ⊆ Q | 937,659 partitions, 0 mismatches (`out_identity.json`) |
| A.2 `geng_sp35`, `geng_sp34` (geng + PRUNE `sp35prune.c`, SPC = 5, 4) | all graphs with -d4 -D6, e = 3n − c, proper sets sparse | P_4 class: 6, 60, 1,150, 35,519, 1,471,764, 74,441,736 for n = 7..12; P_3 class: 4, 32, 524, 14,302, 555,610 for n = 7..11 |
| A.3 `check_types_census.py` | the PRUNE generators equal plain geng 2.9.3 + Python brute-force sparsity filter, as graph6 lists | identical for n = 7, 8, 9, both classes |
| A.4 `geng_sp35q4`, `geng_sp34q4` (also prune any 4-regular subgraph, rooted search of `q4core.h`) | minimal-counterexample search | 0 graphs: P_4 for n = 7..12 (n = 12: 55 s) and n = 13 (A.9); P_3 for n = 7..12 (n = 12: 33 s) |
| A.5 `deep.c`, `no4f.c` | exact 4-factor DFS on G, every G − y and every G − y − z | P_4 class: graphs without a 4-factor 8, 27, 352, 2,426 (n = 9..12); deep 1, 0, 1, 9; P_3 class: 0, 4, 7, 87 (n = 9..12); deep only at n = 12 (2) |
| A.6 `check_deep.py` | Theorem 3.1 by SAT (own encoding, witness check) and brute-force sparsity | 16 of 16 claims confirmed (`out_deep.json`) |
| A.7 `genbg_bsp6` (genbg + PRUNE1 `bsp_prune.c`), `q4count.c` | QB(5) sparse class, degrees 4..6 | 1, 2, 13, 29, 818, 2,895, 229,728 graphs for n = 10..16, all with a 4-regular subgraph; at n = 15, 3 have every port bad (Theorem 3.1(c)); at n = 16 all have a 4-factor |
| A.8 `type_table.py`, `check_types_n10.py`, `typeclass.c` | deletion numbers per type; formula and budget identity on every barrier of every sparse graph without a 4-factor at n = 9, 10; per-graph minimum (§6 table) | 0 mismatches on 21 + 100 barriers |
| A.9 `run_n13.sh` (shard 0 run alone first as a 58 s pilot) | P_4 minimal-counterexample search at n = 13, e = 35, 48 shards | 48 of 48 shards complete, 0 graphs; 767,128,279 PRUNE calls, 552,109,839 quartic rejections, 362,070 sparsity rejections (about 0.8 core-hours) |
| A.10 `qb8_counterexample.g6` | Corollary 5.4(c) | bipartite, 11 vertices, 25 edges, no 4-regular subgraph (q4count and SAT) |

The barrier enumerators (`barstat.c`, `barstat2.c`, `typeclass.c`) enumerate all 3^n pairs (S,T) and
compute q from the components of G[R] by bitmask closure; `barstat.c` also asserts Lemma 2.1(c), (d) and
Lemma 2.2 on every barrier it meets (0 mismatches at n = 7, 8, 9).

## Appendix B. Sources (paths relative to the repository root)

- `reports/585-fable-wildcard/lanes/quartic-subgraph/REPORT.md` (SHA-256 a252b40f...e3f5ec): P_c (line
  136), Lemma 1 (140-158), Lemma 2 budget identity (160-180), Lemma 4 (196-204), Theorem 5 (205-221),
  F1-type bipartite census (269-277), extremal families F3, F4 (287-312).
- `reports/585-fable-wildcard/lanes/quartic-subgraph/obstruction_types.py` (SHA-256 7c16e36a...cd4f0)
  and `out/obstruction_types.txt`: the 12 and 58 types and their order.
- `reports/585-fable-wildcard/reviews/QUARTIC-REVIEW.md`: the Kostochka et al. form of the criterion
  (lines 64-79), Lemma 4 (82-104), Theorem 5 reproduced (105-121).
- `reports/585-next/G110/C1-PAPER.md` (SHA-256 3c67d183...0cf8): Lemma 1.4 (91-95), Lemma 3.1 (137-155),
  Theorem 4.3 (206-211), Lemma 4.4 (213-221), Corollaries 5.1-5.4 (227-246);
  `C1-REVIEW.md` (verdict, lines 15-33); `C1-CORRECTIONS.md` (second referee, lines 13-17).
- `reports/585-next/STATE.md`: F1 and its extensions (lines 18, 31, 33), C1-CLOSE (line 44).
