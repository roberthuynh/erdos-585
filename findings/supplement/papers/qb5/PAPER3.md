# QB(5), round 3: cores reduce to one lemma about a single block

Author lane qb5, round 3, October 5, 2026. Status: frozen for independent review (SHA-256 in
`FROZEN3.sha256`). Not reviewed. This is rung 2 of the round-3 ladder: QB(5) is proved under one extra
hypothesis, Key Lemma KL1 below, a statement about one 2-block and one 4-set of cut edges. KL1 holds on every
block built so far, two of its cases are proved here, and the exact remaining case is stated (§5.4). It is
not a proof of QB(5). No Lean, no `check.sh`, so nothing here is a project-oracle PASS. Rungs: (a) for
Theorem 2.1, Lemmas 3.1 to 3.4, Propositions 5.2 and 5.3; (a) with a computed lemma (Lemma 4.1, two
independent programs) for Theorem 4.2 and Corollary 4.3; (b) for the example of §6.1 and the data of §6.

PAPER.md (frozen, `FROZEN.sha256`) and PAPER2.md (frozen, `FROZEN2.sha256`) are cited by section and number.
Their referee reports REVIEW.md and REVIEW2.md are FINAL with no mathematical error; the fixes F1 to F7 and
G1 to G3 are in force (§1.2).

## 0. Results at a glance

QB(5): every finite simple bipartite graph with maximum degree at most 6, n ≥ 3 vertices and at least
3n − 5 edges contains a nonempty 4-regular subgraph. By PAPER.md Theorem 7.1 and §8.4 it follows from the
**E5 pair statement**: every sparse E5 instance G without a 4-factor has p ∈ P, q ∈ Q such that G − p − q has
a 4-factor. PAPER2 proved the pair statement when every big-side vertex is generic; a non-generic vertex
needs a core (PAPER2 Proposition 5.1). This paper handles cores up to one block-level lemma.

| Item | Statement | Verdict | Where |
|---|---|---|---|
| **Theorem 2.1** | **M-form: (p, q) is good iff p ∈ I_X(M) and q ∈ I_Y(M) for some 4-set M of cut edges; the two blocks decouple once M is fixed** | proved | §2 |
| Lemma 3.1 | identity w(T) + θ(T) + e''(T) = 2κ(T) + 4 for every T ⊆ A, and three sparsity bounds | proved | §3 |
| Lemmas 3.2, 3.3 | overloaded sets are large; a 4-set M is X-bad only in cases (a), (b), (c) | proved | §3 |
| **Lemma 3.4** | **case (b) is rigid: κ = 0, e'' = 0, no deficiency and no spare cut edge on T − a, 3 or 4 cut edges** | proved | §3 |
| Lemma 4.1 | refined covering lemma for 7-edge cuts | computed by two independent programs | §4 |
| **Theorem 4.2** | **if KL1 holds for both blocks, the E5 pair statement holds** | proved, with Lemma 4.1 | §4 |
| **Corollary 4.3** | **if KL1 holds in the blocks of a minimal counterexample (for instance in every 2-block of every sparse E5 instance without a 4-factor), QB(5) holds; KL1 holds for generic blocks** | proved, with Lemma 4.1 | §4 |
| Propositions 5.2, 5.3 | toward KL1: two under-supplied sets always meet; a failure of KL1 needs at least three core-type under-supplied sets | proved | §5 |
| §5.4 | exact remaining case | stated | §5 |
| §6 | case (b) occurs (22-vertex block), so the strong form of KL1 is false; KL1 holds on all 1,750 blocks built and in every search | computed | §6 |

**Key Lemma KL1 (for the block X).** For every 4-set M of cut edges such that every in-degree-3 vertex of A
is an end of an edge of M, I_X(M) is nonempty. KL1 for Y is the same statement with D, B in place of A, C.

**Where a referee should attack first.**
1. Theorem 2.1: the two directions, in particular that I_X(M) avoids the ends of M.
2. Lemma 3.1(i) for every T (the split of C into C'(T) and C''(T)) and its use in Lemma 3.4.
3. Lemma 4.1: that its rigid sets K are exactly what Lemma 3.4 produces, that giving every end outside L the
   deficiency 0 is the worst case, and the two programs.
4. Propositions 5.2 and 5.3: the weight count and the degree bound at the shared vertex.

## 1. Setting

### 1.1 Notation

As in PAPER2 §1.1: G is a sparse E5 instance (sides P, Q, |P| = |Q|, Δ ≤ 6, D(P) = D(Q) = 5, g(S) ≥ 12 for
3 ≤ |S| ≤ n − 1) without a 4-factor, with a fixed 2-block decomposition X = A ∪ C, Y = B ∪ D (A, B ⊆ P), cut
E = E(A, D), |E| = 7. For v ∈ A ∪ D: c_v cut edges, in-block degree d_v, δ_v = 6 − d_v = c_v + def(v).
L_A = {a ∈ A : d_a = 3}, L_D likewise. Facts used (PAPER2 §1.2): (B1) d_v ≥ 3, c_v ≤ 3, and c_v = 3 forces
v ∈ L; (B2) v ∈ L has c_v ≥ 1 and def(v) = 3 − c_v, and Σ_{v∈L_A} (3 − c_v) ≤ 5. Also def(v) ≤ 2 for every v
(deg v ≥ 4) and Σ_{a∈A} δ_a = 12, Σ_A c = 7, Σ_A def = 5.

dem_X(A1) = 4|A1| − Σ_{c∈C} min(4, e(c, A1)) (PAPER2 §2), and for T ⊆ A, φ_X(T) = 4|T| − Σ_c (e(c, T) − 2)^+.
Since min(4, 6 − x) = 4 − (x − 2)^+ for 0 ≤ x ≤ 6, dem_X(A − T) = 8 − φ_X(T). Put ρ(T) = φ_X(T) − 4 =
4 − dem_X(A − T); ρ({v}) = 0 and ρ(T) = 4 when |T| = 2.

M always denotes a 4-set of cut edges; m(v) is the number of edges of M at v, m(S) = Σ_{v∈S} m(v), V(M) is
the set of ends of M. A set A1 ⊆ A is **under-supplied** (by M) if m(A1) < dem_X(A1), and
I_X(M) = ⋂ {A1 : A1 under-supplied} (A is always under-supplied: dem_X(A) = 8 > 4). For T ⊆ A put
θ(T) = m(T) − ρ(T) = dem_X(A − T) − m(A − T); T is **overloaded** if θ(T) ≥ 1, i.e. A − T is under-supplied.
So I_X(M) is A minus the union of all overloaded sets. {v} is overloaded iff m(v) ≥ 1, so
I_X(M) ∩ V(M) = ∅. The same notation is used on the Y side.

The *weight* of v ∈ A is w(v) = δ_v − m(v) = def(v) + (c_v − m(v)) ≥ 0, w(S) = Σ_{v∈S} w(v), w(A) = 12 − 4 = 8.

### 1.2 Corrections in force

F1 to F7 (REVIEW.md §2) as stated in PAPER2 §1.3; G1 (REVIEW2.md): pairs are taken with p ∈ P, q ∈ Q, and
Fact 2.1 of PAPER2 then gives p ∈ A, q ∈ D; G2: (R1) of PAPER2 §7 goes through PAPER2 Corollary 3.4; G3: the
"permissive model" sentence of PAPER2 §7 is an unrefereed observation. REVIEW2.md §2 (optional items) also
records an elementary converse of PAPER2 Corollary 2.3, used in Theorem 2.1.

## 2. The M-form of the pair criterion

**Theorem 2.1.** Let p ∈ A and q ∈ D. G − p − q has a 4-factor if and only if some 4-set M of cut edges has
p ∈ I_X(M) and q ∈ I_Y(M). Hence the E5 pair statement holds for G if and only if some M has I_X(M) and
I_Y(M) both nonempty.

*Proof.* (If.) For a ∈ V(M) ∩ A the set A − a is under-supplied, since dem_X(A − a) = 4 (PAPER2 Lemma 3.1(a))
and m(A − a) = 4 − m(a) < 4. So p ∉ V(M), and likewise q ∉ V(M): M has no edge at p or q. Every
under-supplied set contains p, so every A1 ⊆ A − p has m(A1) ≥ dem_X(A1); likewise every D1 ⊆ D − q has
m(D1) ≥ dem_Y(D1). PAPER2 Corollary 2.3 gives a 4-factor of G − p − q.
(Only if.) Let H be a 4-factor of G − p − q. By PAPER2 Fact 2.1 (with G1), H contains exactly 4 cut edges,
none at p or q; let M be this set. For A1 ⊆ A − p, every vertex of C has H-degree 4 and all its neighbors in
A, so 4|A1| = e_H(A1, C) + m(A1) ≤ Σ_c min(4, e(c, A1)) + m(A1), that is m(A1) ≥ dem_X(A1). So no
under-supplied set lies in A − p, and p ∈ I_X(M). The same argument in Y gives q ∈ I_Y(M). ∎

Checked against maximum flow on every pair of 35 instances (Appendix A.1).

## 3. Overloaded sets

For T ⊆ A let C'(T) = {c ∈ C : e(c, T) ≥ 3}, C''(T) = C − C'(T), κ(T) = |T| − |C'(T)|,
e''(T) = e(C''(T), T), k(T) = dem_X(A − T), X'(T) = T ∪ C'(T) and X''(T) = (A − T) ∪ C''(T).

**Lemma 3.1.** For every T ⊆ A:
(i) e(C'(T), A − T) = 8 − 4κ(T) − k(T);
(ii) δ(T) = 2κ(T) + 8 − k(T) − e''(T);
(iii) w(T) + θ(T) + e''(T) = 2κ(T) + 4;
(iv) if |X'(T)| ≥ 3 then κ(T) + k(T) ≤ 2; if |X''(T)| ≥ 3 then e''(T) ≥ 3κ(T); and if |X''(T)| ≥ 4, every
x ∈ A − T has at least 3 + 3κ(T) − e''(T) neighbors in C''(T).

*Proof.* Write C' = C'(T), C'' = C''(T), κ, k, e''. (i) A vertex of C'' has at most 2 neighbors in T, so at
least 4 in A − T; a vertex of C' has at most 3 in A − T. So k = 4|A − T| − 4|C''| − e(C', A − T), and
|A − T| − |C''| = (|A| − |C|) − (|T| − |C'|) = 2 − κ. (This is PAPER2 Proposition 5.1, Step 1, which uses
nothing about T.) (ii) δ(T) = 6|T| − e(C', T) − e'' and e(C', T) = 6|C'| − e(C', A − T); substitute (i).
(iii) w(T) = δ(T) − m(T) and θ(T) = m(T) − ρ(T) = m(T) − 4 + k; substitute (ii).
(iv) X'(T) ⊆ X is proper; e(X'(T)) = e(C', T) = 6|C'| − 8 + 4κ + k by (i), and sparsity gives
e(X'(T)) ≤ 3(|T| + |C'|) − 6 = 6|C'| + 3κ − 6, so κ + k ≤ 2. X''(T) has 2|C''| + 2 − κ vertices and
6|C''| − e'' edges, so g(X''(T)) = 12 − 6κ + 2e'' ≥ 12. For x ∈ A − T, PAPER.md Identity 1.3 gives
g(X''(T) − x) = g(X''(T)) − 6 + 2e(x, C'') ≥ 12. ∎

**Lemma 3.2.** Let T be overloaded with |T| ≥ 2, and suppose every vertex of L_A − T is an end of M. Then
|T| ≥ 3, |A − T| ≥ 5, −1 ≤ κ(T) ≤ 2 − k(T), 1 ≤ k(T) ≤ 3, m(T) ≥ θ(T) + 2 + κ(T) ≥ 2 and
w(T) ≤ 2m(T) − 3θ(T) − e''(T).

*Proof.* If |T| = 2 then ρ(T) = 4 and θ(T) ≤ 0. If |A − T| ≤ 4, then e(c, A − T) ≤ 4 for every c, so
dem_X(A − T) = Σ_{a∈A−T} (4 − d_a) ≤ |(A − T) ∩ L_A| ≤ m(A − T) (d_a ≥ 3; the L-vertices of A − T are ends of
M), and A − T is not under-supplied. So |X'(T)| ≥ |T| ≥ 3 and |X''(T)| ≥ 5, and Lemma 3.1(iv) applies:
κ + k ≤ 2. By Lemma 3.1(iii) with θ ≥ 1, 2κ + 3 ≥ w(T) + e''(T) ≥ 0, so κ ≥ −1 and k ≤ 3; k = θ + m(A − T) ≥ 1.
With k = 4 − m(T) + θ, κ + k ≤ 2 reads κ ≤ m(T) − 2 − θ, which gives the bound on m(T), and Lemma 3.1(iii)
gives w(T) = 2κ + 4 − θ − e'' ≤ 2m(T) − 3θ − e''. ∎

**Lemma 3.3 (classification).** If I_X(M) = ∅, then (a) at least two vertices of L_A are not ends of M, or
(b) exactly one vertex a of L_A is not an end of M and a lies in an overloaded set, or (c) every vertex of L_A
is an end of M.

*Proof.* If exactly one vertex a of L_A is not an end of M, then {a} is under-supplied
(dem_X({a}) = 1 > 0 = m(a), PAPER2 Lemma 3.1(b)), so I_X(M) ⊆ {a}, and I_X(M) = ∅ means that a lies in an
overloaded set. ∎

**Lemma 3.4 (case (b) is rigid).** Suppose exactly one vertex a of L_A is not an end of M and T ∋ a is
overloaded. Then κ(T) = 0, k(T) ∈ {1, 2}, e''(T) = 0 and θ(T) = 1; every vertex of T − a has def = 0;
every cut edge at a vertex of T − a lies in M; and c(T − a) = m(T) = 5 − k(T).

*Proof.* {a} is not overloaded (m(a) = 0), so |T| ≥ 2 and Lemma 3.2 applies (the L-vertices outside T are
ends of M). Now w(a) = δ_a = 3 and w(T − a) = D(T − a) + (c(T − a) − m(T)) ≥ 0, since m(a) = 0. Lemma 3.1(iii)
gives 2κ + 4 = 3 + w(T − a) + θ + e'' ≥ 4, so κ ≥ 0. If κ = 1, then k = 1 and e'' ≥ 3 (Lemma 3.1(iv)), and
6 = 3 + w(T − a) + θ + e'' ≥ 3 + 0 + 1 + 3 = 7: false. So κ = 0, and 4 = 3 + w(T − a) + θ + e'' with θ ≥ 1 forces w(T − a) = e'' = 0, θ = 1.
w(T − a) = 0 says D(T − a) = 0 and c(T − a) = m(T − a) = m(T). Finally k ≤ 2 − κ = 2 and
m(T) = ρ(T) + θ(T) = 5 − k. ∎

## 4. The main theorem

Call a set K of ends of E on the A side **rigid** for M if every vertex of K ∩ L_A has c = 3, every edge of
E at a vertex of K lies in M, and K is incident with exactly 3 or 4 edges of E. Rigid sets on the D side are
defined in the same way.

**Lemma 4.1 (refined covering lemma; computed).** Let E be a set of 7 edges of a simple bipartite graph with
sides A and D, every vertex in at most 3 of them (c_v of them). Let L_A ⊆ A and L_D ⊆ D consist of vertices
with c_v ≥ 1, contain every vertex with c_v = 3, and satisfy Σ_{L_A} (3 − c_v) ≤ 5 and Σ_{L_D} (3 − c_v) ≤ 5.
Then some 4-set M ⊆ E has, on each side, at most one vertex of L that is not an end of M, and, if a is such a
vertex, no rigid set K ⊆ V(M) − a on that side.

*Verification.* Two programs that share no code (Appendix A.2): `code/refined_cover.py` runs over the 142
cut graphs from nauty `genbg -d1:1 -D3:3 n1 n2 7:7` and their 36,339 admissible labellings;
`code/refined_cover2.c` builds every 0/1 matrix with given non-increasing row and column sums in {1, 2, 3}
(22,792 matrices, a superset of the isomorphism classes) and their 15,342,638 labellings. Both find an M as
claimed in every case (0 failures). The rigid condition is active (it rejects a side 33.5 million times in
the second program); with the size condition "3 or 4 edges" dropped, the second program finds 338,494
labellings with no valid M, so the sizes given by Lemma 3.4 are what make the lemma true. ∎

Lemma 4.1 lets every end outside L have def = 0, which is the most favorable case for rigid sets: a positive
deficiency at an end outside L only removes it from the candidates for K.

**Theorem 4.2.** If KL1 holds for X and for Y, then G − p − q has a 4-factor for some p ∈ A and q ∈ D.

*Proof.* E, L_A and L_D satisfy the hypotheses of Lemma 4.1 by (B1) and (B2) (as in PAPER2 §4.1); let M be
the 4-set it gives. If every vertex of L_A is an end of M, I_X(M) ≠ ∅ by KL1. Otherwise exactly one vertex a
of L_A is not an end of M. If a lay in an overloaded set T, Lemma 3.4 would make K = (T − a) ∩ V(E) rigid
for M: def = 0 on T − a and (B2) give c = 3 on K ∩ L_A, every cut edge at T − a lies in M (so K ⊆ V(M) − a),
and K is incident with c(T − a) = 5 − k(T) ∈ {3, 4} cut edges. Lemma 4.1 excludes this, so a lies in no
overloaded set, and a ∈ I_X(M). The same holds on the D side, and Theorem 2.1 finishes. ∎

**Corollary 4.3.**
(a) The E5 pair statement holds for every sparse E5 instance without a 4-factor whose two blocks satisfy KL1.
(b) If KL1 holds for both blocks of every minimal counterexample to QB(5), in particular if it holds for
every 2-block of every sparse E5 instance without a 4-factor, then QB(5) holds.
(c) KL1 holds for a block in which every big-side vertex is generic (PAPER2 Definition 3.2). So (a) contains
PAPER2 Theorem 4.1 and Corollary 5.2.

*Proof.* (b) A minimal counterexample is a sparse E5 instance without a 4-factor in which no G − p − q has a
4-factor (PAPER.md Lemma 2.1, Theorem 7.1); (a) excludes it. (c) |A| ≥ 6 (PAPER.md Theorem 6.1) and
|V(M) ∩ A| ≤ 4, so some p ∈ A is not an end of M. If M covers L_A and p is X-generic, PAPER2 Lemma 3.3(a)
gives m(A1) ≥ dem_X(A1) for every A1 ⊆ A − p, so p ∈ I_X(M). ∎

## 5. Toward KL1

### 5.1 Setting

In this section M covers L_A. Then w(v) ≤ 2 for every v ∈ A: if v ∈ V(M) then δ_v ≤ 3 and m(v) ≥ 1; if not,
v ∉ L_A, so δ_v ≤ 2. By Lemma 3.2 every under-supplied set A1 ≠ A is either **trivial**, A1 = A − v with
v ∈ V(M) (complement {v}, overloaded iff m(v) ≥ 1), or **core-type**, with |A1| ≥ 5 and |A − A1| ≥ 3. For a
core-type A1 write T = A − A1, κ, k, e'', θ for its data; Lemma 3.2 gives θ ≥ 1, κ ≤ 1, k ≤ 3,
m(A1) ≤ k − 1 ≤ 2, and κ = 1 forces k = 1 and e'' ≥ 3 (Lemma 3.1(iv), |X''(T)| ≥ 5).

I_X(M) = ∅ if and only if some family of under-supplied sets has empty intersection. Take such a family ℱ
minimal under inclusion; it consists of s core-type sets and t trivial sets A − v, and then every such v lies
in the intersection of the core-type members.

### 5.2 Two under-supplied sets always meet

**Proposition 5.2.** If M covers L_A, any two under-supplied sets meet. Hence s ≥ 2 in every minimal family ℱ.

*Proof.* Two trivial sets meet (|A| ≥ 6), and A − v meets every set with at least two elements. Let A1_1,
A1_2 be core-type and disjoint, with complements T_1, T_2. Then T_1 ∪ T_2 = A, so
w(T_1) + w(T_2) ≥ w(A) = 8. Lemma 3.1(iii) with θ_i ≥ 1 gives w(T_i) ≤ 2κ_i + 3 − e''_i, so
2(κ_1 + κ_2) ≥ 2 + e''_1 + e''_2. Then κ_1 + κ_2 ≥ 1, so some κ_i = 1, so e''_i ≥ 3 and
2(κ_1 + κ_2) ≥ 5, while κ_1 + κ_2 ≤ 2. For the last claim: s = 0 gives intersection A − V(M) ≠ ∅, and s = 1
gives a core-type set inside V(M), which has at most 4 vertices. ∎

### 5.3 Two core-type sets are not enough

**Proposition 5.3.** If M covers L_A, no minimal family ℱ has s = 2.

*Proof.* Let A1_1, A1_2 be the core-type members, T_i = A − A1_i, and I = A1_1 ∩ A1_2, nonempty by
Proposition 5.2. As ⋂ℱ = ∅, the trivial members remove I, so I ⊆ V(M), and |I| ≤ m(I) ≤ m(A1_1) ≤ 2.
T_1 ∪ T_2 = A − I, so w(T_1) + w(T_2) = 8 − w(I) + w(T_1 ∩ T_2) ≥ 8 − w(I).
If |I| = 2, then m(A1_i) ≥ 2, so k_i ≥ 3, κ_i ≤ −1 and w(T_i) ≤ 2κ_i + 3 ≤ 1; but 8 − w(I) ≥ 4 > 2.
If I = {u}, then w(u) ≤ 2 gives w(T_1) + w(T_2) ≥ 6, and Lemma 3.1(iii) gives
2(κ_1 + κ_2) ≥ e''_1 + e''_2 ≥ 0. No vertex of C lies in C''(T_1) ∩ C''(T_2): it would have at least 4
neighbors in each A1_i and at most one in A1_1 ∩ A1_2, so at least 7 in all. By Lemma 3.1(iv) (|X''(T_i)| ≥ 5)
u has at least 3 + 3κ_i − e''_i neighbors in C''(T_i), for i = 1, 2, so d_u ≥ 6 + 3(κ_1 + κ_2) − e''_1 − e''_2,
while d_u ≤ 5 because c_u ≥ m(u) ≥ 1. Hence e''_1 + e''_2 ≥ 1 + 3(κ_1 + κ_2) ≥ 1 + (3/2)(e''_1 + e''_2), which is
impossible. ∎

### 5.4 Exact remaining case

By Theorem 4.2, Corollary 4.3 and Propositions 5.2, 5.3: **QB(5) holds unless, in a block X of a minimal
counterexample, some 4-set M of cut edges that covers L_A admits a minimal family of under-supplied sets
with empty intersection that contains at least three core-type sets.** In such a family every core-type
member A1_i has an overloaded complement T_i with m(T_i) ≥ 2, w(T_i) ≤ 2m(T_i) − 3, κ_i ≤ 1 and k_i ≤ 3
(Lemma 3.2); any two members meet (Proposition 5.2); the complements of the core-type members, together with
the vertices removed by trivial members, cover A, so their weights add up to at least 8 while M has 4 units.
`NOTES.md` §7.6 sketches how the case of exactly three core-type members and no trivial member reduces to
one small configuration; that sketch is not claimed here.

## 6. Examples and evidence

### 6.1 Case (b) occurs, and the strong form of KL1 is false

`code/example_b.py` builds a 2-block X on 22 vertices: A = T ∪ U with T = {a, t2, ..., t6} = {0, ..., 5} and
U = {6, ..., 11}; C' = {c1, ..., c6} with N(c4) = N(c5) = N(c6) = T, N(c1) = T − {a, t2} + {6, 7},
N(c2) = T − {a, t3} + {8, 9}, N(c3) = T − {a, t4} + {10, 11}; C'' = {c7, ..., c10}, each adjacent to all of U.
In-block degrees: 3 at a, 5 at t2, t3, t4 and on U, 6 at t5, t6, so L_A = {a}. The block is sparse (largest
e(S) − 3|S| over proper S with |S| ≥ 3 is −6), dem_X(U) = 2, and T ∪ C' has κ = 0. With cut degrees c = 1 at
a, t2, t3, t4 and at three vertices of U including vertex 6, the 4-set M with ends {t2, t3, t4, 6} misses only a, and
I_X(M) = ∅: T is overloaded (m(T) = 3 > ρ(T) = 2), exactly as in Lemma 3.4 with k = 2. So "every M that
misses at most one L-vertex is X-good" is false, and Lemma 4.1 has to work around such M. KL1 itself holds
for this block (`code/blockkl.c`: 129 covering multisets, all with I_X ≠ ∅).

### 6.2 Data

- KL1 on every block built: `code/blockkl.c` checks, for a block and every multiset m on A with |m| = 4,
  m(a) ≤ min(3, δ_a), extendable to an admissible cut-degree vector and covering L_A, that I_X(m) ≠ ∅. On the
  1,750 blocks of the §6 certificate of PAPER2, the 24 core instances, the 100 built instances of PAPER.md
  §8.3 and the 750 random instances of PAPER2 §7 (both blocks of each): 89,194 covering multisets, 0 failures.
  Only the 25 blocks with a core are informative (Corollary 4.3(c) covers the rest).
- Searches: `code/klsearch.c` (local search from random blocks, |A| = 10 to 13) never produced a core-type
  under-supplied set; `code/klplant.c` (about 1,300 starts with planted dense pieces, local search towards small
  I_X(m)) found no failure of KL1. Neither search found case (b), which §6.1 builds by hand, so the searches
  are weak evidence.
- Theorem 2.1 in practice: in the PAPER2 certificate, the 24 core instances and 10 instances of PAPER.md §8.3,
  every one of the 35 sets M is X-good and Y-good.

## Appendix A. Computations

All code in `reports/585-next/wave4/qb5/code/`. C built with `/usr/bin/clang -O3`; Python is `/usr/bin/python3`
(numpy 1.26.4, networkx 3.2.1) for the new scripts, which import `g6.py`, `e5pairs.py`, `generic_check.py`
from rounds 1 and 2; nauty genbg 2.9.3 at `~/.cache/erdos585/nauty2_9_3/genbg`. Total compute: under 15
core-minutes.

| # | Check | Code and input | Result |
|---|---|---|---|
| A.1 | Theorem 2.1 against maximum flow on every pair (asserts) | `mform.py FILE N flowcheck` on `data/cert_core_n28.g6`, all 24 of `data/search/core28.g6`, first 5 of `data/e5_n22.g6` and of `data/e5_n24.g6` | no disagreement on any pair of the 35 instances; all 35 M good on both sides; good pairs 54 to 60 on core28 (as PAPER2 §7) |
| A.2 | Lemma 4.1, first program | `refined_cover.py` (and `plain` mode) | 142 graphs, 36,339 labellings, 0 failures (both modes) |
| A.2b | Lemma 4.1, second program | `refined_cover2.c` (`./refined_cover2`, `plain`, `loose`) | 22,792 matrices, 15,342,638 labellings: 0 failures (refined, plain); 338,494 failures in `loose` (any K) |
| A.3 | KL1 on built blocks | `blocks_of.py` then `blockkl.c` | 1,750 blocks, 89,194 covering multisets, 0 failures |
| A.4 | §6.1 example | `example_b.py`; `blockkl.c` on its block line | sparse, dem(U) = 2, I_X = ∅ for M ends {t2, t3, t4, 6}; KL1 holds (129 covering multisets) |
| A.5 | searches | `klsearch.c` (`data/kl/kls_*`), `klplant.c` (`data/kl/kp_*`) | no KL1 failure; no case (b) found by search |

Script hashes are listed in `FROZEN3.sha256` together with this file.

## Appendix B. Sources (paths relative to the repository root)

- `reports/585-next/wave4/qb5/PAPER.md` (frozen): Identity 1.3, Lemma 2.1, Theorem 6.1, Theorem 7.1, §8.4.
- `reports/585-next/wave4/qb5/PAPER2.md` (frozen): §1.1, §1.2 (B1, B2), Fact 2.1, Theorem 2.2, Corollary 2.3,
  Lemmas 3.1, 3.3, Definition 3.2, §4.1, Theorem 4.1, Proposition 5.1, Corollary 5.2, §6 certificate, §7.
- `reports/585-next/wave4/qb5/REVIEW.md` (FINAL): F1 to F7. `reports/585-next/wave4/qb5/REVIEW2.md` (FINAL):
  G1 to G3 and the converse of Corollary 2.3 (§2, optional items).
