# QB(5), round 2: the E5 pair statement holds for generic blocks

Author lane qb5, round 2, October 5, 2026. Status: frozen for independent review (SHA-256 in
`FROZEN2.sha256`). Not reviewed. This is rung 2 of the round-2 ladder: a proof of the E5 pair statement
of PAPER.md §8.4 under an extra hypothesis (every big-side vertex is *generic*, Definition 3.2) that holds
on every built instance, together with the smallest instance where the natural step fails (n = 28). It is
not a proof of QB(5). All proofs are written out; one finite lemma (Lemma 4.2, about 7-edge graphs) is
verified by computer, by two independent programs. No Lean, no `check.sh`, so nothing here is a
project-oracle PASS. Rungs: (a) for Fact 2.1, Theorem 2.2, Lemma 3.3, Corollary 3.4 and Proposition 5.1;
(a) with a computed lemma (Lemma 4.2) for Theorem 4.1 and Corollaries 5.2, 5.3; (b) for the certificate
of §6 and the data of §7.

PAPER.md (frozen, `FROZEN.sha256`) is cited by section and number; its referee report REVIEW.md is FINAL
(no mathematical error; Theorems 5.1 and 7.1 accepted). The fixes F1 to F7 of REVIEW.md are in force
here (§1.3).

## 0. Results at a glance

**E5 pair statement** (PAPER.md §8.4): every sparse E5 instance G without a 4-factor has p ∈ P, q ∈ Q
such that G − p − q has a 4-factor. It implies QB(5) (PAPER.md §8.4 and Theorem 7.1).

| Item | Statement | Verdict | Where |
|---|---|---|---|
| Fact 2.1 | a 4-factor of G − p − q forces p ∈ A, q ∈ D and uses exactly 4 cut edges | proved | §2 |
| **Theorem 2.2** | **pair criterion: G − p − q has a 4-factor iff dem_X(A1) + dem_Y(D1) ≤ 4 + e(A1, D1) for all A1 ⊆ A − p, D1 ⊆ D − q** | proved | §2 |
| Lemma 3.3, Cor. 3.4 | for generic p, q: G − p − q has a 4-factor iff 4 cut edges avoiding p, q cover every in-degree-3 big-side vertex other than p, q | proved | §3 |
| Lemma 4.2 | covering lemma for 7-edge cuts | computed by two independent programs | §4 |
| **Theorem 4.1** | **the E5 pair statement holds whenever every vertex of A and of D is generic** | proved, with Lemma 4.2 | §4 |
| Proposition 5.1 | a non-generic vertex forces a *core*; its block has at least 18 vertices | proved; exhaustive check for blocks ≤ 16 | §5 |
| Corollary 5.2 | the E5 pair statement holds for every n ≤ 26 | proved, with Lemma 4.2 | §5 |
| Corollary 5.3 | in a minimal QB(5) counterexample, every pair (p, q) with a covering 4-set has a non-generic end, in every 2-block decomposition | proved, with Lemma 4.2 | §5 |
| §6 | the natural step (covering ⇒ 4-factor) fails first at n = 28; certificate, both deciders | proved smallest, certified | §6 |
| §7 | no counterexample to the pair statement: 34,255 random instances (n = 20 to 26), 24 core instances (n = 28), 100 built | computed | §7 |

**Where a referee should attack first.**
1. Theorem 2.2: the separate minimization over C1 ⊆ C and B1 ⊆ B, and the identity
   Σ_b (4 − e(b, D1))^+ = 4|B| − 4|D1| + dem_Y(D1).
2. Lemma 3.3: the three cases, in particular the relevance case (ii).
3. Proposition 5.1: step 4 (|C''| ≥ 3) and step 6 (|T| ≥ 5 + κ).
4. §4.1: that the cut of G satisfies the hypotheses of Lemma 4.2, and that the two programs check
   exactly Lemma 4.2.
5. §6: the n = 28 certificate and the lower bound n ≥ 28.

## 1. Setting

### 1.1 Notation (PAPER.md §1, §6)

Graphs are finite, simple and bipartite. G is a *sparse E5 instance*: sides P, Q with |P| = |Q| = s,
Δ ≤ 6, D(P) = D(Q) = 5 (so e = 3n − 5), and g(S) = 6|S| − 2e(S) ≥ 12 for every S with 3 ≤ |S| ≤ n − 1.
Sparsity gives δ(G) ≥ 4 (g(V − v) = 4 + 2 deg v; PAPER.md §2, remark after Lemma 2.1).
If G has no 4-factor, PAPER.md Theorem 6.1 gives V = X ⊔ Y, X = A ∪ C, Y = B ∪ D (A, B ⊆ P; C, D ⊆ Q),
|A| = |C| + 2, |D| = |B| + 2, every vertex of C has degree 6 and all neighbors in A, every vertex of B has
degree 6 and all neighbors in D, |C|, |B| ≥ 4, and exactly 7 edges join X and Y, all between A and D.
If G has several such decompositions (several violations), fix any one; everything below is relative to it.

- E = E(A, D) is the *cut*, |E| = 7. For v ∈ A ∪ D, c_v is the number of cut edges at v; for A1 ⊆ A,
  c(A1) = Σ_{a∈A1} c_a and E(A1) is the set of cut edges at A1 (same for D).
- d_v is the *in-block degree* (deg_X v for v ∈ A, deg_Y v for v ∈ D), δ_v = 6 − d_v = c_v + def(v).
  Σ_{a∈A} δ_a = 6|A| − 6|C| = 12, and Σ_A c = 7, D(A) = 5. Same for D.
- L_A = {a ∈ A : d_a = 3}, L_D = {d ∈ D : d_d = 3} (*in-degree-3 vertices*).
- A pair (p, q) is *good* if G − p − q has a 4-factor, *bad* otherwise.
- For a set M of cut edges, m^A(A1) = |M ∩ E(A1)| and m^D(D1) = |M ∩ E(D1)|.

### 1.2 Basic facts

(B1) d_v ≥ 3 for v ∈ A ∪ D: if K ∈ {X, Y} is the block of v, K − v is proper with at least 3 vertices and
g(K − v) = 6 + 2d_v ≥ 12 (PAPER.md Identity 1.3, g(K) = 12). Hence c_v ≤ 3, and c_v = 3 forces d_v = 3,
deg v = 6.
(B2) v ∈ L_A has c_v ≥ 1 (deg v ≥ 4) and def(v) = 3 − c_v; so Σ_{v∈L_A} (3 − c_v) ≤ D(A) = 5. Same for D.

### 1.3 Corrections to PAPER.md (REVIEW.md F1 to F7), in force here

- F1 (Identity 1.2): the h-form reads h(A ∪ B) + h(A ∩ B) = h(A) + h(B) − e(A − B, B − A) (coefficient 1).
  Unused there and here.
- F2 (Corollary 7.2): (a) holds for instances with n ≥ 3 (s ≥ 2; s = 2, 3, 4 are empty); (b) assumes t ≥ 1
  (then t ≥ 4).
- F3 (§8.1): n = 15 is the computed smallest port-only failure: in the complete sparse C2 classes the
  number of graphs with every port bad is 0, 0, 3 at n = 11, 13, 15.
- F4 (§8.2): the n = 19 lattice split concerns α-petals of W-vertices (all of degree 6); for petals of
  ports the first split is at n = 21 (`review/data/cert_portsplit_n21.g6`).
- F5 (§8.3, §8.4, A.6): the 60 and 40 built E5 instances are 18 and 33 isomorphism classes; in §8.4 good
  pairs lie *only* in A × D, which is forced (Fact 2.1 below).
- F6 (Lemma 6.4): the census input F1 at n = 18 is `reports/585-next/STATE.md` line 31 (CENSUS.md line 37
  records it as projected); n = 17, 18 by one method. REVIEW.md §4 adds a second, independent check of all
  2-block graphs with c = 6, 7, 8 (every one has a 4-regular subgraph), so |X|, |Y| ≥ 20 and n ≥ 40 in
  PAPER.md Theorem 7.1 rest on two methods.
- F7 (A.1): "13, 818 E5 graphs" and "229,728" count two-colored outputs; as graphs, 9, 447 and 115,932.

## 2. The pair criterion

**Fact 2.1.** If G − p − q has a 4-factor H, then p ∈ A, q ∈ D, and H contains exactly 4 cut edges, none
at p or q.

*Proof.* Every vertex of C − q has all its neighbors in A, so summing H-degrees over A − p gives
4|A − p| = 4|C − q| + e_H(A − p, D − q), that is e_H(A, D) = 8 − 4[p ∈ A] + 4[q ∈ C]. This lies in
{0, ..., 7} and is a multiple of 4. Since [p ∈ A] ≤ 1, the only possibility is [p ∈ A] = 1, [q ∈ C] = 0,
e_H = 4. ∎

**Definition (demand).** For A1 ⊆ A and D1 ⊆ D,

    dem_X(A1) = 4|A1| − Σ_{c∈C} min(4, e(c, A1)),    dem_Y(D1) = 4|D1| − Σ_{b∈B} min(4, e(b, D1)).

**Theorem 2.2 (pair criterion).** For p ∈ A and q ∈ D, G − p − q has a 4-factor if and only if

    dem_X(A1) + dem_Y(D1) ≤ 4 + e(A1, D1)   for all A1 ⊆ A − p, D1 ⊆ D − q.

*Proof.* H = G − p − q has sides P' = P − p and Q' = Q − q of size s − 1. By PAPER.md Lemma 1.5, H has a
4-factor iff σ = e_H(A', Q' − C') − 4(|A'| − |C'|) ≥ 0 for all A' ⊆ P', C' ⊆ Q'. Write A' = A1 ∪ B1
(A1 ⊆ A − p, B1 ⊆ B) and C' = C1 ∪ (D − q − D1) (C1 ⊆ C, D1 ⊆ D − q), so Q' − C' = (C − C1) ∪ D1. B has no
neighbor in C, and the edges at p and q are absent from H but also from these counts (p ∉ A', q ∉ Q' − C'),
so

    σ = [e(A1, C − C1) + 4|C1| − 4|A1|] + [e(B1, D1) − 4|B1| + 4|D| − 4 − 4|D1|] + e(A1, D1).

The first bracket depends on C1 alone (given A1) and the second on B1 alone (given D1). Putting c ∈ C1
exactly when e(c, A1) > 4 minimizes the first: Σ_c min(4, e(c, A1)) − 4|A1| = −dem_X(A1). Putting b ∈ B1
exactly when e(b, D1) < 4 minimizes the second: 4|D| − 4 − 4|D1| − Σ_b (4 − e(b, D1))^+, and
Σ_b (4 − e(b, D1))^+ = 4|B| − Σ_b min(4, e(b, D1)) = 4|B| − 4|D1| + dem_Y(D1). With |D| − |B| = 2 the
minimum of σ over C1 and B1 is 4 − dem_X(A1) − dem_Y(D1) + e(A1, D1). ∎

**Corollary 2.3 (sufficient condition).** If M ⊆ E has |M| = 4, no edge at p or q, m^A(A1) ≥ dem_X(A1)
for all A1 ⊆ A − p and m^D(D1) ≥ dem_Y(D1) for all D1 ⊆ D − q, then G − p − q has a 4-factor.

*Proof.* dem_X(A1) + dem_Y(D1) ≤ |M ∩ E(A1)| + |M ∩ E(D1)| = |M ∩ (E(A1) ∪ E(D1))| + |M ∩ E(A1, D1)|
≤ 4 + e(A1, D1); apply Theorem 2.2. ∎

(With the converse direction, which follows from Theorem 2.2 by matroid intersection, (p, q) is good iff
such an M exists; this is not needed below and was checked on all 100 built instances,
`code/e5pairs.py`.)

## 3. Generic vertices

**Lemma 3.1.** (a) dem_X(A − p) = 4 for every p ∈ A, and dem_X(A) = 8. (b) If |A1| ≤ 4, then
dem_X(A1) = Σ_{a∈A1} (4 − d_a); in particular dem_X({a}) = 1 for a ∈ L_A. Same for Y.

*Proof.* (a) Every c ∈ C has e(c, A − p) ≥ 5, so dem_X(A − p) = 4(|A| − 1) − 4|C| = 4; dem_X(A) = 4|A| − 4|C|
= 8. (b) e(c, A1) ≤ 4 for every c, so Σ_c min(4, e(c, A1)) = e(C, A1) = Σ_{a∈A1} d_a. ∎

**Definition 3.2.** Let p ∈ A. A set A1 ⊆ A − p is *p-relevant* if dem_X(A1) + c(A − p − A1) ≥ 5. The vertex p
is *X-generic* if every p-relevant A1 with |A1| ≤ |A| − 2 has dem_X(A1) ≤ |A1 ∩ L_A|. Y-generic vertices of
D are defined in the same way with B, D, L_D.

The definition only involves X and the cut degrees c_a, a ∈ A.

**Lemma 3.3.** Let p ∈ A and let M ⊆ E have |M| = 4 and no edge at p.
(a) If p is X-generic and M covers L_A − p (every vertex of L_A − p is an end of an edge of M), then
m^A(A1) ≥ dem_X(A1) for every A1 ⊆ A − p.
(b) Conversely (for any p), if m^A(A1) ≥ dem_X(A1) for every A1 ⊆ A − p, then M covers L_A − p.

*Proof.* (a) Every edge of M has its A-end in A − p, so m^A(A − p) = 4. Let A1 ⊆ A − p.
(i) A1 = A − p (the only subset of A − p with |A1| ≥ |A| − 1): m^A = 4 = dem_X(A − p) by Lemma 3.1(a).
(ii) A1 not p-relevant: m^A(A1) = 4 − m^A(A − p − A1) ≥ 4 − c(A − p − A1) ≥ dem_X(A1).
(iii) A1 p-relevant, |A1| ≤ |A| − 2: dem_X(A1) ≤ |A1 ∩ L_A| by genericity, and each vertex of
A1 ∩ L_A ⊆ L_A − p is an end of an edge of M, so |A1 ∩ L_A| ≤ m^A(A1).
(b) For a ∈ L_A − p, m^A({a}) ≥ dem_X({a}) = 1 (Lemma 3.1(b)). ∎

**Corollary 3.4.** Let p ∈ A and q ∈ D. If G − p − q has a 4-factor, then some M ⊆ E with |M| = 4 and no
edge at p or q covers (L_A − p) ∪ (L_D − q). If p is X-generic and q is Y-generic, the converse holds.

*Proof.* Let H be a 4-factor of G − p − q and M its 4 cut edges (Fact 2.1). A vertex a ∈ L_A − p has
H-degree 4 and at most d_a = 3 edges inside X, so it is an end of an edge of M; same for L_D − q. The
converse is Lemma 3.3(a), its mirror for Y, and Corollary 2.3. ∎

## 4. The pair statement for generic blocks

**Lemma 4.2 (covering lemma; computed).** Let E be a set of 7 edges of a simple bipartite graph with sides
A and D, every vertex in at most 3 edges of E, and c_v the number of edges of E at v. Let L_A ⊆ A and
L_D ⊆ D consist of vertices with c_v ≥ 1, contain every vertex with c_v = 3, and satisfy
Σ_{v∈L_A} (3 − c_v) ≤ 5 and Σ_{v∈L_D} (3 − c_v) ≤ 5. Then there are p ∈ A and q ∈ D, each an end of an
edge of E, and M ⊆ E with |M| = 4 and no edge at p or q, such that M covers (L_A − p) ∪ (L_D − q).

*Verification.* Two programs that share no code (Appendix A, A.2 and A.3):
(1) `code/cover_check.c` enumerates every labelled 7-edge set between {0, ..., 6} and {0, ..., 6} with
degrees at most 3 and non-increasing degree sequences on both sides (every 7-edge bipartite graph is
isomorphic to one of these; 22,792 graphs), every admissible pair (L_A, L_D) (15,342,638 in all), and
searches p, q and M directly. With p, q restricted to ends of edges of E: 0 failures; with a vertex
without cut edges also allowed: 0 failures.
(2) `code/generic_check.py` takes the 142 isomorphism classes from nauty `genbg -d1:1 -D3:3 n1 n2 7:7`
(3 ≤ n1, n2 ≤ 7) and all 36,339 admissible labellings, decides every pair (p, q) both by the rule
"(a) c_p + c_q − [pq ∈ E] ≥ 4, or (b) some d ∈ L_D − q has c_d = 1 and pd ∈ E, or (c) the mirror of (b), or
(d) some A1 ⊆ L_A − p, D1 ⊆ L_D − q have |A1| + |D1| − e(A1, D1) ≥ 5" (the obstruction form, by
matroid-intersection duality) and by direct search for M; the two agree on every pair, and every
labelling has a pair with neither obstruction, with or without vertices outside the cut. ∎

### 4.1 The cut of G satisfies the hypotheses of Lemma 4.2

E is a set of 7 edges of the simple graph G between A and D; c_v ≤ 3 by (B1). L_A, L_D (§1.1) consist of
vertices with c_v ≥ 1 (B2), contain every vertex with c_v = 3 (B1), and satisfy the budget (B2).

**Theorem 4.1.** Let G be a sparse E5 instance without a 4-factor, with a 2-block decomposition as in §1.1.
If every vertex of A is X-generic and every vertex of D is Y-generic, then G − p − q has a 4-factor for
some p ∈ A, q ∈ D. In particular G has a nonempty 4-regular subgraph.

*Proof.* Lemma 4.2 (applicable by §4.1) gives p, q and M; Corollary 3.4 (converse part) gives the 4-factor.
∎

## 5. Non-generic vertices: cores

**Proposition 5.1.** Let p ∈ A be not X-generic: some p-relevant A1 ⊆ A − p with |A1| ≤ |A| − 2 has
k := dem_X(A1) > |A1 ∩ L_A|. Put T = A − A1 (so p ∈ T), C' = {c ∈ C : e(c, T) ≥ 3}, C'' = C − C',
t = |T| and κ = t − |C'|. Then:
(a) 1 ≤ k ≤ 3 and −1 ≤ κ ≤ 2 − k; e(C', A1) = 8 − 4κ − k; |A1| = |C''| + 2 − κ;
(b) δ(T) = 2κ + 8 − k − e(C'', T), and e(C'', T) + δ_p ≤ 2κ + 3; c(T − p) ≥ 5 − k; |A1 ∩ L_A| ≤ k − 1;
(c) |C''| ≥ 3 and e(C'', T) ≥ 3κ;
(d) t ≥ 5 + κ, and |X| = 2t + 2|C''| + 2 − 2κ ≥ 18.
We call (T, k) a *core* (of X, at p).

*Proof.* k ≥ 1 because k > |A1 ∩ L_A| ≥ 0.
Step 1 (the demand in terms of C'). A vertex of C'' has e(c, T) ≤ 2, so e(c, A1) ≥ 4; a vertex of C' has
e(c, A1) ≤ 3. Hence k = 4|A1| − 4|C''| − e(C', A1). Since |A| − |C| = 2,
|A1| − |C''| = (|A| − t) − (|C| − |C'|) = 2 − κ, so e(C', A1) = 8 − 4κ − k and |A1| = |C''| + 2 − κ.
Step 2 (t ≥ 3 and κ ≤ 2 − k). t ≥ 2 since |A1| ≤ |A| − 2. If t = 2 then C' = ∅ and k = 4(2 − κ) − 0 with
κ = t = 2, so k = 0; hence t ≥ 3. For S = T ∪ C' (|S| ≥ 3, S ⊆ X ≠ V) sparsity gives e(S) ≤ 3|S| − 6, and
e(S) = e(C', T) = 6|C'| − e(C', A1). So 6|C'| − 8 + 4κ + k ≤ 3t + 3|C'| − 6, that is 3|C'| − 3t + 4κ + k ≤ 2,
that is κ + k ≤ 2.
Step 3 (δ(T) and relevance). The in-block neighbors of T lie in C, so
Σ_{x∈T} d_x = e(C', T) + e(C'', T) = 6|C'| − 8 + 4κ + k + e(C'', T) and
δ(T) = 6t − Σ_T d = 6κ + 8 − 4κ − k − e(C'', T) = 2κ + 8 − k − e(C'', T). Relevance says
c(T − p) = c(A − p − A1) ≥ 5 − k, and c_v ≤ δ_v for every v, so δ(T) − δ_p ≥ 5 − k, which is
e(C'', T) + δ_p ≤ 2κ + 3. The left side is nonnegative, so κ ≥ −1, and then k ≤ 2 − κ ≤ 3. |A1 ∩ L_A| ≤ k − 1
is the hypothesis k > |A1 ∩ L_A|.
Step 4 (|C''| ≥ 3). If C'' = ∅, every c has e(c, A1) ≤ 3 and k = 4|A1| − e(C, A1) = Σ_{a∈A1} (4 − d_a),
which is at most |A1 ∩ L_A| because d_a ≥ 3 (B1); this contradicts k > |A1 ∩ L_A|. So C'' ≠ ∅, and since a
vertex c ∈ C'' has e(c, A1) ≥ 4, |A1| ≥ 4 and e(c, T) ≥ 6 − |A1|. If |C''| = 1, then |A1| = 3 − κ ≥ 4 forces
κ = −1, |A1| = 4, e(C'', T) ≥ 2 > 2κ + 3. If |C''| = 2, then |A1| = 4 − κ ≥ 4 forces κ ≤ 0; for κ = −1,
|A1| = 5 and e(C'', T) ≥ 2 > 1; for κ = 0, |A1| = 4 and e(C'', T) ≥ 4 > 3. Each contradicts Step 3.
Step 5 (e(C'', T) ≥ 3κ). Q = A1 ∪ C'' has |Q| ≥ 3 and Q ≠ V, e(Q) = 6|C''| − e(C'', T), so
12 ≤ g(Q) = 6(|A1| − |C''|) + 2e(C'', T) = 12 − 6κ + 2e(C'', T).
Step 6 (t ≥ 5 + κ). e(C', T) ≤ t|C'| = t(t − κ) and e(C', T) = 6(t − κ) − 8 + 4κ + k, so
(6 − t)(t − κ) ≤ 8 − 4κ − k ≤ 7 − 4κ. For κ = −1 this excludes t = 3 (12 > 11); for κ = 0 it excludes
t = 3, 4 (9, 8 > 7); for κ = 1 it excludes t = 3, 4, 5 (6, 6, 4 > 3). With t ≥ 3, t ≥ 5 + κ.
Step 7. |X| = |A| + |C| = (t + |A1|) + (|C'| + |C''|) = 2t + 2|C''| + 2 − 2κ ≥ 2(5 + κ) + 6 + 2 − 2κ = 18. ∎

*Exhaustive confirmation* (`code/gdl_small.c`): every 2-block graph with |C| = 4, 5, 6, 7 (genbg
`-d6:0 -D6:6 c c+2 6c:6c`: 1, 7, 197, 18,208 graphs; 1, 3, 94, 11,842 with all d_a ≥ 3 and sparse) has
0, 0, 2, 442 sets A1 with dem_X(A1) > |A1 ∩ L_A| and |A1| ≤ |A| − 2, and none of them is p-relevant for any
p and any cut-degree vector allowed by §1.2 (c_a between max(0, δ_a − 2) and min(3, δ_a), Σ c_a = 7).

Example (κ = −1, t = 4, |C''| = 3, k = 2, |X| = 18): T ∪ C' = K_{4,5}, A1 ∪ C'' = K_{3,6}, and the five
C'-vertices send 10 edges to A1, one or two to each A1-vertex; dem_X(A1) = 2 and L_A = ∅ (§6).

**Corollary 5.2.** Every sparse E5 instance without a 4-factor on n ≤ 26 vertices has p ∈ A, q ∈ D with a
4-factor in G − p − q. More generally the E5 pair statement holds whenever both blocks have at most 16
vertices.

*Proof.* |X|, |Y| ≥ 10 (PAPER.md Theorem 6.1) and |X| + |Y| = n ≤ 26 give |X|, |Y| ≤ 16. By
Proposition 5.1(d) and its mirror every vertex of A and of D is generic; apply Theorem 4.1. ∎

**Corollary 5.3 (minimal counterexample).** Let G be a minimal counterexample to QB(5) (PAPER.md
Theorem 7.1, with F6: n ≥ 40). For every 2-block decomposition of G and every pair (p, q) for which some
M ⊆ E covers (L_A − p) ∪ (L_D − q) as in Lemma 4.2, p is not X-generic or q is not Y-generic. Such pairs
exist (Lemma 4.2), so G has a core (T, k) as in Proposition 5.1 in X or in Y.

*Proof.* A minimal counterexample is a sparse E5 instance without a 4-factor in which no G − p − q has a
4-factor (PAPER.md Lemma 2.1, Theorem 7.1). Apply Corollary 3.4 to a covering pair. ∎

*Remark 5.4.* The proof of Theorem 2.2 applied to G itself (no vertex removed) shows that the least
slack of PAPER.md Lemma 1.5 over the sets A' = A1 ∪ B1, C' = C1 ∪ (D − D1) is
8 − dem_X(A1) − dem_Y(D1) + e(A1, D1). Every violation of G has slack −1 (PAPER.md Theorem 6.1), so
taking D1 = D gives dem_X(A1) ≤ c(A1) + 1, and equality makes (A1, {c ∈ C : e(c, A1) ≥ 5}) a violation
whose X-side lies inside X. So if the decomposition is chosen with X inclusion-minimal among the X-sides of
violations, dem_X(A1) ≤ c(A1) for every A1 ⊊ A, and a core of X also has c(A1) ≥ k. When G has several
violations only one of the two blocks can be made minimal this way.

## 6. Where the natural step fails: n = 28

The *natural step* is the converse in Corollary 3.4: a 4-set M of cut edges avoiding p and q that covers
(L_A − p) ∪ (L_D − q) yields a 4-factor of G − p − q.

**Theorem 6.1.** The natural step holds for every pair in every sparse E5 instance without a 4-factor on
n ≤ 26 vertices, and it fails for some pair of some such instance on n = 28 vertices.

*Proof.* If the step fails at (p, q), Corollary 3.4 shows that p or q is not generic, so by
Proposition 5.1 one block has at least 18 vertices; the other has at least 10, so n ≥ 28. The instance
below has n = 28. ∎

**Certificate** `code/data/cert_core_n28.g6` (graph6, 28 vertices, 79 edges; readable form in
`code/data/cert_core_n28.txt`):

    [???????Fs]K}_|C]I?^_B{?No????????????????F_??]G??{AO?{I??]C@?F_

- X: A = {0, ..., 9}, C = {10, ..., 17}. T = {0, 1, 2, 3}, C' = {10, ..., 14} with T ∪ C' = K_{4,5};
  N(10) = N(12) = {0, 1, 2, 3, 4, 6}, N(11) = {0, 1, 2, 3, 7, 8}, N(13) = {0, 1, 2, 3, 5, 9},
  N(14) = {0, 1, 2, 3, 7, 9}; C'' = {15, 16, 17}, each adjacent to A1 = {4, ..., 9}.
- Y = K_{4,6}: B = {18, ..., 21}, D = {22, ..., 27}.
- Cut: 0-27, 1-26, 2-24, 3-26, 4-25, 7-25, 8-27. In-block degrees: 5 on A except d_5 = d_8 = 4; 4 on D.
  L_A = L_D = ∅.
- Pair (p, q) = (0, 25): M = E − E(0) − E(25) = {1-26, 2-24, 3-26, 8-27} has 4 edges and covers
  L_A ∪ L_D = ∅, so the natural step predicts a 4-factor; but G − 0 − 25 has none (maximum flow 51 of 52).
  Witness for Theorem 2.2: A1 = {4, ..., 9} with dem_X(A1) = 2 (p-relevant: 2 + c({1, 2, 3}) = 5), and
  D1 = D − 25 with dem_Y(D1) = 4, e(A1, D1) = 1: 2 + 4 − 1 = 5 > 4. Vertex 0 is not X-generic: (T, 2) is a
  core with κ = −1, t = 4, |C''| = 3.
- Both deciders (Appendix A.4): sparse, Δ = 6, δ = 4, e = 3n − 5, no 4-factor, (0, 25) bad. The pair
  statement still holds here: 56 good pairs, for example (0, 22) and (4, 22).

So genericity, not the pair statement, is what fails first.

## 7. Evidence for the full pair statement, and the exact residual

**Data.** No sparse E5 instance without a 4-factor and without a good pair has been found:
- `code/pairsearch.c` (random 2-blocks with |C|, |B| = 4 to 7, random cuts, with and without matching
  number ≤ 3, with and without twin neighborhoods): 34,255 sparse instances on 20 to 26 vertices in 54
  runs (duplicates across runs not removed), fewest good pairs 23. Corollary 5.2 now proves these sizes;
  the runs agree with it.
- `code/gen_core.py`: 24 instances on 28 vertices with the core of §6 planted: sparse, no 4-factor, 54 to
  60 good pairs each (`e5check.c`); `generic_inst.py` (networkx) re-decided every pair, found every
  non-generic vertex inside the planted T, and found the covering rule wrong on 20 pairs, all at
  non-generic vertices.
- The 100 built instances of PAPER.md §8.3 (18 + 33 classes, F5): 35 to 47 good pairs; every vertex is
  generic (as Proposition 5.1 requires for n ≤ 26).
- 750 random instances (`code/data/search/dump_mixed.g6`, n ≤ 26): every vertex generic; on every pair
  the obstruction rule of Lemma 4.2's program (2) agrees with Theorem 2.2's criterion, and Theorem 2.2's
  criterion agrees with the maximum flow on every pair of the first 60 instances.

**Exact residual.** By Theorem 4.1 and Corollary 5.3, QB(5) follows from either of:
(R1) in every sparse E5 instance without a 4-factor, some covering pair (p, q) of Lemma 4.2 has p and q
generic;
(R2) a minimal counterexample has no core (Proposition 5.1) in either block.
The constraints of Proposition 5.1 alone do not give (R1): a permissive model that admits every vertex
set satisfying them as a core (`code/core_model.py`) can make every vertex of one side non-generic, even
with Remark 5.4. So a proof needs more structure of cores (how two cores of one block interact) or
minimality.

**Next steps.**
1. Cores in one block: a core (T, k) makes p ∈ T non-generic only if c(T − p) ≥ 5 − k, and the block
   has 7 cut edges in all; bound how much of A two or more cores can make non-generic, and show that a
   covering pair survives among the generic vertices (the model of `code/core_model.py` ignores how two
   cores of one block share C-vertices).
2. Minimality on the parts of a core: Q = A1 ∪ C'' has κ(Q) = 2 − κ and g(Q) = 12 − 6κ + 2e(C'', T); for
   κ = 0 and e(C'', T) = 0 it is a 2-block inside X, joined to the rest by e(C', A1) + c(A1) edges.
3. With (R1) or (R2), PAPER.md §8.4 and Theorem 7.1 finish QB(5).

## Appendix A. Computations

All code is in `reports/585-next/wave4/qb5/code/`, data in `code/data/` and `code/data/search/`. C tools
built with `/usr/bin/clang -O3`; Python is `/private/tmp/erdos585-research-venv/bin/python` (networkx
3.6.1); nauty genbg 2.9.3 at `~/.cache/erdos585/nauty2_9_3/genbg`. Total compute: well under one
core-hour.

| # | Check | Code and input | Result |
|---|---|---|---|
| A.1 | Fact 2.1 and two equivalent forms of the criterion (a set function Ψ via the min cut, and the common realizable 4-set of cut edges) on the built instances | `e5pairs.py data/e5_n22.g6`, `data/e5_n24.g6` (networkx max flow) | 100 of 100: good pairs only in A × D; both forms = flow on every pair (`data/e5pairs_check.txt`) |
| A.1b | Theorem 2.2 (demand form) against max flow | `generic_inst.py` (asserts, first 60 instances of each input), `witness.py` (asserts, every pair) | no disagreement on `dump_mixed.g6` (60), `core28.g6` (24), `zzbad_5_6.txt` (5) |
| A.2 | Lemma 4.2, first program | `cover_check.c` (own enumeration; `./cover_check 0`, `./cover_check 1`) | 22,792 labelled graphs, 15,342,638 labellings, 0 failures in both modes |
| A.3 | Lemma 4.2, second program | `generic_check.py` (genbg classes; rule (a)-(d) asserted equal to direct search on every pair) | 142 graphs, 36,339 labellings, 0 failures with and without outside vertices |
| A.4 | §6 certificate | `e5check.c` (C: own max flow, Gray-code sparsity over all 2^28 sets; `./e5check all < data/cert_core_n28.g6`) and `cert_core.py data/cert_core_n28.g6 0 25` (networkx) | both: sparse, no 4-factor, (0, 25) bad; 56 good pairs (e5check); witness as in §6 |
| A.5 | Proposition 5.1, blocks ≤ 16 | `gdl_small.c` on genbg `-q -d6:0 -D6:6 c c+2 6c:6c`, c = 4..7 | relevant non-generic sets: 0 |
| A.5b | Proposition 5.1 (a)-(d) on actual cores | `prop51_check.py data/search/core28.g6 data/search/dump_mixed.g6 data/e5_n22.g6 data/e5_n24.g6` | 72 relevant non-generic (p, A1), all in `core28.g6`; every assertion holds |
| A.6 | §7 random search | `pairsearch.c` via `search1.sh`, `stats1.sh` (`pairsearch_stats.c`) | 34,255 sparse instances, fewest good pairs 23; logs `data/search/ps_*.err`, `st_*.err` |
| A.7 | §7 core instances | `gen_core.py 12 1 3`, `gen_core.py 12 2 4` → `data/search/core28.g6`; `e5check`, `generic_inst.py` | 24 sparse, no 4-factor, 54 to 60 good pairs; mismatches of the covering rule only at core vertices |
| A.8 | §7 genericity in random instances | `generic_inst.py data/search/dump_mixed.g6` | 750 instances: every vertex generic; rule = Theorem 2.2 on every pair; = flow on the first 60 |
| A.9 | §7 permissive core model | `core_model.py` (with and without `minimal`) | the proved core constraints alone allow a whole side to be non-generic |

Script hashes are listed in `FROZEN2.sha256` together with this file and the certificate.

## Appendix B. Sources (paths relative to the repository root)

- `reports/585-next/wave4/qb5/PAPER.md` (SHA-256 1a8cfec5...38380b2, frozen): §1 (notation, Identities 1.1,
  1.3, Lemma 1.5), §2 (Lemma 2.1 and the remark on δ ≥ 4), §6 (Theorem 6.1, Lemmas 6.2 to 6.4), §7
  (Theorem 7.1), §8.3, §8.4.
- `reports/585-next/wave4/qb5/REVIEW.md` (FINAL): fixes F1 to F7, §4 (independent 2-block check for
  c = 6, 7, 8), `review/data/cert_portsplit_n21.g6`.
- `reports/585-next/STATE.md` line 31 (F1 at n = 18), `reports/585-next/census/CENSUS.md` lines 34-37.
