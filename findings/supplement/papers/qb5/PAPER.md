# QB(5): every sparse C2 instance has a good vertex, so a minimal counterexample is E5

Author lane qb5, wave 4, October 5, 2026. Status: frozen for independent review (SHA-256 in
`FROZEN.sha256`). Written proofs with computational checks of the identities, of the minimality-free
core lemma and of every certificate instance (Appendix A). Not reviewed. No Lean, no `check.sh`, so
nothing here is a project-oracle PASS. Rungs: (a) for Lemmas 2.1-6.4 and Theorems 5.1, 6.1, 7.1 (on
paper); (b) for the instances of §8 and Appendix A. Ladder position: rung 2 (a reduction of QB(5) to an
exactly stated residual), not rung 1.

## 0. Results at a glance

QB(5): every finite simple bipartite graph with maximum degree at most 6, n ≥ 3 vertices and at least
3n − 5 edges contains a nonempty 4-regular subgraph.

| Item | Statement | Verdict | Where |
|---|---|---|---|
| Lemma 2.1 | a minimal counterexample is sparse (g ≥ 12 on proper sets of size ≥ 3), has δ ≥ 4, and is an E5 or a C2 instance | proved | §2 |
| Lemma 3.2 | C2: a violation at a W-vertex has one of five types α, β1a, β1b, β2, γ | proved | §3 |
| Lemmas 4.1, 4.2 | tight κ = 1 sets around the deficient U-vertices form a lattice unless a W-small 2-block contains those vertices; such a 2-block has exactly 10 boundary edges and a 3-block complement | proved | §4 |
| **Theorem 5.1** | **core lemma for C2: every sparse C2 instance has a W-vertex w with a 4-factor in G − w** | proved | §5 |
| Theorem 6.1 | a sparse E5 instance without a 4-factor is two 2-blocks joined by exactly 7 edges | proved | §6 |
| Lemmas 6.2-6.4 | in a minimal counterexample of E5 type: the 7 edges contain no 4-matching; the shift constraints; both blocks have ≥ 14 vertices (≥ 20 with the census) | proved | §6 |
| **Theorem 7.1** | **a minimal counterexample to QB(5) is an E5 block pair as in §6; n is even and n ≥ 28 (n ≥ 40 with the census)** | proved | §7 |
| Corollary 7.2 | QB(5) holds iff every sparse E5 instance has a 4-regular subgraph; C0^(2) (2-blocks have 4-regular subgraphs) implies QB(5) | proved | §7 |
| §8 | where the C1 argument fails, with the smallest instances: n = 15 (ports only), n = 19 (the petal lattice), n = 22 (E5 gluing); each size is proved smallest | computed, minimality of the sizes proved | §8 |

**Where a referee should attack first.**
1. Lemma 3.2: the signs in Lemma 3.1, and that ε contains D(C), which is what forces D(C) = 0 in types
   α, β1a and β2 (so their petals contain every deficient U-vertex).
2. Theorem 5.1(ii) and (iv): the choice of a maximal 2-block T, the pairwise "meet exactly in T"
   claims, and the budget of 10 boundary edges.
3. Theorem 5.1(iii): the closure of the (14, 2) family and the final κ count.
4. Theorem 6.1 and Lemma 6.3: the shift of a vertex with three cut edges and the two edge-added
   minimality calls.
5. Theorem 7.1: that "every W-vertex is bad" is the only use of minimality in the C2 case, beyond
   sparsity.

## 1. Setting and tools

All graphs are finite, simple and bipartite with sides U and W. For S ⊆ V: S_U = S ∩ U, S_W = S ∩ W,
e(S) the number of edges inside S, and

    g(S) = 6|S| − 2e(S),   κ(S) = |S_U| − |S_W|,   h(S) = 6|S_W| − e(S),

so h(S) is the deficiency of S_W inside G[S]. D(Z) = Σ_{v∈Z} (6 − deg v) is the deficiency in G, and
def(v) = 6 − deg v.

**Identity 1.1** (C1-PAPER Identity 1.1). 6|S_U| − e(S) = h(S) + 6κ(S) and g(S) = 2h(S) + 6κ(S).
Hence |κ(S)| ≤ g(S)/6; κ(S) = g(S)/6 iff h(S) = 0, that is, every vertex of S_W has degree 6 and all
its neighbors in S; κ(S) = −g(S)/6 iff the same holds for S_U.

**Identity 1.2** (C1-PAPER Identity 1.2). g(A ∪ B) + g(A ∩ B) = g(A) + g(B) − 2e(A − B, B − A), the
same identity holds for h, and κ is modular. For disjoint A, B: g(A ∪ B) = g(A) + g(B) − 2e(A, B).

**Identity 1.3** (C1-PAPER Identity 1.3). g(S − v) = g(S) − 6 + 2deg_S(v) and, for v ∉ S,
g(S + v) = g(S) + 6 − 2e(v, S).

**Identity 1.4.** h(S) = D(S_W) + e(S_W, U − S_U) ≥ D(S_W).

**Lemma 1.5 (flow criterion; C1-PAPER Lemma 1.4, reviewed).** A bipartite graph with sides P, Q of
equal size has a spanning 4-regular subgraph (a 4-factor) iff e(A, Q − C) ≥ 4(|A| − |C|) for all
A ⊆ P, C ⊆ Q. If Δ ≤ 6, the slack σ = e(A, Q − C) − 4k (k = |A| − |C|) equals 2k − D_A + ε with
ε = D_C + e(P − A, C), deficiencies taken in that graph, and a violation (σ < 0) has k ≥ 1.

**Definitions.** G is *sparse* if g(S) ≥ 12 for every S with 3 ≤ |S| ≤ n − 1. A set S is *tight* if
g(S) = 12. A *j-block* is a set S with |κ(S)| = j whose smaller side is saturated inside S (every
vertex of it has degree 6 and all neighbors in S); by Identity 1.1 this is the same as g(S) = 6j. A
2-block with κ = 2 is *W-small*, with κ = −2 *U-small*. In a sparse graph a 1-block has one vertex.

A **C2 instance** has sides U (s vertices) and W (s + 1), Δ ≤ 6 and D(U) = 2, hence D(W) = 8 and
e = 6s − 2 = 3n − 5. Its deficient U-vertices form Z_U = {u0} (deg u0 = 4) or Z_U = {u1, u2}
(degree 5 each). A **port** is a W-vertex of degree at most 5. A W-vertex w is *good* if G − w has a
4-factor and *bad* otherwise. An **E5 instance** has sides P, Q of equal size s, Δ ≤ 6 and
D(P) = D(Q) = 5, so e = 6s − 5 = 3n − 5.

## 2. The minimal counterexample

**Lemma 2.1.** Let G be a counterexample to QB(5) with n minimal, then e minimal. Then
(a) n ≥ 11 and e = 3n − 5;
(b) G is sparse and δ(G) ≥ 4;
(c) G is an E5 instance or a C2 instance;
(d) an E5 instance G has no 4-factor, and in a C2 instance G every W-vertex is bad.

*Proof.* (a) For 3 ≤ n ≤ 9 a bipartite graph has at most n²/4 < 3n − 5 edges, and at n = 10 only
K_{5,5}, which contains K_{4,4}, has 25 edges. If e > 3n − 5, deleting an edge gives a counterexample
with the same n and fewer edges. (b) For 3 ≤ |S| ≤ n − 1, G[S] is bipartite with Δ ≤ 6 and no
4-regular subgraph, so minimality of n gives e(S) ≤ 3|S| − 6, that is g(S) ≥ 12. For a vertex v,
Identity 1.3 gives 12 ≤ g(V − v) = 4 + 2deg v. (c) g(V) = 10. C1-PAPER Identity 1.1 writes g(V) = 2d + 6j
with j the difference of the side sizes and d the deficiency of the smaller side; so (j, d) = (0, 5)
(both sides have deficiency 5) or (1, 2) (the smaller side has deficiency 2, the larger 8).
(d) A 4-factor of G, or of G − w (2s ≥ 2 vertices), is a nonempty 4-regular subgraph of G. ∎

In a sparse C2 or E5 instance δ ≥ 4 follows from sparsity alone, as in (b).

## 3. C2: the violations at a W-vertex

**Lemma 3.1 (cut identity; C1-PAPER Lemma 3.1 with D(U) = 2).** Let G be a C2 instance, w ∈ W,
A ⊆ W − w, C ⊆ U, k = |A| − |C|, σ the slack of (A, C) in the balanced graph G − w, and
ε = D(C) + e(C, W − A). Then σ = 2k − D_A + ε, and Q = V − A − C satisfies

    g(Q) = 10 + 2k + 2σ − 2D(C),   κ(Q) = k − 1,   h(Q) = 8 − 2k + σ − D(C).

*Proof.* The proof of C1-PAPER Lemma 3.1 uses D(U) only through Σ_{u∈U−C} deg u = 6|U − C| − D(U) + D(C)
and gives g(Q) = 6 + 2D(U) + 2k + 2σ − 2D(C) and κ(Q) = k − 1 for every value of D(U); the deficiency
of C in G − w is D(C) + e(w, C), which makes ε as stated. h(Q) = (g(Q) − 6κ(Q))/2. ∎

**Lemma 3.2 (types).** Let G be a sparse C2 instance, w ∈ W bad, and (A, C) a violation of G − w,
Q = V − A − C. Then exactly one of the following holds.

| Type | k | σ | D(C) | ε, def(w) | D_A | (g, κ, h) of Q |
|---|---|---|---|---|---|---|
| γ | 1 | −1 | 0 | Q = {w, u0}, deg u0 = 4, w ~ u0 | 8 − def(w) | (10, 0, 5) |
| α | 2 | −1 | 0 | ε ≤ 3 − def(w) | 5 + ε | (12, 1, 3) |
| β1a | 3 | −1 | 0 | ε + def(w) ≤ 1 | 7 + ε | (14, 2, 1) |
| β1b | 3 | −1 | 1 | ε = 1, def(w) = 0 | 8 | (12, 2, 0) |
| β2 | 3 | −2 | 0 | ε = 0, def(w) = 0 | 8 | (12, 2, 0) |

In every type except β1b the petal Q contains Z_U. A port has a petal of type γ, α or β1a only, and in type
β1a a port y has def(y) = 1, ε = 0 and D(Q_W) = 1: y is the only port in Q.

*Proof.* Q contains w and U − C, and U − C ≠ ∅ (C = U would give |A| = s + k > s = |W − w|), so
|Q| ≥ 2; Q ≠ V because k ≥ 1 forces A ≠ ∅. A ⊆ W − w gives D_A ≤ 8 − def(w); σ ≤ −1 gives
D_A = 2k − σ + ε ≥ 2k + 1 + ε, so k ≤ 3; and ε ≥ D(C) ≥ 0.
If |Q| = 2, then U − C = {u'}, |C| = s − 1 and |A| ≤ s, so k = 1, A = W − w and
σ = deg u' − e(w, u') − 4 ≤ −1. With deg u' ≥ 4 (δ ≥ 4) this gives deg u' = 4 and w ~ u'; as D(U) = 2,
Z_U = {u'} = {u0}, and C = U − u0 has D(C) = 0: type γ.
If |Q| ≥ 3, sparsity and Lemma 3.1 give k + σ − D(C) ≥ 1. For k = 1 this needs σ ≥ D(C) ≥ 0, which is
impossible. For k = 2 it gives σ = −1 and D(C) = 0: type α, with D_A = 5 + ε ≤ 8 − def(w). For k = 3
it gives σ ≥ D(C) − 2 ≥ −2. If σ = −1 then D_A = 7 + ε ≤ 8 − def(w) and D(C) ≤ min(1, ε): β1a
(D(C) = 0) or β1b (D(C) = 1, which forces ε = 1 and def(w) = 0). If σ = −2 then D(C) = 0 and
D_A = 8 + ε ≤ 8 − def(w): β2. The table values follow from Lemma 3.1. D(C) = 0 means C contains no
deficient U-vertex, so Z_U ⊆ U − C ⊆ Q. For a port (def ≥ 1) only γ, α and β1a remain; in β1a,
def = 1 and ε = 0, so D(Q_W) = D(W) − D_A = 8 − 7 = 1 = def(y). ∎

β1b needs a U-vertex of deficiency 1, so it does not occur when Z_U = {u0}. The petals of types β1b
and β2 are W-small 2-blocks (g = 12, κ = 2).

## 4. Tight sets around the deficient U-vertices

**Lemma 4.1 (lattice).** Let G be a sparse C2 instance and Q, Q' sets with 4 ≤ |Q|, |Q'| ≤ n − 1,
g = 12, κ = 1 and Z_U ⊆ Q ∩ Q'. Then |Q ∩ Q'| ≥ 3, Q ∪ Q' ≠ V, g(Q ∩ Q') = g(Q ∪ Q') = 12, and
(κ(Q ∩ Q'), κ(Q ∪ Q')) is (1, 1), (2, 0) or (0, 2). In the last two cases Q ∩ Q' or Q ∪ Q' is a
W-small 2-block containing Z_U.

*Proof.* For u ∈ Z_U and R ∈ {Q, Q'}, R − u is proper with at least 3 vertices, so
12 ≤ g(R − u) = 6 + 2deg_R(u) and deg_R(u) ≥ 3. If Z_U = {u0} (degree 4), u0 has at least 2 common
neighbors in Q ∩ Q'; if Z_U = {u1, u2} (degree 5), u1 has at least one. Either way |Q ∩ Q'| ≥ 3.
If Q ∪ Q' = V, then κ(Q ∩ Q') = 1 + 1 − κ(V) = 3, so g(Q ∩ Q') ≥ 18 by Identity 1.1, while Identity
1.2 gives g(Q ∩ Q') ≤ 24 − g(V) = 14. So both sets are proper with at least 3 vertices, both have
g ≥ 12, and the sum is at most 24: both are tight. κ(Q ∩ Q') + κ(Q ∪ Q') = 2 and a tight set has
|κ| ≤ 2. A tight set with κ = 2 is a W-small 2-block, and both sets contain Z_U. ∎

In C1 (C1-PAPER Lemma 4.2) the petals have g = 10, which allows only κ ≤ 1, and the lattice closes.
Here g = 12 allows κ = 2, and the (2, 0) split occurs (§8.2).

**Lemma 4.2 (W-small 2-blocks on Z_U).** Let G be a sparse C2 instance and T a W-small 2-block
(3 ≤ |T| ≤ n − 1, g(T) = 12, κ(T) = 2) with Z_U ⊆ T. Put B = V − T. Then:
(a) every vertex of T_W has degree 6 and all its neighbors in T_U; so every port lies in B_W;
(b) every edge leaving T joins T_U to B_W, and there are exactly 10 of them;
(c) g(B) = 18, κ(B) = −3, and every vertex of B_U has degree 6 and all its neighbors in B_W;
(d) |T_U| ≥ 6, |T| ≥ 10, |B_U| ≥ 3, |B_W| ≥ 6, |B| ≥ 9;
(e) every x ∈ T_U has deg_T(x) ≥ 3, every w ∈ B_W has e(w, T) ≤ 3, and every u ∈ Z_U has
    deg_T(u) ≥ 3.

*Proof.* (a) h(T) = 0 (Identity 1.1). (b) T_W sends no edge out. The deficiency of T_U inside T is
h(T) + 6κ(T) = 12 = D(T_U) + e(T_U, V − T), and D(T_U) = D(U) = 2 because Z_U ⊆ T. (c) Identity 1.2:
g(V) = g(T) + g(B) − 2·10, so g(B) = 18; κ(B) = κ(V) − κ(T) = −1 − 2 = −3; the deficiency of B_U
inside B is (g(B) + 6κ(B))/2 = 0. (e) g(T − x) = 6 + 2deg_T(x) ≥ 12, and g(T + w) = 18 − 2e(w, T) ≥ 12
(T + w ≠ V because |B| = 2|B_U| + 3 ≥ 3). (d) T_W = ∅ would make |T| = |T_U| = 2; a vertex of T_W
has 6 neighbors in T_U, so |T_U| ≥ 6 and |T| = 2|T_U| − 2 ≥ 10. If B_U = ∅, the three vertices of B_W
have all their edges into T, at most 3 each by (e), against δ ≥ 4; so a vertex of B_U exists, it has 6
neighbors in B_W, and |B_U| = |B_W| − 3 ≥ 3. ∎

## 5. The core lemma for C2

Throughout this section G is a sparse C2 instance and

    𝒜 = {R : 4 ≤ |R| ≤ n − 1, g(R) = 12, κ(R) = 1, Z_U ⊆ R}.

An α-petal lies in 𝒜 (κ = 1 makes |Q| odd, and |Q| = 3 would be one W-vertex and two U-vertices with
g ≥ 18 − 4). A β1a-petal has |Q| ≥ 4 (κ = 2 and Q_W ∋ w).
**Fact F.** If |R| ≥ 4, R ≠ V, g(R) = 14, κ(R) = 2 and u ∈ Z_U ∩ R, then deg_R(u) ≥ 2, since
12 ≤ g(R − u) = 8 + 2deg_R(u).

**Theorem 5.1 (core lemma).** Every sparse C2 instance has a good W-vertex. More precisely:
(i) if Z_U = {u1, u2} and no W-small 2-block contains Z_U, the bad ports carry deficiency ≤ 5;
(ii) if Z_U = {u1, u2} and a W-small 2-block contains Z_U, the bad ports carry deficiency ≤ 6;
(iii) if Z_U = {u0} and no W-small 2-block contains u0, some W-vertex not adjacent to u0 is good;
(iv) if Z_U = {u0} and a W-small 2-block contains u0, some W-vertex not adjacent to u0 is good.
The ports carry deficiency D(W) = 8, so (i) and (ii) give a good port.

The proof uses only sparsity and Lemma 1.5, like C1-PAPER Lemma 4.4; minimality enters later
(Theorem 7.1) only through "every W-vertex is bad".

*Proof of (i).* By Lemma 4.1 and the hypothesis, 𝒜 is closed under union. Let P_α be the bad ports
that have an α-petal. If P_α ≠ ∅, the union R_α of one α-petal for each of them lies in 𝒜, so by
Identity 1.4 D(P_α) ≤ D((R_α)_W) ≤ h(R_α) = 3. By Lemma 3.2 every other bad port y has a β1a-petal Q_y,
def(y) = 1, and y is the only port in Q_y.
For two such ports y ≠ y', Q_y ∩ Q_y' = Z_U. Write R = Q_y, R' = Q_y'; then y ∉ R' and y' ∉ R. If
R ∪ R' = V then κ(R ∩ R') = 2 + 2 + 1 = 5 and g(R ∩ R') ≥ 30 > 28 − g(V). So g(R ∪ R') ≥ 12. If
|R ∩ R'| ≥ 3 then g(R ∩ R') ≥ 12 as well, both values are at most 16, both κ are at most 2 and sum to
4, so both are 2; a tight set with κ = 2 containing Z_U is excluded, so both have g = 14, and
h(R ∪ R') = 1 < 2 ≤ D((R ∪ R')_W) because y, y' are deficient. So |R ∩ R'| ≤ 2 and R ∩ R' = Z_U.
By Fact F, u1 has at least two neighbors in each Q_y, and these sets are disjoint because the petals
share no W-vertex. As deg u1 = 5, at most two bad ports lie outside P_α. Total: at most 3 + 2 = 5. ∎

*Proof of (ii).* Let T be a maximal W-small 2-block containing Z_U and B = V − T (Lemma 4.2). Every
port lies in B_W.
(1) *If Q is an α-petal of a bad port y, then T ∪ Q ∈ 𝒜.* u1 has at least 3 neighbors in T (Lemma
4.2(e)) and in Q, so |T ∩ Q| ≥ 3. T ∪ Q = V would give κ(T ∩ Q) = 4 and g(T ∩ Q) ≥ 24 > 24 − 10. So
both sets are tight and κ(T ∩ Q) + κ(T ∪ Q) = 3 with both at most 2. If κ(T ∪ Q) = 2, T ∪ Q is a W-small
2-block containing Z_U that strictly contains T (y ∉ T), against maximality. So κ(T ∪ Q) = 1.
(2) *Let ℳ be the maximal members of {R ∈ 𝒜 : T ⊆ R}. Distinct R, R' ∈ ℳ meet exactly in T.*
|R ∩ R'| ≥ 10; R ∪ R' = V gives κ(R ∩ R') = 3, g ≥ 18 > 14. Both sets are tight with κ summing to 2.
(1, 1) makes R ∪ R' a larger member; (0, 2) makes R ∪ R' a W-small 2-block containing Z_U and strictly
containing T (κ(R) = 1 ≠ 2, so R ≠ T); so the split is (2, 0), and R ∩ R' ⊇ T is a W-small 2-block
containing Z_U, equal to T by maximality.
(3) *For R ∈ ℳ put c(R) = e(T, R − T), the number of boundary edges of T ending in R − T. Then
R − T = {y} with c(R) = 3, or c(R) ≥ 6; D(R_W) ≤ 3, and D(R_W) ≤ 2 when c(R) = 3.* κ(R − T) = −1,
so |R − T| is odd. Identity 1.2 for the disjoint sets T and R − T gives g(R − T) = 2c(R). If
|R − T| = 1, it is a W-vertex y with c(R) = 3; otherwise |R − T| ≥ 3 and 2c(R) ≥ 12. D(R_W) ≤ h(R) = 3,
and for R = T + y, D(R_W) = def(y) ≤ 2 because deg y = 3 + e(y, B) ≥ 4.
(4) *If a bad port y has no α-petal, it has a β1a-petal Q, def(y) = 1, and R'_y := T ∪ Q has g = 14,
κ = 2, contains no other port, and c'(y) := e(T, R'_y − T) ≥ 5.* T ∪ Q = V gives κ(T ∩ Q) = 5,
g ≥ 30 > 16; so g(T ∪ Q) ≥ 12. If |T ∩ Q| ≥ 3, both values lie in [12, 14], both κ are at most 2 and sum
to 4, so both are 2, and g(T ∪ Q) = 12 would give a W-small 2-block strictly containing T: g(T ∪ Q) = 14.
If |T ∩ Q| ≤ 2 then T ∩ Q = Z_U (g = 12, κ = 2), so g(T ∪ Q) ≤ 14 with κ = 2, and again g(T ∪ Q) = 14.
h(R'_y) = 1 ≥ D((R'_y)_W) ≥ def(y) = 1. Finally κ(R'_y − T) = 0 and g(R'_y − T) = 2 + 2c'(y). If
|R'_y − T| = 2, it is {y, x} with x ∈ B_U, which has no neighbor in T_U, so c'(y) = e(y, T) ≤ 3 while
g({y, x}) ≥ 10 gives c'(y) ≥ 4. So |R'_y − T| ≥ 4 (it is even), g(R'_y − T) ≥ 12 and c'(y) ≥ 5.
(5) *Let P1 be the bad ports lying in a member of ℳ (by (1) this includes every bad port with an
α-petal), ℳ1 the members of ℳ containing a port of P1, and P2 the other bad ports. The sets R − T
(R ∈ ℳ1) and R'_y − T (y ∈ P2) are pairwise disjoint.* Two members of ℳ1: (2). Two ports y ≠ y' in
P2: the intersection contains T, the union is not V (κ(∩) = 5 > 18/6), both values are at least 12 and
at most 16, both κ = 2; g(∪) = 12 is a W-small 2-block strictly containing T, g(∪) = 14 means h(∪) = 1
with y and y' deficient; so g(∪) = 16, g(∩) = 12, and the intersection is a W-small 2-block containing
T, equal to T. A member R ∈ ℳ1 and y ∈ P2: the union is not V (κ(∩) = 4 > 16/6); κ sum 3, both
values in [12, 14]; (2, 1) with g(∩) = 12 gives ∩ = T; (2, 1) with g(∩) = 14 gives g(∪) = 12, so
∪ ∈ 𝒜 contains R and equals R by maximality, putting y in P1; (1, 2) with g(∪) = 12 is a W-small
2-block strictly containing T; (1, 2) with g(∪) = 14 means h(∪) = 1 while ∪ contains y and a port of
R ∩ P1.
(6) *Budget.* The sets of (5) use disjoint sets of the 10 boundary edges of T, and each port of P1
lies in exactly one member of ℳ1 (ports lie outside T). With a members of ℳ1 having c = 3, b having
c ≥ 6, and d = |P2|: 3a + 6b + 5d ≤ 10, and the bad ports carry at most 2a + 3b + d ≤ 6. ∎

*Proof of (iii).* Suppose every W-vertex of W' = W − N(u0) is bad; |W| ≥ 6 (a vertex of U − u0 has six
neighbors), so W' ≠ ∅. By Lemma 3.2 each w ∈ W' has an α- or β1a-petal: γ needs w ~ u0, β1b needs a
U-vertex of deficiency 1, and a β2-petal is a W-small 2-block containing u0. By Lemma 4.1 and the
hypothesis, 𝒜 is closed under union.
(iii-a) *Some w ∈ W' has an α-petal.* Let R* be the union of all members of 𝒜, so R* ∈ 𝒜. u0 has at
least 3 neighbors in R*, so at most one vertex of N(u0) lies outside R*; |R*_W| = |R*_U| − 1 ≤ s − 1,
so at least two W-vertices lie outside R*, and one of them, w, is in W'. It has no α-petal (that would
lie in R*), so it has a β1a-petal Q_w ∋ u0.
*Claim A: R* ∪ Q_w has g = 14 and κ = 2.* u0 has at least 3 neighbors in R* and 2 in Q_w (Fact F), so
a common neighbor x. If R* ∩ Q_w = {u0, x}, then κ(R* ∩ Q_w) = 0, κ(R* ∪ Q_w) = 3 and
g(R* ∪ Q_w) ≥ 18 > 26 − 10. So |R* ∩ Q_w| ≥ 3, and R* ∪ Q_w = V would give κ(∩) = 4, g ≥ 24 > 16. Both
values lie in [12, 14] with κ summing to 3: in case (2, 1), g(∩) = 12 is a W-small 2-block containing u0,
and g(∩) = 14 gives g(∪) = 12, ∪ ∈ 𝒜, ∪ ⊆ R*, w ∈ R*; in case (1, 2), g(∪) = 12 is excluded. So
g(R* ∪ Q_w) = 14, κ = 2.
*Claim B: if R1, R2 ≠ V contain R* and have g = 14, κ = 2, so does R1 ∪ R2.* |R1 ∩ R2| ≥ 5, so
g(R1 ∩ R2) ≥ 12; R1 ∪ R2 = V gives κ(∩) = 5 > 18/6; both values at most 16, κ sum 4, both κ = 2, and
g = 12 is excluded, so both are 14.
Let R** be the union of R* ∪ Q_w over all w ∈ W' − R*. By Claim B, κ(R**) = 2 (and R** ≠ V). R**
contains W' and the at least three neighbors of u0 in R*, so |R**_W| ≥ s and |R**_U| ≥ s + 2 > |U|. ✗
(iii-b) *No w ∈ W' has an α-petal.* Let ℬ = {R : 4 ≤ |R| ≤ n − 1, g(R) = 14, κ(R) = 2, u0 ∈ R}. As in
Claim B, R, R' ∈ ℬ with |R ∩ R'| ≥ 3 have R ∪ R' ∈ ℬ. Let M_1, ..., M_r be the maximal members of ℬ
that contain a β1a-petal of a vertex of W'. For i ≠ j, |M_i ∩ M_j| ≤ 2 by maximality and u0 ∈ M_i ∩ M_j;
if M_i ∩ M_j = {u0, x} with x ∈ W then κ(M_i ∪ M_j) = 4 and g(M_i ∪ M_j) ≥ 24 > 28 − 10. So distinct
M_i share no W-vertex. By Fact F each M_i contains two neighbors of u0, so r ≤ 2. If r = 1, M_1 contains
W' and two vertices of N(u0): |M_1 ∩ W| ≥ s − 1 and |M_1 ∩ U| ≥ s + 1 ✗. If r = 2, M_1 ∪ M_2 ⊇ W and
κ(M_1 ∪ M_2) = 4 − κ(M_1 ∩ M_2) ≥ 2, since M_1 ∩ M_2 is {u0} or {u0, x} with x ∈ U; so
|(M_1 ∪ M_2) ∩ U| ≥ s + 3 ✗. ∎

*Proof of (iv).* Let T be a maximal W-small 2-block containing u0, B = V − T, W' = W − N(u0), and
suppose every vertex of W' is bad. u0 has at least 3 neighbors in T (Lemma 4.2(e)), so
|N(u0) ∩ B_W| ≤ 1. Put 𝒜_T = {R ∈ 𝒜 : T ⊆ R} and ℬ_T = {R : T ⊆ R ≠ V, g(R) = 14, κ(R) = 2}.
(1) *A vertex w ∈ B_W ∩ W' has no β2-petal; an α-petal Q of w gives T ∪ Q ∈ 𝒜_T; a β1a-petal Q of w
gives T ∪ Q ∈ ℬ_T.* β2: Q is a W-small 2-block containing u0 with |Q| ≥ 4; u0 has 3 neighbors in T and
in Q, so |T ∩ Q| ≥ 3; T ∪ Q = V gives κ(∩) = 5 > 14/6; both sets are tight, κ sums to 4, so both have
κ = 2, and T ∪ Q is a W-small 2-block containing u0 and w ∉ T ✗. α: as (ii)(1), with u0 (degree 4, at
least 3 neighbors in each set, so 2 in common) in place of u1. β1a: u0 has a common neighbor x in T and
Q; T ∩ Q = {u0, x} would give κ(T ∪ Q) = 4 and g ≥ 24 > 16; so |T ∩ Q| ≥ 3 and (ii)(4) applies verbatim.
(2) *Let ℳ and ℳ' be the maximal members of 𝒜_T and of ℬ_T. Two members of ℳ meet exactly in
T; two members of ℳ' meet exactly in T; a member of ℳ and a member of ℳ' are nested or meet exactly
in T.* The first is (ii)(2). For R', R'' ∈ ℳ': the union is not V, κ sum 4, both κ = 2; g(∪) = 12 is a
W-small 2-block strictly containing T, g(∪) = 14 puts the union in ℬ_T against maximality, so
g(∪) = 16 and g(∩) = 12, ∩ = T. For R ∈ ℳ, R' ∈ ℳ': the union is not V (κ(∩) would be 4 > 16/6),
κ sum 3, values in [12, 14]; (2, 1) with
g(∩) = 12 gives ∩ = T, with g(∩) = 14 gives ∪ ∈ 𝒜_T, so ∪ = R and R' ⊆ R; (1, 2) with g(∪) = 12 is
excluded, with g(∪) = 14 gives ∪ ∈ ℬ_T, so ∪ = R' and R ⊆ R'.
Let 𝒞 be the inclusion-maximal sets of ℳ ∪ ℳ'. They meet pairwise exactly in T, and by (1) every
vertex of B_W ∩ W' lies in one of them.
(3) *Counting.* Let 𝒞 have p members from ℳ and q from ℳ'. For the first kind |(R − T)_W| =
|(R − T)_U| + 1, for the second |(R − T)_W| = |(R − T)_U|, and the parts R − T are disjoint subsets of
B. So |B_W| − |N(u0) ∩ B_W| ≤ |B_U| + p = |B_W| − 3 + p, that is p ≥ 3 − |N(u0) ∩ B_W| ≥ 2. The counts
c(R) = e(T, R − T) satisfy (ii)(3) on ℳ and c ≥ 5 on ℳ' (the proof in (ii)(4) uses only g, κ and Lemma
4.2(e)), and they sum to at most 10.
If p ≥ 3: then p = 3, q = 0 and all three have c = 3 (3 + 3 + 6 and 3 + 3 + 3 + 5 exceed 10), so
B_W ∩ W' has at most three vertices and |B_W| ≤ 4 < 6 ✗ (Lemma 4.2(d)).
If p = 2: then N(u0) ∩ B_W = {x0} and equality holds above: the members cover exactly B_W − x0, and their
U-parts cover B_U. The boundary edge u0x0 lies in no member, so the counts sum to at most 9. Two
members with c = 3 have empty U-parts, so B_U ≠ ∅ needs q ≥ 1 and a sum ≥ 11 ✗. One with c = 3
(R_1 = T + y) and one with c ≥ 6 force q = 0 and c(R_2) = 6; then R_2 − T = B − x0 − y, so
R_2 = V − x0 − y, and Identity 1.3 gives 12 = g(R_2) = 2(deg x0 + deg y) − 2, so deg x0 + deg y = 7,
against δ ≥ 4 ✗. Two with c ≥ 6 exceed 9 ✗. ∎

## 6. E5: two 2-blocks and a 7-edge cut

**Theorem 6.1 (structure).** Let G be a sparse E5 instance with sides P, Q and no 4-factor. Then
V = X ⊔ Y with X = A ∪ C and Y = B ∪ D (A, B ⊆ P; C, D ⊆ Q), where |A| = |C| + 2 and |D| = |B| + 2;
every vertex of C has degree 6 and N(C) ⊆ A; every vertex of B has degree 6 and N(B) ⊆ D;
D(A) = D(D) = 5; every edge between X and Y joins A and D, and there are exactly 7 of them;
g(X) = g(Y) = 12, so X and Y are 2-blocks; and |C|, |B| ≥ 4, so |X|, |Y| ≥ 10 and n ≥ 20.

*Proof.* Lemma 1.5 gives A ⊆ P, C ⊆ Q with k = |A| − |C| ≥ 1 and σ = 2k − D_A + ε < 0,
ε = D_C + e(P − A, C). Put X = A ∪ C. Then e(X) = 6|C| − ε, so g(X) = 6k + 2ε, and X ≠ V. The
violation gives D_A ≥ 2k + 1 + ε, and D_A ≤ D(P) = 5, so 2k + ε ≤ 4. If |X| ≥ 3, sparsity gives
3k + ε ≥ 6; with 2k + ε ≤ 4 this forces k = 2, ε = 0, D_A = 5, σ = −1. If |X| ≤ 2, then C = ∅ and X is
one vertex of degree ≤ 3 (k = 1, D_A ≥ 3) or two vertices of degree sum ≤ 7 (k = 2, D_A ≥ 5), against
δ ≥ 4. So e(A, Q − C) = 4k + σ = 7, ε = 0 makes C saturated with N(C) ⊆ A, and with B = P − A,
D = Q − C: D(B) = D(P) − D_A = 0 and e(B, C) = 0, so B is saturated with N(B) ⊆ D; D(D) = 5 − D_C = 5;
the edges between X and Y are the 7 edges of E(A, D); g(Y) = g(V) + 14 − g(X) = 12. A vertex of C has six
neighbors in A, so |A| ≥ 6 and |C| ≥ 4 (C = ∅ was excluded); B = ∅ would make D two vertices of
degree sum 7. So |B| ≥ 4 as well. ∎

Every 4-regular subgraph H of such a G uses exactly 0 or 4 edges of the cut: summing H-degrees over
A and over C gives e_H(A, D) = 4(|V(H) ∩ A| − |V(H) ∩ C|) ≤ 7.

**Lemma 6.2 (gluing).** In a minimal counterexample G of E5 type (Theorem 6.1), the 7 cut edges
contain no matching of size 4.

*Proof.* Let a_i d_i (i ≤ 4) be a matching in the cut, a_i ∈ A. X + z, with z a new vertex on the Q
side adjacent to a_1, ..., a_4, is bipartite with Δ ≤ 6 (each a_i has a cut edge, so deg_X(a_i) ≤ 5),
has |X| + 1 ≤ n − 1 vertices and e(X) + 4 = 3(|X| + 1) − 5 edges. By minimality it has a 4-regular
subgraph, which must contain z with its four edges (otherwise it lies in G). Removing z leaves
H_X ⊆ G[X] with degree 3 at the a_i and 4 elsewhere. The same for Y gives H_Y with degree 3 at the d_i.
H_X ∪ H_Y ∪ {a_i d_i} is a 4-regular subgraph of G. ∎

**Lemma 6.3 (shift).** Let G be a minimal counterexample of E5 type and v ∈ A a vertex with 3 cut
edges. Then deg_X(v) = 3, deg v = 6, X − v and Y + v are tight, and for every cut edge ad with a ≠ v and
d ∉ N(v), the vertex a is adjacent to all three vertices of N_X(v) ⊆ C. The same holds with X and Y
exchanged.

*Proof.* deg_X(v) ≤ 6 − 3, and g(X − v) = 6 + 2deg_X(v) ≥ 12, so deg_X(v) = 3, deg v = 6,
g(X − v) = 12 and g(Y + v) = 12 + 6 − 2·3 = 12. Suppose ad is a cut edge with a ≠ v, d ∉ N(v), and
c ∈ N_X(v) is not adjacent to a. X' = X − v plus the edge ca is bipartite (c ∈ Q, a ∈ P), has Δ ≤ 6
(c has degree 5 in X − v, a has degree ≤ 5 in X because of the edge ad), |X − v| ≤ n − 1 vertices and
3|X − v| − 5 edges; by minimality it has a 4-regular subgraph H1, which uses ca. Y' = Y + v plus the edge
vd is bipartite, has Δ ≤ 6 (v has degree 3 in Y + v; d has degree ≤ 5 in Y + v because of ad and
d ∉ N(v)) and 3|Y + v| − 5 edges; it has a 4-regular subgraph H2 using vd. Then
(H1 − ca) ∪ (H2 − vd) ∪ {vc, ad} is a 4-regular subgraph of G. ∎

**Lemma 6.4 (sizes).** In a minimal counterexample of E5 type, |X|, |Y| ≥ 14, so n ≥ 28. If QB(6)
holds for graphs with at most 18 vertices (it does by the census: F1 for n ≤ 18, see below), then
|X|, |Y| ≥ 20 and n ≥ 40.

*Proof.* X is 4-regular-free. A 2-block on 10 vertices is K_{4,6}. On 12 vertices each of the five
C-vertices misses exactly one of the seven A-vertices: if two miss the same vertex, those two and any
two more C-vertices have at least 4 common neighbors (K_{4,4}); otherwise the five missed vertices and C
span K_{5,5} minus a perfect matching, which is 4-regular. G[X] has 3|X| − 6 edges, so QB(6) on at most
18 vertices gives a 4-regular subgraph; 2-blocks have even size. For the census: a minimal counterexample
to QB(6) has e = 3n − 6 and δ ≥ 4 (as in Lemma 2.1; QB(6) is vacuous for 3 ≤ n ≤ 9), and F1(n)
(bipartite, δ ≥ 4, Δ ≤ 6, e ≥ 3n − 6 implies a 4-regular subgraph) holds for n ≤ 18
(`reports/585-next/census/CENSUS.md` lines 34-37, 123-136; n = 17, 18 by one method). ∎

## 7. The main theorem

**Theorem 7.1.** A minimal counterexample to QB(5) (Lemma 2.1) is an E5 instance with the structure
of Theorem 6.1, in which the 7 cut edges have matching number at most 3 (Lemma 6.2), Lemma 6.3 holds,
and n is even with n ≥ 28 (n ≥ 40 with the census).

*Proof.* By Lemma 2.1, G is sparse and E5 or C2. If G is C2, every W-vertex is bad (Lemma 2.1(d)),
contradicting Theorem 5.1. So G is E5 without a 4-factor; apply Theorem 6.1 and Lemmas 6.2-6.4. ∎

**Corollary 7.2.**
(a) QB(5) holds if and only if every sparse E5 instance has a 4-regular subgraph; equivalently, iff no
graph as in Theorem 7.1 exists. If QB(5) fails, its smallest counterexamples have an even number of
vertices.
(b) If every 2-block graph (bipartite, sides t and t + 2, Δ ≤ 6, every vertex of the smaller side of
degree 6) has a 4-regular subgraph, then QB(5) holds. This hypothesis is the j = 2, d = 0 part of QB(6)
(C1-PAPER Identity 1.1 at g = 12).
(c) Every sparse C2 instance has a W-vertex w with a 4-factor in G − w (Theorem 5.1). With E5 settled,
this would be the C1-PAPER Lemma 4.4 analog that finishes QB(5).

*Proof.* (a) A minimal counterexample is a sparse E5 instance with no 4-regular subgraph; the
converse is trivial. (b) X in Theorem 7.1 would be a 4-regular-free 2-block graph. ∎

## 8. Where the C1 argument fails, and the smallest instances

The C1 proof (C1-PAPER Theorem 4.3) has three steps: every port has a petal of one type (Lemma 3.2),
the petals form a lattice (Lemma 4.2), and the union of all petals contradicts the deficiency count.
Each step fails for QB(5), at a size that can be pinned down.

**8.1 Petals at ports only (P4, n = 15).** P4 PAPER Theorem 3.1(c): three sparse C2 instances at
n = 15 in which every port is bad, all through type γ (four ports of degree 4, all adjacent to u0). Our
analysis replaces ports by all W-vertices off N(u0) (Theorem 5.1(iii)-(iv)); in those three graphs the
degree-6 W-vertices are good. In the whole sparse class at n = 11, 13, 15 (2, 29, 2,895 graphs) every
bad W-vertex is of type γ: no α or β petal occurs at n ≤ 15 (C2 instances have odd n; Appendix A.1).

**8.2 The petal lattice (n = 19, smallest possible).** Lemma 4.1 allows a (2, 0) or (0, 2) split, and
then Q ∩ Q' or Q ∪ Q' is a W-small 2-block containing Z_U, so Lemma 4.2(d) gives n ≥ 10 + 9 = 19. This
is attained: in the family T = K_{4,6} (T_W of size 4 saturated into T_U), B = K_{3,6} (B_U saturated into
B_W), plus 10 edges between T_U and B_W (64 graphs, all sparse C2 instances, n = 19), 12 graphs have two
α-petals Q, Q' whose intersection is a W-small 2-block (κ = 2) and whose union has κ = 0
(`code/data/tb19_split.g6`; 3 with u0, 9 with u1, u2). Example: `R??F~z{~??????_Bg@s?[OB_wM@o[?` (first line of that file): u0 = 5, T = {0, ..., 9},
Q = T + 18, Q' = T + 17. So "the union of two petals is a petal" is false for QB(5), and Theorem 5.1
replaces it by a maximal 2-block T and a budget of its 10 boundary edges.

**8.3 E5 gluing (n = 22, smallest possible).** Lemma 6.2 closes E5 when the cut has a 4-matching. A
sparse E5 instance without a 4-factor whose cut has matching number at most 3 needs n ≥ 22: by König
the 7 cut edges have a vertex cover of size at most 3, so some vertex carries 3 cut edges and has degree
3 inside its block (Lemma 6.3's first step uses only sparsity), while every vertex of the big side of a
10-vertex 2-block (K_{4,6}) has in-block degree 4; 2-blocks have even size, so one block has at least 12
vertices. This is attained: 60 instances at n = 22 (X with sides 5 and 7, Y = K_{4,6}) and 40 at n = 24
(both blocks with sides 5 and 7), all sparse, without a 4-factor, with matching number 3
(`code/data/e5_n22.g6`, `e5_n24.g6`). They contain K_{4,4}, so they are not counterexamples; they show
that sparsity, "no 4-factor" and 4-matching gluing cannot finish E5.

**8.4 What the instances suggest.** In every instance of 8.3, G − p − q has a 4-factor for 35 to 47 of
the pairs p ∈ P, q ∈ Q (mostly p ∈ A, q ∈ D). In a minimal counterexample every such pair is bad, so the
statement "every sparse E5 instance without a 4-factor has p ∈ P, q ∈ Q with a 4-factor in G − p − q"
would prove QB(5). Its violations are richer than in Lemma 3.2: with σ' = f(S) − e(S_P, q) the
complement R of a violation S of G − p − q has g(R) = 10 + 2k + 2f − 2D(C') and κ(R) = k, and k ranges
over 1 to 5 (P4's adjacency term e(S, Y) of its Lemma 2.2 reappears as e(S_P, q)).

## 9. Exact residual

QB(5) is equivalent to the nonexistence of the following object (Theorem 7.1): a bipartite graph G with
Δ ≤ 6 and no 4-regular subgraph, V = X ⊔ Y, where
- X has sides C (degree 6, all neighbors in A) and A with |A| = |C| + 2; Y has sides B (degree 6, all
  neighbors in D) and D with |D| = |B| + 2; D(A) = D(D) = 5;
- exactly 7 edges join A and D, and they contain no matching of size 4;
- G is sparse (every S with 3 ≤ |S| ≤ n − 1 spans at most 3|S| − 6 edges);
- X and Y each realize every set of four distinct big-side vertices of in-block degree at most 5
  (proof of Lemma 6.2), and Lemma 6.3 holds;
- |X|, |Y| ≥ 14 (≥ 20 with the census), n ≥ 28 (≥ 40).
The step that fails is the gluing of two 2-blocks across the 7-edge cut when the four cut edges any
4-regular subgraph must use share endpoints: that needs a block to realize a degree pattern with a
vertex of degree 2 or 1, which the minimality calls of Lemmas 6.2 and 6.3 do not give.

Next steps, in order of expected value:
1. Prove the E5 pair statement of 8.4 by a petal analysis of G − p − q with p ∈ A, q ∈ D (the natural
   choice: the X-violation is fixed when c_p + c_q − [p ~ q] ≤ 3, where c_v counts cut edges at v).
2. Multi-trace realization in 2-blocks: show a tight 2-block X realizes deficit patterns (2, 1, 1),
   (2, 2), (3, 1) on its big side under the hypotheses of §9; with Lemma 6.2 this closes E5.
3. C0^(2) (Corollary 7.2(b)) as a QB(6) sub-case: a joint induction "QB(5) and C0^(2)" makes proper
   2-blocks 4-regular-containing; its own core lemma (deleting two big-side vertices) has gap 0 between
   g(V) = 12 and the sparsity bound, so it needs a different idea.

## Appendix A. Computations

All code is in `reports/585-next/wave4/qb5/code/`, data in `code/data/`; `code/run_all.sh` rebuilds the
C tools (`/usr/bin/clang -O3`), regenerates every built family from its seed, compares it with
`code/data/`, and reruns every check below (log: `code/data/run_all.log`). Interpreter
`/private/tmp/erdos585-research-venv/bin/python` (networkx 3.6.1). Generator for the cut graphs: plain
nauty genbg 2.9.3 (`~/.cache/erdos585/nauty2_9_3/genbg`). The exhaustive sparse classes are P4's
(`reports/585-next/wave3/P4/checks/data/qb5_n*.g6`, genbg 2.9.3 with the PRUNE1 hook `bsp_prune.c`,
degrees 4 to 6, e = 3n − 5, every proper set of size ≥ 3 spanning ≤ 3|S| − 6 edges). Total compute: a
few core-minutes. These checks cover identities, the minimality-free Theorems 5.1 and 6.1 and the
certificates; the minimality steps (Lemmas 2.1(b), 6.2, 6.3, 6.4, Theorem 7.1) cannot be run, since no
counterexample is known.

Tools. `petal.c`: for every vertex set S of a C2 instance it computes f(S) = e(S_W, U − S_U) − 4(|S_W| −
|S_U|), the slack of (S_W, S_U) in G − w for every w ∈ W − S (Lemma 1.5), so w is bad iff some S avoiding w
has f(S) < 0; each violation is typed by Lemma 3.2 (any other combination is reported as "other");
it lists tight sets by κ, the (2, 0)/(0, 2) splits of α-petal pairs, and the core checks of Theorem 5.1
(u1u2: some port good; u0: some W-vertex off N(u0) good). For E5 it decides the 4-factor by the same
enumeration. `clcheck.c`: the chain of Theorem 5.1(i)-(ii) on ports: (A) port petals are α, β1a or γ;
(B) the union of the α-petals of ports has g = 12, κ = 1 when no W-small 2-block contains Z_U; (D) two
β1a-only ports have petals meeting in Z_U; (CL) bad ports carry ≤ 5, (CL') ≤ 6. `verify_certs.py`
shares no code with these: 4-factors by networkx maximum flow, sparsity by a subset DP, the E5 violation
from a minimum cut, matching number by networkx.

| Check | Input | Result |
|---|---|---|
| A.1 `petal` | P4 classes n = 11 (5+6), 13 (6+7), 15 (7+8): 2, 29, 2,895 C2 graphs; n = 12, 14 (6+6, 7+7): 13, 818 E5 graphs | all sparse; every bad W-vertex is γ (4, 36, 2,640 of them); no α or β petal; core check holds in all (u0: 1, 9, 660 graphs; u1u2: 1, 20, 2,235); all E5 graphs have a 4-factor (n = 16: P4's `deep`, 229,728 of 229,728) |
| A.2 `petal` | tb19: `genbg -q -d0:1 -D2:3 6 6 10:10` (64 cut graphs) + `assemble_tb.py 6 4 3 6` (T = K_{4,6}, B = K_{3,6}) | 64 sparse C2 (u0 14, u1u2 50); bad W-vertices at most 6 of 10, types α, β2, γ; 12 graphs with a (2, 0) split of an α-petal pair (`tb19_split.g6`) |
| A.3 `clcheck` | `gen_template.py alpha|beta|alpha1 300 7` (planted α, β1a, α with ε = 1; n = 19 to 21) | 293, 290, 287 sparse; (A), (B), (D), (CL) hold; bad-port deficiency exactly 3, 1, 2 |
| A.4 `clcheck`, `petal` | `gen_j3.py u1u2 1500 11` (T = K_{4,6} with Z_U = {u1, u2}, random 3-block B with b = 3, 4) and `gen_j3.py u0 1500 12` | all 3,000 sparse; u1u2: (CL') holds, bad-port deficiency ≤ 2 (bound 6); u0: a good W-vertex off N(u0) in all 1,500 |
| A.5 `verify_certs.py c2core` | A.1 C2 classes, tb19, j3, j1 (5,990 graphs) | 0 failures |
| A.5 `verify_certs.py e5`, `sparse` | first 10 of `e5_n22.g6`, first 4 of `e5_n24.g6`; first 3 of `tb19_split.g6` | E5: sparse, no 4-factor, min-cut violation with k = 2, g(X) = g(Y) = 12, 7 cut edges, matching number ≤ 3: 0 failures; split certificates sparse |
| A.6 `petal`, `pairs_e5.py` | `gen_e5.py 60 5` (n = 22) and `gen_e5.py 40 9 big` (n = 24) | 100 sparse E5 graphs without a 4-factor, cut matching number 3 (checked in the generator by brute force); good pairs (p, q): 35 to 40 (n = 22), 40 to 47 (n = 24) of 121 and 144 |

Script hashes (SHA-256, first and last 8 hex digits) at freezing: listed in `FROZEN.sha256` together with
this file.

## Appendix B. Sources (paths relative to the repository root)

- `reports/585-next/G110/C1-PAPER.md` (SHA-256 3c67d183...): classes and Identity 1.1 (lines 66-84),
  Identities 1.2, 1.3 (86-89), Lemma 1.4 flow criterion (91-95), Lemma 3.1 cut identity (137-155),
  Lemma 3.2 (157-170), Lemma 4.2 lattice (194-204), Theorem 4.3 (206-211), Lemma 4.4 core lemma
  (213-221), Corollary 5.3 QB(4) (234-240); accepted by two referees (`C1-REVIEW.md`,
  `C1-CORRECTIONS.md`).
- `reports/585-next/wave3/P4/PAPER.md` (SHA-256 825189da...): Theorem 3.1(c) and the remark on its
  graphs (161-163, 173-175), Corollary 5.4 (280-299), §7 step 1 (347-351), A.7 (374).
  `reports/585-next/wave3/P4/FLAW.md` (SHA-256 50486165...) line 32. The sparse classes
  `reports/585-next/wave3/P4/checks/data/qb5_n*.g6` and `qb5_deep_n15.txt`, `qb5_deep_n16.txt`.
- `reports/585-next/census/CENSUS.md` (SHA-256 c2018a72...): F1 for n ≤ 16 by two methods and n = 17, 18
  by one (lines 34-37, 123-136); `reports/585-next/STATE.md` line 31 (F1(18) complete).
