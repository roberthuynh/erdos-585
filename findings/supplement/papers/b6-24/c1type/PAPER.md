# The C1 type at a port: no smallest W1b counterexample on 19, 21 or 23 vertices

wave4/c1type (Pass 3 wave 4), October 5, 2026. Written proofs plus SAT cross-checks. Not reviewed.
No Lean, no `check.sh`. Rungs as in STATE.md: Theorem C and Corollary C are (a), resting on the
censuses listed in §8; the checks of §7 are (b).

Sources. "THEORY" is `wave4/theory/PAPER.md` (frozen, SHA-256 521a1139…), "ADD-B" is
`wave4/theory/ADDENDUM-B.md` (frozen, 555b8ef3…), "PAIRS" is `wave3/pairs/PAPER.md` (frozen 6fad9b43…,
refereed ACCEPT WITH FIXES; Prop 5 is used with the referee's fix |S| ≥ 3), "C1P" is
`G110/C1-PAPER.md` (Lemma 4.4 refereed ACCEPT twice), "SCOUT" is `wave3/pairs/SCOUT.md` (censuses H22
and L5). Paths are relative to `reports/585-next/`.

## 0. Results

A *pair* is two edge-disjoint cycles with the same vertex set. W1b: every bipartite graph with Δ ≤ 6,
n ≥ 2 and e ≥ 3n − 4 has a pair.

**Theorem C.** There is no smallest W1b counterexample of C1 type with n ∈ {19, 21, 23}.

**Corollary C.** W1b holds for every bipartite graph on at most 23 vertices. Hence every simple
bipartite 6-regular graph on at most 24 vertices has a pair (B6 for N ≤ 24; the direct census gives
N ≤ 20). The part n ≤ 22, N ≤ 22 uses neither census L5 nor H22 for the C1 type.

*Proof of Corollary C from Theorem C.* If W1b fails on some graph with at most 23 vertices, take a
counterexample X with n minimal, then e minimal; n ≤ 23. By PAIRS Lemma 1 X is a sparse E4 or C1
instance, and by census F2 n ≥ 19. E4 instances have n even and C1 instances n odd. ADD-B Corollary B
excludes E4 type with n ≤ 22, and Theorem C excludes C1 type with n ∈ {19, 21, 23}. For B6: if B is
bipartite 6-regular on N ≤ 24 vertices with no pair, then for any vertex o, B − o has n = N − 1 ≤ 23,
Δ ≤ 6, e = 3N − 6 = 3n − 3 and no pair (`wave4/theory/N.md`, step 1). ∎

The method is ADD-B's (one-crossing cycles at the unique bad pair of a 4-factor, then THEORY
Proposition 6.6 and the census H_m), applied to Y = X − w at a good port w. Two facts make it work:
the bad pair of a 4-factor of Y has a side K_{4,4} − e or 5 + 5 (Lemma C1, as in THEORY Lemma 6.1), and
the U-side deficiency of Y is spread out, at most one vertex of U having deficiency 2 in Y (fact F2).
F2 stands in for the E4 bound D(Q) = 4 in ADD-B's counts, and at n = 23 it removes the need for the
mirror half (Steps 1'-3') of ADD-B §4.3.

**Where to check first.** (1) Fact F2 and the bound D_Y(S_Q) ≤ r + 1 in Lemma C3, used in every case.
(2) Lemma C1(b) and the transfer of THEORY Proposition 6.6 (Proposition C2), which need m ≤ 22.
(3) §4.2 (3)-(4): the covering count and the parallel-edge contradiction. (4) §4.1 for n = 23: the
classification of good sets and the endgame at q' (the one shape without a SAT cross-check).
(5) §4.3, Steps 2 and 5, where the C1 argument departs from ADD-B §4.3.

## 1. Setting

Let X be a smallest W1b counterexample (n minimal, then e minimal) of C1 type. By PAIRS Lemma 1,
e(X) = 3n − 4, δ(X) ≥ 4, X has no pair, and X is *sparse*: g(S) = 6|S| − 2e(S) ≥ 10 for every S with
2 ≤ |S| ≤ n − 1. The classes are U (s vertices, D(U) = 1) and W (s + 1 vertices, D(W) = 7), n = 2s + 1,
where D(Z) = Σ_{v∈Z} (6 − deg v); u1 is the vertex of U of degree 5, all others in U have degree 6.

(F1) X contains no K_{4,4} (it has a pair, PAIRS Example 4), and every 5 + 5 subgraph of X has at most
21 edges (no pair-free bipartite graph on 5 + 5 vertices has 22 or more edges: THEORY Appendix A,
`genbg` + `pairc`). Consequently X contains no bipartite subgraph with classes of sizes

- 4 and 5 with ≥ 19 edges (delete the 5-side end of the missing pair, if any);
- 4 and 6 with ≥ 22 edges (delete the 6-side ends of the at most two missing pairs, then more 6-side
  vertices until four remain);
- 5 and 6 with ≥ 27 edges (ADD-B Lemma B2: delete a 5-side vertex meeting a missing pair, then the
  6-side ends of the at most two remaining missing pairs, then more 6-side vertices).

*Ports.* A port is a vertex of W of degree 4 or 5; the ports carry all of D(W) = 7. A port w is *good*
if X − w has a 4-factor (a spanning 4-regular subgraph). By C1P Lemma 4.4 (which assumes only that a
C1 instance with D(U) = 1 is sparse), the bad ports carry total deficiency at most 2, so **a good port
w exists**. Fix one and put

    Y = X − w,   P = W − w,   Q = U,   m = |V(Y)| = n − 1 = 2s.

(F2) For q ∈ Q, the deficiency of q in Y is D_Y(q) = [q ∈ N(w)] + [q = u1]. So D_Y(v) ≤ 2 for every
v ∈ V(Y) (δ(X) ≥ 4), and **D_Y(Z) ≤ |Z| + 1 for every Z ⊆ Q** (at most one vertex of Q has D_Y = 2).
Also D_Y(Q) = 1 + deg w and D_Y(P) = D(W) − (6 − deg w) = 1 + deg w; put d := 1 + deg w ∈ {5, 6}.

For S ⊆ V(Y), g(S) = g_X(S) (the same induced graph), so g(S) ≥ 10 whenever |S| ≥ 2.

Let F be a 4-factor of Y and H = Y − F; h(v) = deg_Y(v) − 4 = 2 − D_Y(v) ∈ {0, 1, 2} is the H-degree.
D(F) is the digraph with an arc p → q for each pq ∈ F and q → p for each pq ∈ H (p ∈ P, q ∈ Q).
Reversing a directed cycle Z of D(F) gives the 4-factor F Δ E(Z). For S ⊆ V(Y) with S_P = S ∩ P,
S_Q = S ∩ Q and j(S) = |S_Q| − |S_P|, THEORY Lemma 1.1 (its proof uses only the F-degree sums, so it
holds in Y) gives that the number of arcs of D(F) leaving S is

    s(S) = g(S)/2 − j(S) − D_Y(S_Q),   independent of F.                                (1.1)

(F3) (Used only for n = 23.) By PAIRS Proposition 5 (with |S| ≥ 3) and census L5, a set S' of X with
3 ≤ |S'| ≤ min(17, n − 1) has g_X(S') ≥ 12. For S ⊆ V(Y) with 2 ≤ |S| ≤ 16, apply this to S' = S + w:
g(S + w) = g(S) + 6 − 2|N(w) ∩ S| gives g(S) ≥ 6 + 2|N(w) ∩ S|, and (1.1) with (F2) gives

    s(S) ≥ 3 − [u1 ∈ S] − j(S).                                                          (1.2)

A set T is *balanced* if |T_P| = |T_Q|; then c_F(T) := e_F(T_Q, P − T) = e_F(T_P, Q − T) and
∂_F(T) = 2c_F(T). A cut of at most 2 edges of a 4-regular bipartite graph is balanced (degree sums).
T is *bad* for F if T is balanced, 2 ≤ |T| ≤ m − 2 and c_F(T) ≤ 1.

(K) *If F has no bad set, X has a pair.* F is then connected (a component C of F is balanced with
|C| ≥ 8 and |V(Y) − C| ≥ 8, and c_F(C) = 0) and has no cut of at most 2 edges. By census H_m (SCOUT
§2.3: every connected bipartite 4-regular graph on at most 22 vertices with no 2-edge cut is
Hamilton-decomposable; two methods for m ≤ 20, one at m = 22) F is the union of two edge-disjoint
Hamilton cycles of Y, a pair in X.

## 2. Bad sets at a port

**Lemma C1.** Let m ≤ 22 and let F be a 4-factor of Y.
(a) F is connected.
(b) If T is bad for F, then c_F(T) = 1, g(T) ≤ 2|T| + 2 and g(V(Y) − T) ≤ 2|V(Y) − T| + 2, and the
smaller side A satisfies one of: |A| = 8 and X[A] = K_{4,4} − e; or |A| = 10 and X[A] is a pair-free
graph on 5 + 5 vertices with 19, 20 or 21 edges. In particular both sides have at least 8 vertices.
(c) F has at most one bad pair {T, V(Y) − T}.

*Proof.* (a) A component of F is 4-regular bipartite, so it has at least 4 vertices in each class.
If F is disconnected, its smallest component C has |C| ≤ m/2 ≤ 11, so |C| ∈ {8, 10} and F[C] is
K_{4,4} or K_{5,5} minus a perfect matching (the only 4-regular bipartite graphs on 4 + 4 and 5 + 5
vertices). Both are Hamilton-decomposable (THEORY §6.2a gives the two Hamilton cycles of K_{5,5} minus
a perfect matching), which is a pair in X. So F is connected, and c_F(T) ≥ 1 for every balanced T
with ∅ ≠ T ≠ V(Y).

(b) Let T be bad. Summing H-degrees over T, Σ_{v∈T} h(v) = 2|T| − D_Y(T) = 2e_H(T) + e_H(∂T), and
e_H(∂T) = ∂(T) − ∂_F(T) ≥ ∂(T) − 2. Since Σ_{v∈T} deg_Y v = 2e(T) + ∂(T), g(T) = D_Y(T) + ∂(T). Hence
2|T| − D_Y(T) ≥ g(T) − D_Y(T) − 2, that is g(T) ≤ 2|T| + 2; the same holds for V(Y) − T. Let A be the
smaller side; it is balanced and |A| ≤ m/2 ≤ 11, so |A| ∈ {2, 4, 6, 8, 10}. If |A| = 2, g(A) ≤ 6 < 10.
For |A| = 2t with t ≥ 2, e(A) = 3|A| − g(A)/2 ≥ 4t − 1, while e(A) ≤ t². This fails for t = 2, 3. For
t = 4, e(A) ≥ 15 and, by (F1), X[A] = K_{4,4} − e. For t = 5, 19 ≤ e(A) ≤ 21 by (F1), and X[A] is
pair-free because X is. The other side is at least as large as A. By (a), c_F(T) = 1.

(c) As in THEORY Lemma 6.1(b), using (a) and (b): two crossing bad pairs give four pairwise disjoint
bad sets (submodularity and posimodularity of ∂_F, all cuts even and at least 2), so m ≥ 32; two
non-crossing ones give, after complementing, bad sets T1 ⊊ T2, and M = T2 − T1 is balanced with
∂_F(M) ≤ 4, so 2|M| − 2 ≤ e_F(M) ≤ (|M|/2)², |M| ≥ 8 and m ≥ 24. ∎

So the bad pair is K_{4,4} − e | 10 vertices for n = 19; K_{4,4} − e | 12 vertices or 5 + 5 | 5 + 5
for n = 21; K_{4,4} − e | 14 vertices or 5 + 5 | 12 vertices for n = 23.

**Proposition C2 (repair; THEORY Proposition 6.6).** Let m ≤ 22, F a 4-factor of Y with bad pair
{T, V(Y) − T}, e1, e2 the two F-edges across ∂T, and D⁻ = D(F) − {e1, e2}. If D⁻ has a directed cycle
with exactly one arc leaving T and one arc entering T (a *one-crossing cycle*), and Z is a shortest
one, then F' = F Δ E(Z) has no bad set.

*Proof.* THEORY's proof of Proposition 6.6 applies word for word with Lemma C1 in place of THEORY
Lemma 6.1: c_F(T) = 1 and c_{F'}(T) = 2; a bad set W of F' is, by Lemma C1(c) for F', in the only bad
pair of F', which is not {T, V(Y) − T}; F' is connected by Lemma C1(a), so W does not cross T; after
complementing, W ⊊ R ∈ {T, V(Y) − T}, and M = R − W is balanced with 2 ≤ |M| ≤ m − 16 ≤ 6 by
Lemma C1(b) for W and V(Y) − R. From there the argument (F'[M] is an edge or K_{3,3}, all four
F'-edges across ∂T end in M, and the shortest choice of Z gives a contradiction) uses nothing about X
beyond these facts. ∎

## 3. The one-crossing lemma: notation and two tools

Let F have the bad pair {A, B}, A the smaller side (Lemma C1(b)), so c_F(A) = 1. As in ADD-B §1:
e1 = p1q' (p1 ∈ A_P, q' ∈ B_Q) and e2 = p'q1 (p' ∈ B_P, q1 ∈ A_Q) are the F-edges across; E0H is the
set of H-edges between A_Q and B_P (arcs A_Q → B_P), E1H the set of H-edges between A_P and B_Q (arcs
B_Q → A_P). For a ∈ E0H write y_a ∈ A_Q, x'_a ∈ B_P for its ends; for b ∈ E1H, x_b ∈ A_P and
y'_b ∈ B_Q. D_A = D(F)[A], D_B = D(F)[B]; R(x') is the set of vertices reachable from x' ∈ B_P in D_B.
For x ∈ A_P, y ∈ A_Q, x' ∈ B_P, y' ∈ B_Q let in(x), out(y), out'(x'), in'(y') be the numbers of E1H,
E0H, E0H, E1H edges at the vertex; each is at most 2. Put k0 = |E0H| and k1 = |E1H|.

ADD-B Lemma B1 holds verbatim (its proof uses only that e1, e2 are the F-edges across ∂A): D⁻ has a
one-crossing cycle iff there are a ∈ E0H, b ∈ E1H with x_b ⇝ y_a in D_A and x'_a ⇝ y'_b in D_B. Call
(a, b) *A-blocked* if x_b does not reach y_a in D_A and *B-blocked* if x'_a does not reach y'_b in D_B;
D⁻ has no one-crossing cycle iff

    (★) every (a, b) ∈ E0H × E1H is A-blocked or B-blocked.

**Lemma C3 (closed sets; ADD-B Lemma B3).** Let S ⊆ B be closed under the out-arcs of D_B, with
t = |S_P| ≥ 1, r = |S_Q|, and let k be the number of E1H arcs with tail in S. Then
s(S) = [p' ∈ S] + k and

    e(S) = 4t + 2r − D_Y(S_Q) − s(S),   so   (t − 2)(r − 4) ≥ 8 − D_Y(S_Q) − s(S),          (3.1)

and r ≥ 3, with r ≥ 4 unless S_P = {p'}. Also D_Y(S_Q) ≤ min(d, r + 1) ≤ min(6, r + 1) by (F2).

*Proof.* ADD-B's proof of Lemma B3: the arcs leaving a closed S ⊆ B are e2 (if p' ∈ S) and the E1H arcs
with tail in S; e_F(S) = 4t − [p' ∈ S]; e_H(S) = Σ_{q∈S_Q} h(q) − k = 2r − D_Y(S_Q) − k; and
e(S) ≤ tr. A vertex x' ≠ p' of B_P has its four F-neighbors in B_Q, and p' has three. ∎

**The 5 + 5 side (ADD-B (D2), (D3)).** If |A| = 10, then e_F(A) = 19; the complement F̄ of F[A] in the
complete bipartite graph on A_P ∪ A_Q has 6 edges, degree 2 at p1 and q1 and 1 elsewhere, and is
(α) the path y* p1 q1 x* plus a perfect matching of the other six vertices, or (β) the paths y1 p1 y2
and x0 q1 x1 plus a perfect matching between {x2, x3} and {y3, y4}. H[A] ⊆ F̄ and, by (F1),
e_H(A) = e(X[A]) − 19 ≤ 2. A vertex of A other than p1, q1 is *generic* and has exactly one
F̄-neighbor, written β(y) for generic y ∈ A_Q and γ(x) for generic x ∈ A_P. If (a, b) is A-blocked
then x_b y_a ∈ F̄ (otherwise x_b → y_a is an arc of D_A). (D3): if xy ∈ H[A], then x̃ ⇝ ỹ in D_A whenever
x̃y ∈ F and xỹ ∈ F (path x̃ → y → x → ỹ). The same holds for a 5 + 5 side B with p', q' and F̄_B.

## 4. Proof of the one-crossing lemma

**Theorem C3.** Let n ∈ {19, 21, 23} and let F be a 4-factor of Y with a bad pair. Then D⁻ has a
one-crossing cycle.

Assume (★). The shapes are those listed after Lemma C1.

### 4.1 A = K_{4,4} − e (n = 19, 21, 23)

As in ADD-B (D1): e_F(A) = (32 − 2)/2 = 15 = e(X[A]), so F[A] = X[A], no H-edge lies inside A, and
the missing pair is p1q1 (the two vertices of F[A]-degree 3). So for x ∈ A_P, y ∈ A_Q with
(x, y) ≠ (p1, q1) the arc x → y lies in D_A. Every x ∈ A_P has all its H-edges in E1H, so

    k1 = Σ_{x∈A_P} h(x) = 8 − D_Y(A_P) ≥ 8 − d ≥ 2.                                       (4.1)

Each y ∈ A_Q − {q1} has its four F-edges inside A and its h(y) H-edges in E0H. By (F2),
Σ_{y ∈ A_Q − q1} h(y) = 6 − D_Y(A_Q − q1) ≥ 6 − 4 = 2, so the set 𝒜 of a ∈ E0H with y_a ≠ q1 is not
empty. For a ∈ 𝒜 no pair (a, b) is A-blocked, so by (★) all are B-blocked: no E1H arc has its tail in
R(x'_a). Call a closed S ⊆ B with S_P ≠ ∅ and no E1H tail *good*; then s(S) = [p' ∈ S] ≤ 1 and (3.1)
gives, with D := D_Y(S_Q),

    (t − 2)(r − 4) ≥ 7 − D.                                                              (4.2)

- t = 1: (4.2) reads 4 − r ≥ 7 − D ≥ 6 − r. Impossible. t = 2: D ≥ 7 > 6. Impossible.
- t ≥ 3: r ≥ 5. If S_Q = B_Q, every E1H arc has its tail in S, so E1H = ∅, against (4.1). So
  5 ≤ r ≤ |B_Q| − 1.

*n = 19* (|B_Q| = 5): no good set exists, but R(x'_a) is one for a ∈ 𝒜. Contradiction.

*n = 21* (|B_Q| = 6): a good set has r = 5, and (4.2) is t − 2 ≥ 7 − D.
- t = 3: D ≥ 6 = r + 1, so d = 6 (deg w = 5), |N(w) ∩ S_Q| = 5, hence S_Q = N(w), and u1 ∈ S_Q. Then
  e(S) = 12 + 10 − 6 − s(S) ≤ 15 = 3 · 5 forces X[S] = K_{3,5}, and X[S + w] = K_{4,5} ⊇ K_{4,4},
  against (F1).
- t = 4, 5, 6: e(S) = 4t + 10 − D − s(S) ≥ 4t + 3 is at least 19, 23, 27 on 4 + 5, 5 + 5, 6 + 5
  vertices, against (F1).
So no good set exists; contradiction as for n = 19.

*n = 23* (|B_Q| = 7): a good set has r ∈ {5, 6}, and by (1.2) (|S| ≤ 14) s(S) ≥ 3 − [u1 ∈ S] − (r − t).
- r = 5: t = 3 gives K_{4,5} ⊆ X[S + w] exactly as for n = 21; t = 4 gives e(S) ≥ 19 on 4 + 5;
  t ≥ 5 gives r − t ≤ 0 and s(S) ≥ 2 by (1.2). All impossible.
- r = 6, t = 3: (4.2) gives D ≥ 5, so |N(w) ∩ S_Q| ≥ D − 1, and e(S) = 24 − D − s(S); then
  X[S + w] has classes of sizes 4 and 6 and at least 24 − D − s(S) + D − 1 ≥ 22 edges, against (F1).
- r = 6, t = 4: e(S) = 28 − D − s(S) ≤ 21 by (F1), so D = 6 and s(S) = 1.
- r = 6, t = 5: (1.2) gives u1 ∈ S and s(S) = 1; e(S) = 31 − D ≤ 26 by (F1), so D ≥ 5.
- r = 6, t ≥ 6: s(S) ≥ 2 by (1.2). Impossible.
So every good set S has |S_Q| = 6, |S_P| ∈ {4, 5} and s(S) = 1, so p' ∈ S.
For a ∈ 𝒜, R_a := R(x'_a) is good, so p' ∈ R_a and R(p') ⊆ R_a; R(p') is closed, contains p' and has
no E1H tail, so it is good too, and |R(p')_Q| = |(R_a)_Q| = 6 gives (R_a)_Q = R(p')_Q =: B_Q − z for
every a ∈ 𝒜. Every E1H arc has its tail outside R_a, so at z; hence k1 ≤ h(z) ≤ 2, and (4.1) gives
k1 = 2 = h(z), d = 6 = D_Y(A_P) and D_Y(B_P) = 0. The F-neighbors of z in B_P (four of them, or three if
z = q') lie outside R(p'), which has at least four of the seven vertices of B_P. So z = q',
|R(p')_P| = 4, B_P − R(p')_P = Z_P := N_F(q') ∩ B_P, and no R_a meets Z_P (it would contain q'), so
x'_a ∉ Z_P for a ∈ 𝒜. Each x ∈ Z_P has h(x) = 2. An H-edge from x to B_Q − q' = R(p')_Q would be an
arc leaving R(p'); the two H-edges at q' are in E1H. So both H-edges at x lie in E0H, and they are not
in 𝒜: their A-ends are q1. That is six E0H edges at q1, against h(q1) ≤ 2.

So (★) fails when A = K_{4,4} − e.

### 4.2 n = 21 and |A| = |B| = 10

(1) *Counts.* Each y ∈ A_Q has its H-edges in H[A] or in E0H, so k0 = Σ_{A_Q} h − e_H(A) =
10 − D_Y(A_Q) − e_H(A) ≥ 2; likewise k1 = 10 − D_Y(A_P) − e_H(A) ≥ 2, and from the B side
k1 = 10 − D_Y(B_Q) − e_H(B) with e_H(B) ≤ 2. As D_Y(A_Q) + D_Y(B_Q) = d ≤ 6,

    k0 + k1 = 20 − d − e_H(A) − e_H(B) ≥ 10.

(2) *Covering.* For a ∈ E0H, (★) gives E1H ⊆ {b : x_b ∈ N_F̄(y_a)} ∪ {b : y'_b ∈ N_F̄B(x'_a)}, so
k1 ≤ 2deg_F̄(y_a) + 2deg_F̄B(x'_a). For b ∈ E1H, likewise k0 ≤ 2deg_F̄(x_b) + 2deg_F̄B(y'_b).

(3) *k1 ≥ 5 is impossible.* By (2), no a ∈ E0H has both ends generic. Since q1p' = e2 ∈ F, every a has
exactly one of y_a = q1, x'_a = p', and (2) gives k1 ≤ 2·2 + 2·1 = 6 for every a. So k0 ≥ 4, while
k0 = out(q1) + out'(p') ≤ 4. Hence k0 = 4, k1 = 6 and out(q1) = out'(p') = 2. Take a1 ∈ E0H at q1
(x'_{a1} is generic; write γ_B(x'_{a1}) for its F̄_B-neighbor) and a2 ∈ E0H at p' (y_{a2} is
generic). With k1 = 6, (2) at a1 says that E1H is the disjoint union of the four E1H edges at the two
vertices of N_F̄(q1) (so in = 2 at both) and the two at γ_B(x'_{a1}); and (2) at a2 says that
in(β(y_{a2})) = 2.

In (α), N_F̄(q1) = {p1, x*}, and the only generic y with β(y) ∈ N_F̄(q1) is y* (β(y*) = p1). In (β),
N_F̄(q1) = {x0, x1}, whose only F̄-neighbor is q1, so there is none. Suppose β(y_{a2}) ∉ N_F̄(q1).
The three vertices N_F̄(q1) ∪ {β(y_{a2})} have in = 2 each, which uses up Σ_{x∈A_P} in(x) = 6, so every
E1H edge has its A_P-end among them. The two E1H edges at γ_B(x'_{a1}) avoid N_F̄(q1), so both join
γ_B(x'_{a1}) to β(y_{a2}): two parallel edges, impossible. Hence β(y_{a2}) ∈ N_F̄(q1): configuration
(α) and y_{a2} = y*. This holds for both E0H edges at p', which have distinct ends in A_Q.
Contradiction.

(4) *k0 ≥ 5 is impossible.* This is (3) with the roles of E0H and E1H exchanged. By (2) no b ∈ E1H has
both ends generic; as p1q' = e1 ∈ F, every b has exactly one of x_b = p1, y'_b = q'; so k1 ≤ 4, k0 ≤ 6,
hence k1 = 4, k0 = 6, in(p1) = in'(q') = 2. For b1 at p1, E0H is the disjoint union of the four E0H
edges at N_F̄(p1) and the two at γ'_B(y'_{b1}) (the F̄_B-neighbor of y'_{b1}); for b2 at q',
out(γ(x_{b2})) = 2. The only generic x with γ(x) ∈ N_F̄(p1) is x* in configuration (α)
(N_F̄(p1) = {q1, y*} in (α), {y1, y2} in (β)). If γ(x_{b2}) ∉ N_F̄(p1), the two E0H edges at
γ'_B(y'_{b1}) both join it to γ(x_{b2}): parallel edges. So both E1H edges at q' have x-end x*.
Contradiction.

Since k0 + k1 ≥ 10, (3) or (4) applies, so (★) fails. (As in ADD-B §4.2 the argument gives more: some
a, b have x_b y_a ∈ F and x'_a y'_b ∈ F, a one-crossing cycle of length 4.)

### 4.3 n = 23 and |A| = 10, |B| = 12

Here |B_P| = |B_Q| = 6 and k1 = 10 − D_Y(A_P) − e_H(A) ≥ 2.

**Lemma C4.** Every S ⊆ B with S_P ≠ ∅ has s(S) ≥ 2.

*Proof.* If S_Q = B_Q, all E1H arcs leave S, so s(S) ≥ k1 ≥ 2. Otherwise r = |S_Q| ≤ 5, t = |S_P| ≥ 1,
D = D_Y(S_Q) ≤ min(6, r + 1), and by (1.1) s(S) = 4t + 2r − e(S) − D.
- t = 1: e(S) ≤ r, s ≥ 4 + r − D ≥ 3. t = 2: e(S) ≤ 2r, s ≥ 8 − D ≥ 2.
- t = 3: e(S) ≤ 3r, s ≥ 12 − r − D; this is ≥ 3 for r ≤ 4, and for r = 5 it is ≥ 1 with equality only
  if D = 6 and X[S] = K_{3,5}, which gives K_{4,5} ⊆ X[S + w] as in §4.1. So s ≥ 2.
- t = 4: for r ≤ 3, s ≥ 16 − 2r − D ≥ 6; for r = 4, e(S) ≤ 15, s ≥ 4; for r = 5, e(S) ≤ 18 by (F1),
  s ≥ 2.
- t = 5: for r ≤ 3, s ≥ 20 − 3r − D ≥ 7; for r = 4, e(S) ≤ 18 (a bipartite graph on 5 + 4 vertices
  without K_{4,4} misses edges at two vertices of the 5-side), s ≥ 5; for r = 5, s ≥ 2 by (1.2).
- t = 6: r − t < 0 and s ≥ 3 by (1.2). ∎

Let 𝒴 = {y ∈ A_Q − {q1} : out(y) ≥ 1} (all generic) and Y0 = A_Q − {q1} − 𝒴.

*Step 1 (a generic tail).* Let y ∈ 𝒴, a ∈ E0H with y_a = y, R = R(x'_a). An E1H arc b with tail in R is
not B-blocked, so by (★) it is A-blocked and x_b = β(y). So s(R) = [p' ∈ R] + (number of E1H arcs from
R to β(y)) ≤ 3. Lemma C4 gives s(R) ≥ 2, so such an arc exists: **β(y) does not reach y in D_A**.

*Step 2 (one blocker).* For a closed R ⊆ B with R_P ≠ ∅ and s(R) ≤ 3, (3.1) gives: if r = 3 then
D + s ≥ 6 + t, so t = 1, D = 4 and R_P = {p'}; if r = 4 then D + s ≥ 8, so D = 5. In both cases
D = r + 1, so u1 ∈ R_Q. Let y1, y2 ∈ 𝒴 with β(y1) ≠ β(y2), a_i ∈ E0H at y_i and R_i = R(x'_{a_i}).
S = R1 ∩ R2 is closed, and an E1H arc with tail in S would have head β(y1) = β(y2); so s(S) ≤ 1 and, by
Lemma C4, S ⊆ B_Q. A vertex of S has no H-edge (into B_P it would give a P-vertex of S; E1H is
excluded), so it has D_Y = 2 and, by (F2), S ⊆ {u1}. Hence r1 + r2 ≤ 6 + |S| ≤ 7 with r_i ≥ 3. If
r1 = r2 = 3, both R_i have P-part {p'} and p' ∈ S. If {r1, r2} = {3, 4}, D_Y(R1_Q) + D_Y(R2_Q) = 4 + 5 = 9,
while it equals D_Y(R1_Q ∪ R2_Q) + D_Y(S) ≤ d + 2 ≤ 8. Both impossible. So all members of 𝒴 have the
same blocker β°. Two generic vertices of A_Q with a common F̄-neighbor are the two F̄-neighbors of p1
in configuration (β); so |𝒴| ≤ 2, with |𝒴| = 2 only in (β), 𝒴 = {y1, y2} and β° = p1.

*Step 3 (𝒴 is not empty).* A vertex y ∈ Y0 has out(y) = 0, so h(y) = deg_{H[A]}(y) ≤ deg_F̄(y) = 1 and
D_Y(y) = 2 − deg_{H[A]}(y). Hence 2|Y0| − e_H(A) ≤ D_Y(Y0) ≤ |Y0| + 1 by (F2), so |Y0| ≤ 3 and
|𝒴| ≥ 1. If |𝒴| = 1, then |Y0| = 3 and equality holds throughout: e_H(A) = 2 and the two H[A]-edges
have distinct Q-ends y5, y6 ∈ Y0.

*Step 4 (|𝒴| = 2 is impossible).* Let 𝒴 = {y1, y2} in (β). By Step 1, p1 reaches neither y1 nor y2.
Every edge xy of F̄ other than p1y1, p1y2 has x ≠ p1 and y ∉ {y1, y2}, so p1y ∈ F and xy1 ∈ F, and by
(D3) xy ∉ H[A] (it would give p1 ⇝ y1). So y3 and y4 have no H[A]-edge and, being in Y0, no E0H edge:
h(y3) = h(y4) = 0 and D_Y(y3) = D_Y(y4) = 2, against (F2).

*Step 5 (end).* So 𝒴 = {y°}, and by Step 3 H[A] = {x5y5, x6y6} with x_i = β(y_i). Fix i ∈ {5, 6}. If
β° ≠ x_i and y° ∉ N_F̄(x_i), then β°y_i ∈ F (the only F̄-neighbor of y_i is x_i) and x_iy° ∈ F, and
(D3) gives β° ⇝ y° in D_A, against Step 1 (β° = β(y°)). Otherwise x_i has the two F̄-neighbors y_i and
y° (if β° = x_i, then y° ∈ N_F̄(β°)), so x_i = p1 and {y_i, y°} = N_F̄(p1). This cannot hold for both
i = 5 and i = 6, since y5 ≠ y6. Contradiction.

So (★) fails in every shape, and Theorem C3 holds. ∎

## 5. Proof of Theorem C

Let X be a smallest W1b counterexample of C1 type with n ∈ {19, 21, 23}, w a good port (§1), Y = X − w
(m = n − 1 ≤ 22) and F a 4-factor of Y. If F has no bad set, (K) gives a pair in X. Otherwise F has a
unique bad pair (Lemma C1), Theorem C3 gives a one-crossing cycle, and Proposition C2 turns the
shortest one into a 4-factor F' of Y with no bad set; (K) gives a pair in X. Either way X has a pair,
a contradiction. ∎

## 6. Beyond 23 vertices

For n ≥ 25 (m ≥ 24) Lemma C1 fails as stated: two nested bad pairs become possible (|M| = 8 in
Lemma C1(c)), a disconnected 4-factor can have two components of 12 vertices, and both sides of a bad
pair can have 12 or more vertices; (F3) also stops at |S| ≤ 16. And (K) needs H_m for m ≥ 24, which is
not available (H24 is estimated at 50-100 core-hours in `wave4/theory/N.md`). So n = 23 is where this
route stops; going further is the S6 lane's all-sizes question.

## 7. Computer checks (rung (b))

All in `wave4/c1type/code/`. Python is `~/.cache/erdos585/venv/bin/python` (pysat CaDiCaL 1.5.3),
`pairc` is `reports/585-fable/tools/pairc`.

- `check_aside.py` (`check_aside.out`): pair test of every 5 + 5 side of Lemma C1(b) given by
  F̄ ∈ {(α), (β)} and H[A] ⊆ F̄ with |H[A]| ≤ 2 (44 graphs): 12 have a pair, 32 are pair-free; K_{4,4} − e
  is pair-free and K_{4,4} has a pair (controls). The 32 pair-free sides are exactly those with
  p1q1 ∉ H[A], H[A] not meeting both p1 and q1, and, in (β), not both matching edges in H[A].
- `c1_sat.py`, the analog of `wave4/theory/lemmaB_sat.py` for Y = X − w. Side A is fixed; F[B], H[B],
  the edges between A and B, N(w) ∩ Q and the position of u1 are variables. Constraints: F[B] has
  degree 4 except 3 at p', q'; every Q-vertex q has H-degree + [q ∈ N(w)] + [q = u1] = 2 (F2); every
  P-vertex has H-degree ≤ 2; |N(w)| = deg w ∈ {4, 5}; one u1; (★) by closure variables of D_B. Levels:
  `side` adds, for a 5 + 5 side B, the pair-free rules above and e_H(B) ≤ 2, and for a 6 + 6 or 7 + 7
  side B, no K_{4,4} in X[B] and e(S) ≤ 3|S| − 6 for S ⊆ B with |S| ≥ 3 (F3); `y` adds no K_{4,4} in
  X[B + w] and e(S) + |N(w) ∩ S| ≤ 3|S| − 3 for S ⊆ B with |S| ≥ 2 (F3). Option `qfree` replaces (F2)
  by "Q-vertices have H-degree ≤ 2 and D_Y(Q) = d"; option `allA` also runs the 12 sides A with a pair.
  Drivers: `run_cases.sh`, `run_cases2.sh`, `run_k44_23.sh`, `run_k44p.sh`. Total compute about
  3 core-hours, most of it in the two K_{4,4} − e runs at n = 23.
  - n = 19 (`c1_sat_19.out`): K_{4,4} − e | 5 + 5, deg w = 4, 5: UNSAT at every level, including with no
    B-side constraint (as §4.1 says); controls without (★) SAT.
  - n = 21 (`sat21_y.out`, level y): all 66 models (33 sides × 2 degrees) UNSAT; controls without (★)
    (`sat21_ctrl.out`): 66 of 66 SAT. The relaxed model with only what §4.2 uses (`qfree`, `allA`,
    only e_H(B) ≤ 2 on B; `sat21_proof.out`): 88 of 88 UNSAT for 5 + 5 | 5 + 5. (The same relaxation is
    SAT for K_{4,4} − e | 6 + 6 with deg w = 5, as expected: §4.1 uses (F2) and w.)
  - n = 23 (`sat23_y.out`, level y): 5 + 5 | 6 + 6, 64 of 64 models UNSAT. With `allA`
    (`sat23_allA.out`, the 44 sides of §4.3, which uses only e_H(A) ≤ 2): 88 of 88 UNSAT.
    K_{4,4} − e | 7 + 7: no answer within 1500 s for either degree (full model, `sat23_k44.out`), nor
    within 900 s for a lean model `k44p` that keeps only what §4.1 uses for n = 23 (no K_{4,4} in X[B]
    or X[B + w], and (1.2) for |S_P| ≥ 5, |S_Q| ∈ {5, 6}, |S_Q| ≤ |S_P| + 1; `sat23_k44p.out`; its
    controls without (★) are SAT, `sat23_k44p_ctrl.out`). **This shape rests on the written proof
    alone** (§4.1, n = 23).

## 8. What the result rests on

| Item | Used for | Status |
|---|---|---|
| PAIRS Lemma 1 (smallest counterexample is sparse E4 or C1, δ ≥ 4) | all | refereed, ACCEPT |
| PAIRS Example 4 (K_{4,4} has a pair) | all | refereed |
| C1P Lemma 4.4 (bad ports carry deficiency ≤ 2) | all | refereed twice, ACCEPT |
| Census F2 (no counterexample with n ≤ 18) | Corollary C | two methods |
| 5 + 5 pair-free census (none with ≥ 22 edges) | all | one method (genbg + pairc), re-run in THEORY |
| Census H18, H20 | n = 19, 21 | two methods (SCOUT §2.3, referee) |
| Census H22 | n = 23; ADD-B Corollary B | one method |
| PAIRS Proposition 5 with census L5 (via F3) | n = 23 only | Prop 5 refereed with fix; L5 one method, referee spot check |
| THEORY Lemma 1.1 and Proposition 6.6; ADD-B Lemmas B1, B3, (D1)-(D3) | all | unreviewed (frozen for review) |
| ADD-B Corollary B (E4 type, n ≤ 22) | Corollary C | unreviewed (frozen) |
| Theorem C (this paper) | | unreviewed; SAT cross-checks in §7 for every shape except K_{4,4} − e at n = 23 |
