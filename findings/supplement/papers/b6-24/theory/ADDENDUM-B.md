# Addendum B: one-crossing cycles below 23 vertices (Lemma B), and no smallest E4-type counterexample on at most 22 vertices

wave4/theory (Pass 3 wave 4), October 5, 2026. Frozen for review (SHA-256 in `FROZEN-B.sha256`).
Written proof plus a SAT cross-check. Not reviewed. No Lean, no `check.sh`. Rungs as in STATE.md:
Theorem B is (a); Corollary B is (a) given the censuses listed in §6; the checks of §5 are (b).

"PAPER" is `wave4/theory/PAPER.md` (frozen, SHA-256 521a1139…). "PAIRS" is
`reports/585-next/wave3/pairs/PAPER.md` (frozen 6fad9b43…, refereed ACCEPT WITH FIXES in
`wave3/pairs/REVIEW.md`; Prop 5 is used with the referee's fix |S| ≥ 3). Notation is PAPER §1.

## 0. Results

**Theorem B (Lemma B of PAPER §6.2a).** Let X be a smallest W1b counterexample of E4 type with
n ≤ 22, F a 4-factor of X with a bad set, {T, V − T} its bad pair, e1, e2 the F-edges across ∂T and
D⁻ = D(F) − {e1, e2}. Then D⁻ has a one-crossing cycle (a directed cycle with exactly one arc leaving T
and one arc entering T).

**Corollary B.** There is no smallest W1b counterexample of E4 type with n ≤ 22. So if W1b fails on
some bipartite graph with at most 22 vertices, a smallest counterexample is of C1 type with
n ∈ {19, 21}.

The proof does not use PAIRS Lemma 7 or its case distinction: it shows directly that a one-crossing
cycle exists, so PAIRS Lemma 7(b) cannot occur in this setting.

## 1. Setting

Let X, F be as in Theorem B. By PAIRS Lemma 1 and census F2, X is a sparse E4 instance with δ ≥ 4 and
e = 3n − 4, and n ∈ {20, 22} (n ≥ 19, n even). Write H = X − F and h(v) = deg v − 4 ∈ {0, 1, 2} (the
H-degree), so D(v) = 6 − deg v = 2 − h(v). By PAPER Lemma 6.1 and §6.2a, F is connected, {T, V − T} is
its only bad pair, c_F(T) = 1, and the smaller side A of the pair satisfies

- X[A] = K_{4,4} − e (|A| = 8), or
- X[A] is a pair-free graph on 5 + 5 vertices with 19, 20 or 21 edges (|A| = 10).

Put B = V − A; B is balanced and |B| = n − |A| ∈ {10, 12, 14}. A cycle crosses ∂T exactly twice iff it
crosses ∂A exactly twice, so we may and do take T = A.

Since c_F(A) = 1, F has exactly one edge between A_P and B_Q, e1 = p1 q' (p1 ∈ A_P, q' ∈ B_Q), and
exactly one between A_Q and B_P, e2 = p' q1 (p' ∈ B_P, q1 ∈ A_Q). Every other edge between A and B is an
H-edge. Let E0H be the set of H-edges between A_Q and B_P (arcs A_Q → B_P of D(F), leaving A) and E1H
the set of H-edges between A_P and B_Q (arcs B_Q → A_P, entering A). For a ∈ E0H write y_a ∈ A_Q and
x'_a ∈ B_P for its ends; for b ∈ E1H write x_b ∈ A_P and y'_b ∈ B_Q. For y ∈ A_Q let out(y) be the
number of E0H edges at y, and for x ∈ A_P let in(x) be the number of E1H edges at x; both are at most
2. D_A = D(F)[A] and D_B = D(F)[B] are the subdigraphs of D⁻ induced on A and on B (e1 and e2 cross).
"x ⇝ y in D_A" means that D_A has a directed path from x to y.

**Lemma B1 (reduction).** D⁻ has a one-crossing cycle iff there are a ∈ E0H and b ∈ E1H with
x_b ⇝ y_a in D_A and x'_a ⇝ y'_b in D_B.

*Proof.* The arcs of D⁻ between A and B are exactly the E0H arcs (out of A) and the E1H arcs (into A).
So a one-crossing cycle is an E0H arc a, a path of D_B from x'_a to y'_b, an E1H arc b and a path of
D_A from x_b to y_a. Conversely two such paths lie in the disjoint sets B and A, so together with a and
b they form a directed cycle that crosses ∂A twice. ∎

Call a pair (a, b) ∈ E0H × E1H *A-blocked* if x_b does not reach y_a in D_A, and *B-blocked* if x'_a
does not reach y'_b in D_B. Theorem B fails iff

    (★) every pair (a, b) ∈ E0H × E1H is A-blocked or B-blocked.

## 2. The small side A

**(D1) A = K_{4,4} − e.** e_F(A) = (4|A| − ∂_F(A))/2 = 15 = e(X[A]), so F[A] = X[A] and no H-edge lies
inside A. In F[A] the vertices p1 and q1 have degree 3 (their fourth F-edges are e1 and e2) and the
others degree 4; in K_{4,4} − e the vertices of degree 3 are the ends of the missing edge. So
X[A] = K_{4,4} − p1q1, and for every x ∈ A_P, y ∈ A_Q with (x, y) ≠ (p1, q1) the F-arc x → y lies in
D_A. Hence a pair (a, b) can be A-blocked only if (x_b, y_a) = (p1, q1).

**(D2) A of 5 + 5 vertices.** e_F(A) = (40 − 2)/2 = 19, so e_H(A) = e(X[A]) − 19 ≤ 2. Let F̄ be the
complement of F[A] in the complete bipartite graph on A_P ∪ A_Q. It has 6 edges, degree 2 at p1 and q1
and degree 1 at the other eight vertices, and H[A] ⊆ F̄ (X is simple). If xy ∉ F̄ then x → y is an arc
of D_A; so if (a, b) is A-blocked then x_b y_a ∈ F̄. As F̄ has maximum degree 2 and only one vertex of
degree 2 on each side, it is a union of paths, and up to names it is one of

- (α) the path y* p1 q1 x* plus a perfect matching between A_P − {p1, x*} and A_Q − {q1, y*};
- (β) the paths y1 p1 y2 and x0 q1 x1 plus a perfect matching between {x2, x3} and {y3, y4}.

Call y ∈ A_Q − {q1} and x ∈ A_P − {p1} *generic*. A generic y has exactly one F̄-neighbor β(y) (its
*blocker*), and a generic x exactly one F̄-neighbor γ(x). Put Bl(y) = {x ∈ A_P : x does not reach y in
D_A} ⊆ N_F̄(y) and Bl*(x) = {y ∈ A_Q : x does not reach y in D_A} ⊆ N_F̄(x).

**(D3) Rescue.** If xy ∈ H[A], the arc y → x lies in D_A. So x̃ ⇝ ỹ in D_A whenever x̃y ∈ F and xỹ ∈ F
(path x̃ → y → x → ỹ).

## 3. Two lemmas on low-slack sets

Recall s(S) = |δ⁺_{D(F)}(S)| = g(S)/2 − j(S) − D(S_Q) (PAPER Lemma 1.1). Let in(S) be the number of
arcs of D(F) entering S: in(S) = e_F(P − S, S_Q) + e_H(Q − S, S_P). The F-degree sums over S_Q and S_P
give in(S) = 4|S_Q| − 4|S_P| + ∂_P(S) = g(S)/2 + j(S) − D(S_P) (by PAPER (1.1)). This is s(S) with P and
Q exchanged; the proof of PAPER Lemma 3.1 uses only sparsity and D(P) = D(Q) = 4, so its classification
holds for in(S) with P and Q exchanged.

**Lemma B2 (no low-slack set with at most 6 vertices on one side).** Let S ⊆ V with 2 ≤ |S| ≤ n − 1.
(i) If S_P ≠ ∅ and |S_Q| ≤ 6, then s(S) ≥ 2. (ii) If S_Q ≠ ∅ and |S_P| ≤ 6, then in(S) ≥ 2.

*Proof.* (i) Suppose s(S) ≤ 1. By PAPER Lemma 3.1, S has type F1, F2 or U0-U4.

- Types F1, U0, U1 have g(S) = 10 and j(S) ∈ {0, 1}, so |S| ≤ 2|S_Q| ≤ 12. If |S| ≥ 3, PAIRS Prop 5
  and census L5 give |S| ≥ 18. If |S| = 2, then S is an edge pq with j = 0 (type U0) and
  ∂_Q(S) = deg q − 1 ≥ 3, while U0 has ∂_Q(S) = 1.
- Types F2, U3, U4 have j = 2 and e(S) ∈ {6t, 6t − 1} with t = |S_P| ≥ 1; e(S) ≤ t(t + 2) forces t ≥ 4,
  so (|S_P|, |S_Q|) = (4, 6) and e(S) ≥ 23.
- Type U2 has j = 1 and e(S) = 6t − 3 ≤ t(t + 1), so t ≥ 5, (|S_P|, |S_Q|) = (5, 6) and e(S) = 27.

A bipartite graph on 4 + 6 vertices with at least 23 edges, or on 5 + 6 vertices with at least 27
edges, contains K_{4,4}. In the first case at most one pair is missing: delete its end on the 6-side and
one more vertex of that side. In the second case at most three pairs are missing: delete a vertex of the
5-side that meets a missing pair, then the ends on the 6-side of the at most two remaining missing
pairs, then further vertices of the 6-side until four remain. K_{4,4} has a pair (PAIRS Example 4) and X
has none. (ii) is (i) with P and Q exchanged. ∎

For x' ∈ B_P let R(x') be the set of vertices reachable from x' in D_B, and for y' ∈ B_Q let C(y') be
the set of vertices of B from which y' is reachable in D_B.

**Lemma B3 (reach sets).** Let x' ∈ B_P, R = R(x'), t = |R_P|, r = |R_Q|. Then the arcs of D(F)
leaving R are e2 (if p' ∈ R) and the E1H arcs with tail in R, and

    e(R) = 4t + 2r − D(R_Q) − s(R),   hence   (t − 2)(r − 4) ≥ 8 − D(R_Q) − s(R).

If x' ≠ p', the four F-neighbors of x' lie in R_Q. Consequently, if s(R) ≤ 3 then either R is *big*
(t ≥ 3 and r ≥ 5) or R is *tiny*: x' = p', t = 1, r = 3, D(R_Q) = 4 and s(R) = 3.
Mirror: for y' ∈ B_Q and C = C(y'), t̃ = |C_Q|, r̃ = |C_P|, the arcs of D(F) entering C are e1 (if q' ∈ C)
and the E0H arcs with head in C, e(C) = 4t̃ + 2r̃ − D(C_P) − in(C), and if in(C) ≤ 3 then C is big
(t̃ ≥ 3, r̃ ≥ 5) or tiny (y' = q', t̃ = 1, r̃ = 3, D(C_P) = 4, in(C) = 3).

*Proof.* R is closed under the out-arcs of D_B. An F-edge at p ∈ R_P is the arc p → q, so q ∈ R unless
q ∉ B, which happens only for e2 at p = p'. An H-edge at q ∈ R_Q is the arc q → p, so p ∈ R unless
p ∈ A, i.e. the edge lies in E1H. This gives the arcs leaving R, so s(R) = [p' ∈ R] + k with k the number
of E1H arcs with tail in R; e_F(R) = 4t − [p' ∈ R]; and e_H(R) = Σ_{q ∈ R_Q} h(q) − k = 2r − D(R_Q) − k.
Adding gives e(R), and e(R) ≤ tr gives the inequality. A vertex x' ≠ p' of B_P has all four F-edges
inside B (only p' has an F-edge to A). If s(R) ≤ 3 then, as D(R_Q) ≤ D(Q) = 4, (t − 2)(r − 4) ≥ 1:
t = 2 is impossible, t ≥ 3 forces r ≥ 5, and t = 1 forces r ≤ 3; as R ⊇ N_F(x') ∩ B, which has four
vertices unless x' = p' and three if x' = p', t = 1 gives x' = p', r = 3 and equality
D(R_Q) + s(R) = 7. The mirror is the same argument with all arcs reversed. ∎

## 4. Proof of Theorem B

Assume (★). There are three shapes: A = K_{4,4} − e (n = 20 or 22); |A| = 10 and n = 20; |A| = 10
and n = 22.

### 4.1 A = K_{4,4} − e

Every y ∈ A_Q − {q1} has its four F-edges and no H-edge inside A (D1), so out(y) = h(y) and
Σ_{y ≠ q1} out(y) = Σ_{y ≠ q1} (2 − D(y)) ≥ 6 − D(Q) = 2. Take a ∈ E0H with y_a ≠ q1. By (D1) no pair
(a, b) is A-blocked, so by (★) all of them are B-blocked: no E1H arc has its tail in R = R(x'_a). By
Lemma B3, s(R) = [p' ∈ R] ≤ 1. Here R ⊆ B, x'_a ∈ R and |R| ≥ 2. If |R_Q| ≤ 6, Lemma B2(i) gives
s(R) ≥ 2, a contradiction. Otherwise |B| = 14 and R_Q = B_Q, so E1H = ∅; but every x ∈ A_P has all its
H-edges outside A, so |E1H| = Σ_{x ∈ A_P} h(x) = 8 − D(A_P) ≥ 4. Contradiction.

### 4.2 n = 20 and |A| = 10

Then |B| = 10, and PAPER Lemma 6.1(a) applies to B too, so (D2) holds for B: e_H(B) ≤ 2, and with F̄_B
the complement of F[B] in B_P × B_Q (degree 2 at p' and q', degree 1 elsewhere), x' → y' is an arc of
D_B whenever x'y' ∉ F̄_B. So (a, b) is B-blocked only if x'_a y'_b ∈ F̄_B.

Counting the edges at A and at B: ∂(A) = Σ_{v ∈ A} deg v − 2e(A) = (60 − D(A)) − 2(19 + e_H(A)) =
22 − D(A) − 2e_H(A), and likewise ∂(B) = 22 − D(B) − 2e_H(B). With ∂(A) = ∂(B) and D(A) + D(B) = 8 this gives
∂(A) = 18 − e_H(A) − e_H(B) ≥ 14, so |E0H| + |E1H| = ∂(A) − 2 ≥ 12. Also |E0H| ≤ Σ_{y ∈ A_Q} h(y) ≤ 10
and |E1H| ≤ 10, so |E0H|, |E1H| ≥ 2.

Write d(v) for the degree of v in F̄ or F̄_B. Fix a ∈ E0H. By (★) each b ∈ E1H has x_b ∈ N_F̄(y_a) or
y'_b ∈ N_F̄B(x'_a), and at most two E1H edges meet any vertex, so |E1H| ≤ 2d(y_a) + 2d(x'_a).
Likewise |E0H| ≤ 2d(x_b) + 2d(y'_b) for each b ∈ E1H.

- If some b has x_b ≠ p1 and y'_b ≠ q', then |E0H| ≤ 4, so |E1H| ≥ 8, so every a has
  d(y_a) = d(x'_a) = 2, i.e. y_a = q1 and x'_a = p'. But q1p' = e2 is an F-edge, so E0H = ∅,
  contradicting |E0H| ≥ 2.
- Otherwise every b has x_b = p1 or y'_b = q', so |E1H| ≤ 4 (at most two E1H edges at p1 and two at
  q') and |E0H| ≥ 8; then every b has d(x_b) = d(y'_b) = 2, i.e. x_b = p1 and y'_b = q', but p1q' = e1 is
  an F-edge, so E1H = ∅. Contradiction.

(So for n = 20 and |A| = |B| = 10 there is even a one-crossing cycle of length 4.)

### 4.3 n = 22 and |A| = 10

Then |B| = 12, so |B_P| = |B_Q| = 6 and Lemma B2 applies to every subset of B with at least 2 vertices.

**Step 1 (a generic tail).** Let y ∈ A_Q − {q1}, a ∈ E0H with y_a = y, and R = R(x'_a). An E1H arc b
with y'_b ∈ R is not B-blocked, so by (★) it is A-blocked: x_b ∈ Bl(y) ⊆ {β(y)}. Hence
s(R) ≤ 1 + in(β(y)) ≤ 3. Lemma B2(i) gives s(R) ≥ 2, so such an arc b exists and β(y) ∈ Bl(y): β(y)
does not reach y in D_A. By Lemma B3, R is big, or tiny with x'_a = p'. If R is tiny, then
R = {p'} ∪ R_Q with |R_Q| = 3, no H-edge lies inside R (R_Q ⊆ N_F(p')), and the H-degree total of R_Q is
2r − D(R_Q) = 2, carried by E1H edges into the single vertex β(y); so R_Q has exactly one vertex of
degree 4 (the other two have degree 5).

**Step 2 (one blocker).** Let y1, y2 be generic with β(y1) ≠ β(y2), and a_i ∈ E0H with y_{a_i} = y_i.
Then S = R(x'_{a_1}) ∩ R(x'_{a_2}) is closed under the out-arcs of D_B, and an E1H arc b with y'_b ∈ S
would need x_b ∈ Bl(y1) ∩ Bl(y2) = ∅. So no E1H arc leaves S and s(S) ≤ [p' ∈ S] ≤ 1. If S contains a
P-vertex, it also contains its at least three F-neighbors in B, and Lemma B2(i) is contradicted. So
S ⊆ B_Q, and each q ∈ S has no H-edge (an H-neighbor in B would lie in S, and E1H edges at q are
excluded), so deg q = 4 and 2|S| = D(S) ≤ D(Q) = 4. Now if both reach sets are big,
|S| ≥ 5 + 5 − 6 = 4; if one is big and one tiny, |S| ≥ 5 + 3 − 6 = 2 while the tiny one contains only
one vertex of degree 4; if both are tiny, x'_{a_1} = x'_{a_2} = p' and S ∋ p'. Each case is impossible.
So all vertices of 𝒴 = {y ∈ A_Q − {q1} : out(y) ≥ 1} have the same blocker. Two generic vertices with a
common F̄-neighbor are the two F̄-neighbors of p1 in configuration (β); hence |𝒴| ≤ 2, and |𝒴| = 2 only
in configuration (β) with 𝒴 = {y1, y2}.

**Step 3 (𝒴 is not empty).** Let Y0 = A_Q − {q1} − 𝒴. For y ∈ Y0, out(y) = 0, so h(y) is the H[A]-degree
of y, which is at most its F̄-degree 1, and D(y) = 2 − deg_{H[A]}(y). Hence
4 ≥ D(A_Q) ≥ 2|Y0| − e_H(A) ≥ 2|Y0| − 2, so |Y0| ≤ 3 and |𝒴| ≥ 1. If |𝒴| = 1, then e_H(A) = 2, the two
H[A]-edges have distinct Q-ends in Y0, and D(A_Q) = 4.

**Steps 1'-3' (mirror).** The same three steps run with E1H arcs, co-reach sets C(y'), Lemma B2(ii)
and the mirror of Lemma B3. Step 1': for a generic x and b ∈ E1H with x_b = x, an E0H arc with head in
C = C(y'_b) is not B-blocked, so its tail lies in Bl*(x) ⊆ {γ(x)}; hence in(C) ≤ 1 + out(γ(x)) ≤ 3,
Lemma B2(ii) gives in(C) ≥ 2, so x does not reach γ(x) in D_A, and C is big, or tiny with y'_b = q'
(then C_P has exactly one vertex of degree 4). Step 2': all vertices of
𝒳 = {x ∈ A_P − {p1} : in(x) ≥ 1} have the same γ (for generic x1, x2 with γ(x1) ≠ γ(x2), the
intersection of the two co-reach sets receives no E0H arc, so in(S) ≤ 1, and by Lemma B2(ii) it
consists of P-vertices without H-edges, so of at most two degree-4 vertices; the overlap counts of
Step 2 then give a contradiction); so |𝒳| ≤ 2, with |𝒳| = 2 only in configuration (β) with
𝒳 = {x0, x1}. Step 3': |𝒳| ≥ 1, and |𝒳| = 1 forces
e_H(A) = 2, both H[A]-edges with distinct P-ends in X0 = A_P − {p1} − 𝒳, and D(A_P) = 4.

**Step 4 (H[A] when |𝒴| = 2).** Let 𝒴 = {y1, y2} (configuration (β), common blocker p1). By Step 1, p1
reaches neither y1 nor y2 in D_A. Every edge of F̄ other than p1y1, p1y2 has its Q-end outside
{y1, y2} and its P-end different from p1, so by (D3) it is not in H[A] (it would give p1 ⇝ y1). Hence
H[A] ⊆ {p1y1, p1y2}, the vertices y3, y4 have no H-edge at all, D(y3) = D(y4) = 2, D(A_Q) = 4 and
D(q1) = D(y1) = D(y2) = 0. Mirror: if 𝒳 = {x0, x1}, then H[A] ⊆ {x0q1, x1q1}, D(A_P) = 4 and
D(p1) = D(x0) = D(x1) = 0.

**Step 5 (end).** By Steps 2, 3 and their mirrors, |𝒴|, |𝒳| ∈ {1, 2}.

- If |𝒴| = 2, then H[A] ⊆ {p1y1, p1y2} has no P-end in X0, so |𝒳| ≠ 1 by Step 3'; hence |𝒳| = 2,
  H[A] ⊆ {x0q1, x1q1} as well, and H[A] = ∅. Symmetrically |𝒳| = 2 forces |𝒴| = 2.
- If |𝒴| = |𝒳| = 1, let 𝒴 = {y°}, β° = β(y°), and let xy be an H[A]-edge (x ∈ X0, y ∈ Y0, both generic,
  so N_F̄(y) = {x} and N_F̄(x) = {y}). Then x ≠ β° (otherwise x would have the two F̄-neighbors y and
  y°), so β°y ∈ F; and y° ≠ y, so xy° ∈ F. By (D3), β° ⇝ y° in D_A, contradicting Step 1.
- If |𝒴| = |𝒳| = 2 and H[A] = ∅ (configuration (β)), then D(A) = 8 by Step 4, so D(B) = 0. Since
  h(y1) = 2 and no H-edge lies in A, y1 has two E0H edges; let a1 be one with x'_{a_1} ≠ p', so
  R1 = R(x'_{a_1}) is big (Step 1) and its E1H arcs go into Bl(y1) ⊆ {p1}. Since h(q1) = 2, q1 has an
  E0H edge a2; R2 = R(x'_{a_2}) contains at least three Q-vertices, and its E1H arcs go into
  Bl(q1) ⊆ N_F̄(q1) = {x0, x1}. As in Step 2, S = R1 ∩ R2 is closed, no E1H arc leaves it, s(S) ≤ 1, so
  S ⊆ B_Q consists of vertices of degree 4; there are none (D(B) = 0), so S = ∅. But
  |R1_Q| + |R2_Q| ≥ 5 + 3 > 6 = |B_Q|. Contradiction.

So (★) fails in every case, and Theorem B holds. ∎

*Proof of Corollary B.* Let X be a smallest W1b counterexample of E4 type with n ≤ 22. It has a
4-factor F (PAIRS Lemma 2). If F has no bad set, F has no cut of at most 2 edges (such a cut is
balanced, PAPER §1), and census H22 makes F Hamilton-decomposable: a pair in X. Otherwise F is
connected with c_F(T) = 1 (PAPER §6.2a), Theorem B gives a one-crossing cycle, and PAPER Proposition 6.6
turns the shortest one into a 4-factor F' with no cut of at most 2 edges; H22 again gives a pair. With
F2 (no counterexample on at most 18 vertices), a smallest counterexample on at most 22 vertices is of C1
type, with n odd: 19 or 21. ∎

## 5. Computer checks (rung (b))

- `lemmaB_sat.py` (pysat CaDiCaL; output `lemmaB_sat.out`). For each shape, the side A is fixed
  (K_{4,4} − p1q1, or F̄ in configuration (α) or (β) together with each of the 22 choices of H[A] ⊆ F̄
  with |H[A]| ≤ 2), and F[B], H[B] and all H-edges between A and B are variables. Constraints: F[B]
  has degree 4 except 3 at p' and q'; every H-degree is at most 2; there are n − 4 H-edges
  (equivalently D(P) = D(Q) = 4); for a 5 + 5 side B, e_H(B) ≤ 2; for a 6 + 6 or 7 + 7 side B, no
  K_{4,4} in X[B] and e(S) ≤ 3|S| − 6 for every S ⊆ B with |S| ≥ 3 (the only facts about B the proof
  uses); and (★), encoded with one closed-set variable vector per x' ∈ B_P (a closed set of D_B
  containing x' and avoiding y' certifies that x' does not reach y'). Result: UNSAT in all 90
  configurations (44 for n = 20 with |A| = |B| = 10, 1 for K_{4,4} − e with B of 6 + 6, 44 for n = 22
  with |A| = 10, 1 for K_{4,4} − e with B of 7 + 7). Controls: the same models without the (★)
  clauses are SAT in all 90. For the 46 configurations whose side B has 6 + 6 or 7 + 7 vertices, the
  models stay UNSAT even without the B-side constraints, so for those shapes no fact about B beyond
  the degree counts is needed (the A side still comes from PAPER Lemma 6.1); the written proof uses
  more than it needs there.
- `lemmaB_sat_test.py` (`lemmaB_sat_test.out`), a test of the encoding: with the H-edge count replaced
  by "at least k E0H and at least k E1H edges", the models with the (★) clauses are SAT for k = 1, 3, 5
  (except two shapes at k = 5), and a plain BFS on each decoded model finds no one-crossing pair.
- `census_side.sh` (`census_side.out`, genbg + pairc): every bipartite graph on 4 + 6 vertices with 23
  or 24 edges and on 5 + 6 vertices with 27 to 30 edges has a pair (2 and 11 graphs), as Lemma B2
  uses. (Also: 5 + 7 vertices with 29 edges: 1 of 79 graphs is pair-free; 30 or 31 edges, and 6 + 7
  vertices with 33 to 35 edges: none. Not used.)
- `final_checks.sh` (`census55.out`): pair-free 5 + 5 graphs with 19, 20, 21, 22+ edges: 62, 24, 8, 0
  (the census behind PAPER Lemma 6.1(a)).

## 6. What the result rests on

| Item | Status |
|---|---|
| PAIRS Lemma 1, Lemma 2 | refereed, ACCEPT |
| PAIRS Example 4 (K_{4,4} has a pair) | refereed, ACCEPT WITH FIX F2 (the fix concerns a remark, not this claim) |
| PAIRS Prop 5 (g = 10, \|S\| ≥ 3 ⇒ 4-core ≥ 18 vertices) | refereed, ACCEPT WITH FIX F1 (\|S\| ≥ 3) |
| Census F2 (no counterexample with n ≤ 18) | two methods |
| Census L5 (used by Prop 5) | one method, referee spot check |
| 5 + 5 pair-free census (PAPER Lemma 6.1(a)) | one method (genbg + pairc), re-run in this session |
| Census H22 (Corollary B only) | one method at n = 22, two for n ≤ 20 |
| PAPER Lemma 1.1, Lemma 3.1, Lemma 6.1, Proposition 6.6 | unreviewed (PAPER is frozen for review) |
| Theorem B (this addendum) | unreviewed; SAT cross-check of the case analysis in §5 |

What Corollary B gives (see `N.md`): it removes the E4 type below 23 vertices. It does not move the
B6 bound on its own, because n = 19 and n = 21 are C1-only sizes; the C1 type (PAPER §7) is the next
step. The method (reach sets of the far side, blocked pairs inside the dense side, and Lemma B2 for
low-slack sets with at most 6 vertices on one side) is local, so it may transfer to the port-deleted
instances Y = X − y of the C1 type, where PAPER Lemma 7.1(iii) gives s(S) ≥ 2 − [u1 ∈ S] − j(S).
