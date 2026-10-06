# G110: the small-cut lemma, a minimal C0 counterexample, petal uncrossing, and size bounds

Author lane M1, October 4-5, 2026. Status: frozen for independent review (SHA-256 in
`FROZEN.sha256`). Written proofs, with computational checks of the counting identities in
Appendix A. Not reviewed. No Lean and no `check.sh` run, so nothing here is a project oracle PASS.
Rungs: the lemmas are (a); the size statements are (b) (special cases), proved on paper, three of
them conditional on a census. One item of the brief is false as stated (FLAW.md).

## 0. Results at a glance

| Item | Statement (short form) | Verdict | Section |
|---|---|---|---|
| G-1 | B − o − y without spanning 4-factor gives X with ∂_B(X) = 6k + 2ε ∈ {6,8,10,12}, \|X\| ≥ 10 (11 if k = 1), \|V(B) − X\| ≥ 12 (13 if k = 1) | TRUE, proved | §1 |
| G-1 corollary | no such cut implies every B − o has a quartic subgraph; covers every B on ≤ 20 vertices | TRUE, with a wording note: the 20-vertex coverage comes from \|X\| + \|Y\| ≥ 22, not from the literal "side ≤ 9" hypothesis | §1 |
| (1a) | a minimal C0 counterexample has larger-side minimum degree 5, so it is a G110 gadget | TRUE | §2.1 |
| (1b) | every negative cut of Γ − y is of type (2,5,0), with the listed data | TRUE | §2.1 |
| (1c) | e(y', C_y) ≥ 2, cases e = 0, 1 excluded | TRUE (strengthened to ≥ 4 in §2.5) | §2.2 |
| (2) | trace lemma, x ∈ {0,4}, 35-trace interface | TRUE | §2.3 |
| (3) | X + β has 2c + 3 vertices and 3n − 2 edges, so X realizes some τ; Q + α has 3n edges | TRUE (and Q realizes a τ inside every 5-subset) | §2.3 |
| (4) | distinct I−C endpoints give an E3 instance, so Q realizes τ; at most 3 of the 7 edges per vertex | TRUE | §2.4 |
| (U) | six-port uncrossing: two petals share at most one vertex, an I-vertex with 3 + 3 petal neighbors | TRUE, every step verified by hand; identities checked numerically | §2.5 |
| §3 warm-up | under F1(N1), F2(N2): 2m + 1 ≥ N1 + N2 + 2; with 14, 18: C0 for m ≤ 16 | TRUE, conditional | §3.1 |
| §3 main | under F2(N2) and (U): 2m + 1 ≥ 6(N2 + 1); with N2 = 18: C0 for m ≤ 56 | TRUE, conditional on F2(18) only | §3.2 |
| §3 M1 refinement | adding the hub count: C0 for m ≤ 59, conditional on F2(18) | TRUE, conditional | §3.3 |
| §3 M1 unconditional | C0 for m ≤ 41 with no census | TRUE, proved | §3.4 |
| Remark, C1 sub-case | "P2 + β at 3n − 2" | FALSE as stated when ε = 1: the count is 3n − 2 − ε (see FLAW.md); TRUE for ε = 0 | §4.4 |
| Remark, C1 sub-case | "P1 + α_τ in E4 for distinct-endpoint 4-traces" | TRUE | §4.4 |

G110-quartic for a bipartite 6-regular B means: B − o has a 4-regular subgraph for every vertex o.
A C0 instance of size m is B − o for |V(B)| = 2m + 2 when it is a G110 gadget, so "C0 for m ≤ 41"
gives G110-quartic for every simple bipartite 6-regular B on at most 84 vertices, without a census.
None of this is a pair statement (§5).

**Where to attack first.**
1. Theorem 2.9 (U) with Lemma 2.8. Everything after §2.4 rests on it: the submodularity of ε (a
   directed cut count), the use of the minimum slack −1 in step 2, and the two uses of minimality
   in steps 4 and 5 (Γ[W] and Γ[Z] are C0 instances).
2. Prop. 2.3 (claim 1b): excluding k = 1 cuts uses (M) for E3 pieces of size at most m − 1, and
   (M) uses Corollary 0.6, the reviewed E3 reduction with the trivial-piece case made explicit.
3. Prop. 2.12(3)-(4), Lemma 3.4 and Theorem 3.5 (C0 for m ≤ 41 with no census). These are new
   here and were not in the brief: check sh_y ≤ 2 (7 is not a multiple of 3), R_O ≠ ∅, and the
   t_y = 6, 7 cases.
4. Corollary 2.10 applies Prop. 2.7(1) to both ports of a shared vertex.
5. F1 and F2 enter only Theorems 3.1 to 3.3.

## 0.1 Setting, notation, and tools

**Graphs.** All graphs are finite and bipartite, and simple unless called multigraphs. A
*quartic subgraph* of G is a nonempty edge set F ⊆ E(G) in which every vertex has degree 0 or 4;
G is *quartic-free* if it has none. For a vertex set Z of a graph G with Δ(G) ≤ 6, the
*deficiency* is D_Z = Σ_{v∈Z} (6 − deg_G v).

**Classes** (quartic REPORT.md lines 238-241, with sides renamed).
- C_j(s), s ≥ 1: simple bipartite, sides U with |U| = s and W with |W| = s + 1, Δ ≤ 6, D_U ≤ j.
  The size is s. C0: every U-vertex has degree 6. C1: D_U ≤ 1.
- E_d(s), s ≥ 1: simple bipartite, both sides of size s, Δ ≤ 6, deficiency at most d on each side
  (the two deficiencies are equal, both are 6s − e).
- A G110 gadget is a C0 instance in which W has exactly six vertices of degree 5 (the ports) and all
  other W-vertices have degree 6. These are exactly the graphs B − o, B simple bipartite 6-regular
  (PAPER.md lines 27-31).

Sizes. A C0 instance has s ≥ 5: a U-vertex has 6 neighbors in W, so s + 1 ≥ 6. An E3 instance has
s ≥ 6: if s ≤ 5, every vertex has degree at most s, so a side has deficiency at least
s(6 − s) ≥ 5 > 3. The object with s = 0 (a single W-vertex, no edges) is not a C0 instance. It is
quartic-free, which is why the E3 step below must produce a piece of positive size.

**Notation for a C0 instance Γ.** Write I for the saturated side (size m) and O for the other side
(size m + 1). Then e(Γ) = 6m and D_O = 6. For S ⊆ V(Γ) put S_I = S ∩ I, S_O = S ∩ O and

- k(S) = |S_O| − |S_I| (additive over disjoint sets),
- ε(S) = e_Γ(S_I, O − S), the edges leaving S at its I-part,
- λ(S) = e_Γ(S_O, I − S), the edges leaving S at its O-part,
- D(S_O) = deficiency of S_O in Γ; for a gadget with port set P this is p(S) = |S_O ∩ P|,
- Φ(S) = λ(S) − 4k(S), the *slack* of S,
- Q_S = Γ[V(Γ) − S].

**Identity (0.1).** λ(S) = 6k(S) − D(S_O) + ε(S), hence Φ(S) = 2k(S) − D(S_O) + ε(S).

*Proof.* Summing degrees over S_O: 6|S_O| − D(S_O) = e(S_O, S_I) + λ(S). Over S_I (all degree 6):
6|S_I| = e(S_O, S_I) + ε(S). Subtract. ∎

For a gadget, Φ = 2k − p + ε is PAPER.md eq. (1) (line 75), there for S ⊆ V(Γ) − y.

**Identity (0.2).** e(Q_S) = 6|I − S| − λ(S). *Proof.* The 6|I − S| edge ends at I − S lie in Q_S
or go to S_O, and the latter are counted by λ(S). ∎

**Lemma 0.1 (flow criterion).** Let G be bipartite with sides P, Q of equal size s ≥ 1. G has a
spanning 4-regular subgraph iff e(A, Q − C) ≥ 4(|A| − |C|) for all A ⊆ P, C ⊆ Q. If Δ(G) ≤ 6, then
e(A, Q − C) = 6k − D_A + ε with k = |A| − |C| and ε = D_C + e(P − A, C) (deficiencies in G), so the
slack e(A, Q − C) − 4k equals 2k − D_A + ε. A violation has k ≥ 1, because the slack is at least −4k.

*Proof.* Network s → p (capacity 4), p → q (capacity 1 per edge), q → t (capacity 4). An integral
flow of value 4s is a spanning 4-regular subgraph. The cut with source side {s} ∪ A ∪ C has
capacity 4|P − A| + e(A, Q − C) + 4|C| = 4s + (e(A, Q − C) − 4k), and every cut has this form. The
degree identity is (0.1) in this notation. This is the reviewed criterion (quartic REPORT.md lines
243-246, QUARTIC-REVIEW.md lines 187-201). ∎

*Use for a C0 instance.* For y ∈ O, H_y = Γ − y is balanced with sides O − y and I of size m. A cut
of H_y is (A, C) = (S_O, S_I) for S ⊆ V(Γ) − y, and e_{H_y}(S_O, I − S) = λ(S) because y ∉ S_O. So
the slack of this cut is Φ(S). In particular **Φ(S) does not depend on y: it is the slack of S in
H_y for every y ∈ O − S.** In the lemma's notation, ε = D_C(H_y) + e(O − y − A, C) = e(y, C) +
e(O − y − A, C) = ε(S), because I-vertices have degree 6 in Γ.

**Lemma 0.2 (zero-sum threshold, multigraph form).** Let M be a loopless bipartite multigraph with
n ≥ 1 vertices and at least 3n − 2 edges. Then some nonempty set F of edges (parallel edges are
distinct elements) has every F-degree divisible by 4. If Δ(M) ≤ 7, every F-degree is 0 or 4.

*Proof.* This is Olson's group-ring argument in the form of PAPER.md lines 33-49, reviewed in
G110-REVIEW.md lines 100-114, written out for a list with repeats. Let V = V(M) with sides U, W,
fix v0 ∈ V, and let K ⊆ (Z/4)^V be the coordinate-sum-zero subgroup. The vectors b_v = e_v − e_{v0}
(v ≠ v0) form a basis, so K ≅ (Z/4)^r with r = n − 1. To an edge f = uw (u ∈ U, w ∈ W) assign
g_f = e_u − e_w ∈ K. In F2[K] put t_v = X^{b_v} + 1. Then t_v^4 = X^{4b_v} + 1 = 0, and
F2[K] = F2[t_v : v ≠ v0]/(t_v^4). For g = Σ a_v b_v, X^g + 1 = Π(1 + t_v)^{a_v} + 1 has zero
constant term. A product of 3r + 1 polynomials with zero constant term has only monomials of degree
at least 3r + 1, and each of these has some exponent at least 4, so the product is 0. Take any
L = 3n − 2 = 3r + 1 edges f_1, ..., f_L (a list; parallel edges appear separately). Then

    0 = Π_j (1 + X^{g_{f_j}}) = Σ_{T ⊆ {1..L}} X^{Σ_{j∈T} g_{f_j}}.

The coefficient of X^0 is the number of T with Σ_{j∈T} g_{f_j} = 0, modulo 2. T = ∅ is one, so
some nonempty T has zero sum. Its v-coordinate is +deg_T(v) for v ∈ U and −deg_T(v) for v ∈ W, so
every T-degree is divisible by 4. If Δ ≤ 7, these degrees are 0 or 4. ∎

**Lemma 0.3 (degeneracy bound; FINDINGS.md Corollary C, line 958, stated there without proof).**
A simple bipartite graph on n ≥ 6 vertices in which every nonempty subgraph has a vertex of degree
at most 3 has at most 3n − 9 edges.

*Proof.* Repeatedly delete a vertex of degree at most 3 and list the vertices in reverse order of
deletion as v_1, ..., v_n. Then v_j has at most 3 neighbors among v_1, ..., v_{j−1}. A bipartite
graph on six vertices has at most 9 edges (ab ≤ 9 when a + b = 6). So
e ≤ 9 + 3(n − 6) = 3n − 9. ∎

**Lemma 0.4 (4-cores).** Deleting a vertex of degree d ≤ 3 changes e − 3n by 3 − d ≥ 0. Let G be
simple bipartite with Δ ≤ 6, n ≥ 6 and e ≥ 3n − 8. Then its 4-core G' (what remains after
repeatedly deleting vertices of degree at most 3) is nonempty, has δ(G') ≥ 4, Δ(G') ≤ 6 and
e(G') − 3|G'| ≥ e(G) − 3n, and it is quartic-free if G is.

*Proof.* The first sentence is arithmetic. If G' were empty, every nonempty subgraph of G would have
a vertex of degree at most 3, and Lemma 0.3 would give e ≤ 3n − 9. ∎

**Lemma 0.5 (E3 reduction, reviewed; trivial pieces made explicit).** Let G ∈ E3(s) with sides P, Q
and no spanning 4-regular subgraph. Then there are A ⊆ P, C ⊆ Q with |A| = |C| + 1, ε = 0 and
D_A = 3, and both G[A ∪ C] and G[(P − A) ∪ (Q − C)] are C0 instances or single vertices: G[A ∪ C]
has saturated smaller side C (size |C|), G[(P − A) ∪ (Q − C)] has saturated smaller side P − A (size
s − 1 − |C|). The two sizes sum to s − 1 ≥ 5, so at least one piece is a C0 instance of positive
size, smaller than s.

*Proof.* Lemma 0.1 gives a violation with k ≥ 1 and D_A ≥ 2k + 1 + ε. As D_A ≤ D_P ≤ 3: k = 1,
ε = 0, D_A = D_P = 3. ε = 0 means D_C = 0 and e(P − A, C) = 0, so every C-vertex has 6 neighbors,
all in A. D_{P−A} = D_P − D_A = 0 and e(P − A, C) = 0, so every (P − A)-vertex has 6 neighbors, all
in Q − C. Sizes: |A| = |C| + 1 and |Q − C| = s − |C| = |P − A| + 1. A piece whose smaller side is
empty is a single vertex. Both cannot be single vertices, since s ≥ 6 (§0.1). This is REPORT.md
lines 252-254 and QUARTIC-REVIEW.md lines 208-210. ∎

**Corollary 0.6.** If every C0 instance of size 1, ..., s − 1 has a quartic subgraph, so does every
E3(s) instance. *Proof.* A spanning 4-regular subgraph is a quartic subgraph (s ≥ 1). Otherwise
Lemma 0.5 gives a C0 piece of size between 1 and s − 1, and its quartic subgraph is one of G. ∎

## 1. G-1, the small-cut lemma

Setting: B is simple bipartite 6-regular, oy ∈ E(B), Γ = B − o with sides I (the side of o, minus
o, size m) and O (the side of y, size m + 1), P = N_B(o) the six ports, H = B − o − y = Γ − y. So
|V(B)| = 2m + 2 and B's sides are I ∪ {o} and O.

**Lemma 1.1 (G-1).** Suppose H has no spanning 4-regular subgraph. Then H has a cut (A, C),
A ⊆ O − y, C ⊆ I, with Φ < 0, and every such cut satisfies, with k = |A| − |C|, p = |A ∩ P|,
ε = e_Γ(C, O − A), c = |C|, X = A ∪ C, Y = V(B) − X, t = |I − C| = m − c:

1. (k, p, ε) is (1, p, ε) with 3 + ε ≤ p ≤ 5, or (2, 5, 0) (PAPER.md lines 81-84; no
   quartic-freeness is assumed);
2. ∂_B(X) = 6k + 2ε, which is 6, 8 or 10 when k = 1 (ε = 0, 1, 2) and 12 when k = 2;
3. c ≥ 5 and |X| = 2c + 1 ≥ 11 when k = 1; c ≥ 4 and |X| = 2c + 2 ≥ 10 when k = 2;
4. t ≥ 6 in both cases; |Y| = 2t + 1 ≥ 13 when k = 1, and |Y| = 2t ≥ 12 when k = 2.

In particular |V(B)| = |X| + |Y| ≥ 22, and ≥ 24 when k = 1.

*Proof.* Lemma 0.1 gives a cut with Φ = 2k − p + ε < 0, and k ≥ 1.

1. Φ ≤ −1 means p ≥ 2k + 1 + ε. Since A ⊆ O − y contains at most 5 ports, p ≤ 5. So k ≤ 2; k = 1
   needs 3 + ε ≤ p ≤ 5 (so ε ≤ 2); k = 2 needs p ≥ 5 + ε, so p = 5, ε = 0.
2. Edges of B with exactly one end in X: from C (C ⊆ I has all its B-neighbors in O) to O − A,
   ε of them; from A to I − C, e_Γ(A, I − C) = λ(X) = 6k − p + ε by (0.1); from A to o, p of them
   (o ∉ X). Total 6k + 2ε.
3. If c = 0 then |A| = k ≤ 2 < 3 ≤ p ≤ |A|, impossible. So c ≥ 1. All 6c edge ends at C go to A
   except the ε that go to O − A, so e(A, C) = 6c − ε. B is simple, so e(A, C) ≤ |A||C| = (c + k)c,
   that is c² + (k − 6)c + ε ≥ 0. For k = 1 and c = 1, 2, 3, 4, c² − 5c is −4, −6, −6, −4, so
   c² − 5c + ε ≤ −2 < 0 (ε ≤ 2); hence c ≥ 5. For k = 2, ε = 0: c(c − 4) ≥ 0 with c ≥ 1 gives c ≥ 4.
   |X| = |A| + |C| = 2c + k.
4. Q = Γ[(I − C) ∪ (O − A)] = B[Y − o]. Note y ∈ O − A. The O − A side has Q-deficiency
   (6 − p) + ε: its 6 − p ports have degree 5 in Γ, and ε edges go to C.
   - k = 1: |O − A| = m + 1 − (c + 1) = t = |I − C|, and t ≥ 1 because y ∈ O − A. Both sides of Q
     have deficiency 6 − p + ε ≤ 3. Every Q-degree is at most t (Q is simple with sides of size
     t), so if t ≤ 5 the I − C side has deficiency at least t(6 − t) ≥ 5 > 3. Hence t ≥ 6 and
     |Y| = |I − C| + |O − A| + |{o}| = 2t + 1 ≥ 13.
   - k = 2: |O − A| = t − 1 and the O − A side has deficiency 6 − 5 + 0 = 1, all at y. Since
     ε = 0, y has its 5 neighbors in I − C, and every other vertex of O − A is a non-port with its
     6 neighbors in I − C. If O − A = {y}, then t = 2 < 5, impossible. Otherwise some vertex of
     O − A − y has 6 neighbors in I − C, so t ≥ 6, and |Y| = t + (t − 1) + 1 = 2t ≥ 12. ∎

The lead's sketch for the Y side, "o has only 6 − p ≤ 3 − ε neighbors outside A (or 1 when
k = 2), which forces |O − A| ≥ 6 or 5", agrees with item 4: |O − A| = t ≥ 6 when k = 1 and
|O − A| = t − 1 ≥ 5 when k = 2. The proof above uses the deficiency count instead.

**Corollary 1.2.** Suppose B has no vertex set X ⊆ V(B) with ∂_B(X) ≤ 12, |X| ≥ 10 and
|V(B) − X| ≥ 12. Then for every edge oy, B − o − y has a spanning 4-regular subgraph, which is a
quartic subgraph of B − o (it has 2m ≥ 10 vertices). So every B − o has a quartic subgraph. The
lead's hypothesis, "every edge cut of B with at most 12 edges has a side with at most 9 vertices",
implies this one.

*Wording note on "covers every B on at most 20 vertices".* True, but through the sizes in Lemma 1.1:
X ∪ Y = V(B) and |X| + |Y| ≥ 22, so for |V(B)| ≤ 20 (|V(B)| is even) no cut of Lemma 1.1 exists
and every B − o − y has a spanning 4-regular subgraph. The literal "side ≤ 9" hypothesis can fail at
20 vertices: take two copies (L1, R1), (L2, R2) of K5,5 and add a perfect matching between L1 and
R2 and one between L2 and R1.
This B is simple bipartite 6-regular, and X = L1 ∪ R1 has ∂_B(X) = 10 with both sides of size 10
(checked in Appendix A, check G1-c). At 22 vertices only k = 2 with |X| = 10, |Y| = 12 remains.

## 2. Structure of a minimal C0 counterexample

Suppose some C0 instance is quartic-free. Let m be the least size s ≥ 1 of a quartic-free C0
instance and Γ one of them, with sides I (size m) and O (size m + 1). Then m ≥ 5, and:

**(M)** every C0 instance of size 1, ..., m − 1 has a quartic subgraph; so, by Corollary 0.6,
every E3(s) instance with 1 ≤ s ≤ m has a quartic subgraph.

Since Γ is quartic-free, so is every subgraph of Γ.

### 2.1 Claims (1a) and (1b)

**Lemma 2.1 (cut analysis at a deleted O-vertex).** Let Γ be any C0(m) instance, y0 ∈ O of degree
d0 ≤ 5, and S ⊆ V(Γ) − y0 with Φ(S) ≤ −1. Put c = |S_I|, t = m − c, k = k(S). Then:

1. 1 ≤ k and 2k ≤ d0 − 1, and |O − S| = t + 1 − k ≥ 1;
2. if every O-vertex has degree at least 4, then c ≥ 1;
3. if k = 1, Q_S is an E3(t) instance (balanced, t ≥ 1, deficiency at most 3 per side);
4. if k = 2 (which forces d0 = 5): Φ(S) = −1, λ(S) = 7, ε(S) = 0, y0 has all its neighbors in
   I − S, every other vertex of O − S has degree 6 and all its neighbors in I − S, and
   D(S_O) = 5. So Q_S is a C1 instance of size t − 1: smaller side O − S, whose only deficient
   vertex is y0 (deficiency 1), larger side I − S with deficiency 7.

*Proof.* (1) Φ ≥ −4k (λ ≥ 0), so k ≥ 1. By (0.2), e(Q_S) = 6t − λ(S) = 6t − 4k − Φ(S) ≥ 6t − 4k + 1.
Counting from O − S, which has t + 1 − k vertices including y0:
e(Q_S) ≤ Σ_{v∈O−S} deg_Γ v ≤ 6(t + 1 − k) − (6 − d0). So 6t − 4k + 1 ≤ 6t − 6k + d0, that is,
2k ≤ d0 − 1. (2) If c = 0, then S = S_O has k vertices and all their edges go to I = I − S, so
λ(S) = Σ_{v∈S_O} deg v ≥ 4k, and Φ(S) ≥ 0. (3) For k = 1 both sides of Q_S have t vertices, t ≥ 1 by
(1), and e(Q_S) ≥ 6t − 3. (4) For k = 2, d0 = 5 and
6t − 7 ≤ 6t − 8 − Φ(S) = e(Q_S) ≤ Σ_{v∈O−S} deg_{Q_S} v ≤ Σ_{v∈O−S} deg_Γ v ≤ 6(t − 1) − 1 = 6t − 7,
so all are equalities: Φ(S) = −1 and λ(S) = 7; deg_{Q_S} v = deg_Γ v on O − S, so no edge joins O − S
to S_I, which is ε(S) = 0; and D(O − S) = 1, carried by y0, so D(S_O) = D_O − 1 = 5. The I − S
side of Q_S has deficiency 6t − e(Q_S) = λ(S) = 7. ∎

**Proposition 2.2 (claim 1a).** In the minimal counterexample, every O-vertex has degree 5 or 6, and
exactly six have degree 5. So Γ is a G110 gadget and B = Γ + o (o joined to the six) is simple
bipartite 6-regular.

*Proof.* Let y0 ∈ O have minimum degree d0. As Σ_O deg = 6m < 6(m + 1), d0 ≤ 5. Γ − y0 is balanced
(both sides of size m) with deficiency d0 on each side: D_{O−y0} = 6 − (6 − d0) and each of the d0
I-neighbors of y0 loses one.
- d0 ≤ 3: Γ − y0 ∈ E3(m) has a quartic subgraph by (M).
- d0 = 4: Γ − y0 has no spanning 4-regular subgraph (it would be a quartic subgraph of Γ), so
  Lemma 0.1 gives S ⊆ V(Γ) − y0 with Φ(S) ≤ −1. Lemma 2.1(1) gives 2k ≤ 3, so k = 1. Every O-vertex
  has degree ≥ d0 = 4, so c ≥ 1 by 2.1(2), and Q_S ∈ E3(m − c) with m − c ≤ m − 1 (the task's
  "smaller E3 piece"; it is indeed smaller). Q_S has a quartic subgraph by (M).
Both contradict quartic-freeness. So d0 = 5, every O-vertex has deficiency at most 1, and D_O = 6. ∎

**Proposition 2.3 (claim 1b).** Let y be a port. Then H_y = Γ − y has no spanning 4-regular
subgraph, and every S ⊆ V(Γ) − y with Φ(S) < 0 has (k, p, ε) = (2, 5, 0) and Φ(S) = −1. Write
A = S_O, C = S_I, c = |C|, t = m − c, X = A ∪ C, Q = Q_S, T = E_Γ(A, I − C). Then:
|A| = c + 2; c ≥ 4; every C-vertex has all 6 neighbors in A; A ⊇ P − y; |T| = 7; and Q is a C1
instance of size t − 1, with smaller side O − A whose only deficient vertex is y (deficiency 1)
and larger side I − C with deficiency 7.

*Proof.* A spanning 4-regular subgraph of H_y would be a quartic subgraph of Γ. Apply Lemma 2.1
with y0 = y, d0 = 5: k ∈ {1, 2}. If k = 1, Q_S ∈ E3(t), with t ≤ m − 1 because c ≥ 1 (Lemma 2.1(2);
all O-degrees are at least 5), so Q_S has a quartic subgraph by (M), a contradiction. So k = 2 and
Lemma 2.1(4) applies: Φ = −1, ε = 0, |T| = λ(S) = 7, and D(S_O) = 5 means A contains five ports,
which must be P − y. c ≥ 1, and a C-vertex has its 6 neighbors in A (ε = 0), so c + 2 = |A| ≥ 6. ∎

Remark. Under quartic-freeness alone, PAPER.md (lines 86-106) leaves four types (1,3,0), (1,4,1),
(1,5,2), (2,5,0). The k = 1 types leave Q balanced with deficiency exactly 3 per side, an E3
instance, and minimality removes them. Lemma 2.1 shows this without the zero-sum step of PAPER.md.

### 2.2 Claim (1c): cross-port transfer

**Proposition 2.4.** For any S ⊆ V(Γ) and port y' ∈ S_O:
Φ(S − y') = Φ(S) − 1 + e(S_I, y'). In particular, if X_y = A_y ∪ C_y is a negative cut of H_y and
y' ≠ y is a port (so y' ∈ A_y), then S' = (A_y − y') ∪ C_y is a cut of H_{y'} with
(k, p, ε) = (1, 4, e(C_y, y')) and Φ(S') = e(C_y, y') − 2. Hence e(y', C_y) ≥ 2.

*Proof.* Removing y' from S_O lowers k and p by one and adds the edges from S_I to y' to ε. So
Φ changes by −2 + 1 + e(S_I, y'). For X_y, Φ = −1 (Prop. 2.3), giving e(C_y, y') − 2. S' avoids
y', so it is a cut of H_{y'} with k = 1, and Prop. 2.3 for y' says it is not negative:
e(C_y, y') ≥ 2. The two excluded cases: e = 0 gives Φ(S') = −2, below the minimum slack −1 and a
negative k = 1 cut; e = 1 gives Φ(S') = −1 with type (1, 4, 1), which Prop. 2.3 excludes. ∎

§2.5 improves this to e(y', C_y) ≥ 4 (Corollary 2.11).

### 2.3 Claims (2) and (3): traces and contraction

Fix a port y and the data of Proposition 2.3. For τ ⊆ T and v ∈ V(Γ), τ(v) is the number of edges
of τ at v.

**Definition.** Γ[X] *realizes* τ if there is F ⊆ E(Γ[X]) with deg_F(v) + τ(v) ∈ {0, 4} for every
v ∈ X. Q realizes τ if there is F ⊆ E(Q) with deg_F(v) + τ(v) ∈ {0, 4} for every v ∈ V(Q).
R_X and R_Q denote the sets of 4-subsets τ ⊆ T realized by Γ[X] and by Q. There are C(7,4) = 35
four-subsets.

**Lemma 2.5 (claim 2, traces).**
1. Every edge of Γ lies in exactly one of E(Γ[X]), T, E(Q).
2. For a quartic subgraph H of Γ, x = |H ∩ T| = 4(|V(H) ∩ A| − |V(H) ∩ C|), so x ∈ {0, 4}.
3. Γ has a quartic subgraph iff Γ[X] has one, or Q has one, or R_X ∩ R_Q ≠ ∅.

*Proof.* (1) Edges join I = C ⊔ (I − C) to O = A ⊔ (O − A). None joins C to O − A (ε = 0); the
other three blocks are E(Γ[X]), T and E(Q). (2) All neighbors of a C-vertex are in A. Counting H-edge
ends: at A, 4|V(H) ∩ A| = e_H(A, C) + x; at C, 4|V(H) ∩ C| = e_H(A, C). Subtract. As 0 ≤ x ≤ 7 and
4 | x, x ∈ {0, 4}. (3) If τ ∈ R_X ∩ R_Q via F_X and F_Q, then F_X ∪ τ ∪ F_Q has all degrees in
{0, 4} and is nonempty. Conversely let H be quartic. If x = 0, H ∩ E(Γ[X]) and H ∩ E(Q) have all
degrees in {0, 4} (a vertex of X sees only E(Γ[X]) and T; a vertex of Q sees only E(Q) and T), and
one of them is nonempty. If x = 4, τ = H ∩ T is realized by H ∩ E(Γ[X]) and by H ∩ E(Q). ∎

**Proposition 2.6 (claim 3, contraction).**
1. X + β: add a vertex β to the I side and, for each f = ai ∈ T (a ∈ A), an edge aβ labeled f.
   This is a bipartite multigraph with 2c + 3 vertices, 6c + 7 = 3(2c + 3) − 2 edges and maximum
   degree 7 (β has degree 7; an A-vertex keeps its Γ-degree; C-vertices have degree 6). By
   Lemma 0.2 it has a nonempty F with all degrees in {0, 4}. Since Γ[X] is quartic-free, F uses β,
   so deg_F(β) = 4. With τ the labels of F's four β-edges, F minus those edges realizes τ in Γ[X].
   So R_X ≠ ∅.
2. Q + α: add a vertex α to the O side and an edge iα for each f = ai ∈ T. It has 2t vertices
   and e(Q) + 7 = (6t − 7) + 7 = 6t = 3(2t) edges, two more than the threshold. For any two
   g, h ∈ T, (Q + α) minus the α-edges of g and h has 3(2t) − 2 edges and maximum degree at most 7,
   so Lemma 0.2 gives F with degrees in {0, 4}; F uses α because Q is quartic-free, and Q
   realizes the 4-set of labels of F's α-edges, a subset of T − {g, h}. **So R_Q meets every
   5-subset of T.**

*Proof.* Counts: e(Γ[X]) = 6c (every C-vertex has its 6 edges in Γ[X]) and |X| = 2c + 2;
e(Q) = 6t − 7 by (0.2) and |V(Q)| = t + (t − 1). The rest is in the statement. Lemma 0.2 applies to
multigraphs because the group-ring argument uses a list of group elements with repeats. ∎

### 2.4 Claim (4): distinct endpoints and the at-most-three rules

Write r(i) = |{f ∈ T : f ∋ i}| for i ∈ I − C and s(a) = |{f ∈ T : f ∋ a}| for a ∈ A. So
Σ r = Σ s = 7, and the Q-degree of i ∈ I − C is 6 − r(i).

**Proposition 2.7.**
1. r(i) ≤ 3 for every i ∈ I − C.
2. s(a) ≤ 3 for every a ∈ A.
3. If the four I − C endpoints of a 4-subset τ ⊆ T are distinct, then Q realizes τ.
4. Hence every τ ∈ R_X has a repeated I − C endpoint, and R_X ∩ R_Q = ∅ with R_X ≠ ∅.

*Proof.* (1) Suppose r(i) ≥ 4. Q − i has sides O − A and I − C − i, both of size t − 1 ≥ 1
(y ∈ O − A). Deficiencies: the I side keeps the other 7 − r(i) units; the O side has y's unit plus
one for each of the 6 − r(i) Q-neighbors of i, total 7 − r(i). Both are at most 3, so
Q − i ∈ E3(t − 1) with t − 1 < m, and (M) gives a quartic subgraph. (2) Suppose s(a) ≥ 4. Then
Q + a = Γ[(I − C) ∪ (O − A) ∪ {a}] has sides of size t, and a has degree s(a) in it. O side
deficiency: 1 + (6 − s(a)) = 7 − s(a); I side: 7 − s(a). So Q + a ∈ E3(t), t ≤ m − 4, and (M)
applies. (3) Q + α_τ: add α to the O side, joined to the four distinct endpoints. It is simple,
both sides have size t, and Δ ≤ 6 (an endpoint i had Q-degree 6 − r(i) ≤ 5). Deficiencies: O side
1 + (6 − 4) = 3; I side 7 − 4 = 3. So Q + α_τ ∈ E3(t), t < m, and (M) gives a quartic F. Q is
quartic-free, so F uses α with degree 4, that is, all four α-edges, and F minus them realizes τ in
Q. (4) A distinct-endpoint τ ∈ R_X would lie in R_Q by (3), and Lemma 2.5(3) would give a quartic
subgraph of Γ. R_X ≠ ∅ is Prop. 2.6(1). ∎

### 2.5 (U): six-port uncrossing

For each port y fix one negative cut X_y = A_y ∪ C_y of H_y (type (2,5,0) by Prop. 2.3). Call
Q_y = V(Γ) − X_y the *petal* of y, and write O_y = Q_y ∩ O = O − A_y, I_y = Q_y ∩ I = I − C_y,
t_y = |I_y|, T_y = E(A_y, I_y) (the seven petal edges). So |O_y| = t_y − 1, y ∈ O_y, and
N(O_y) ⊆ I_y (ε(X_y) = 0). For U ⊆ V(Γ) use k_U = k(U), p_U = p(U), ε_U = ε(U) from §0.1.

**Lemma 2.8 (boundary identity and submodularity).** For every U ⊆ V(Γ) = V(B) − o,
∂_B(U) = 6k_U + 2ε_U. Consequently ε is submodular on subsets of V(Γ), k and p are modular, and Φ
is submodular.

*Proof.* B's sides are I ∪ {o} and O. Edges leaving U: from U_I to O − U, ε_U of them (U_I has no
neighbor o); from U_O to I − U, λ(U) = 6k_U − p_U + ε_U by (0.1); from U_O to o, p_U of them.
Total 6k_U + 2ε_U. The cut function ∂_B of a graph is submodular, k is modular, so
ε = (∂_B − 6k)/2 is submodular; p is modular; Φ = 2k − p + ε is submodular. ∎

**Theorem 2.9 (U).** For distinct ports y, y', X_y ∪ X_{y'} is V(Γ) or V(Γ) − {i} for one i ∈ I.
Equivalently, Q_y ∩ Q_{y'} is empty or one I-vertex; in particular O_y ∩ O_{y'} = ∅.

*Proof.* Put W = X_y ∪ X_{y'} and U = X_y ∩ X_{y'}.
1. Submodularity: ε_U + ε_W ≤ ε(X_y) + ε(X_{y'}) = 0, so ε_U = ε_W = 0. Modularity:
   k_U + k_W = 2 + 2 = 4. Ports: X_y ∩ P = P − y and X_{y'} ∩ P = P − y', so p_U = 4 and p_W = 6.
2. k_U ≥ 2: U ⊆ V(Γ) − y is a cut of H_y with Φ(U) = 2k_U − 4 + 0. The minimum slack of H_y is −1
   (Prop. 2.3), so 2k_U − 4 ≥ −1. (Prop. 2.3 even gives Φ(U) ≥ 0, since a negative cut has p = 5.)
   Hence k_W ≤ 2.
3. k_W ≥ 1: W contains all six ports, each adjacent to o ∉ W, so 6k_W = ∂_B(W) ≥ 6.
4. k_W = 1: every vertex of W_I has its 6 neighbors in W_O (ε_W = 0) and |W_O| = |W_I| + 1, so
   Γ[W] is a C0 instance of size |W_I| ≥ |C_y| ≥ 4, and it is quartic-free. By minimality
   |W_I| ≥ m, so W_I = I, |W_O| = m + 1 and W = V(Γ).
5. k_W = 2: let Z = V(Γ) − W = V(B) − (W ∪ {o}). Then ∂_B(Z) = ∂_B(W ∪ {o}) =
   ∂_B(W) + 6 − 2·6 = 12 + 6 − 12 = 6 (all six neighbors of o are in W), and
   k_Z = k(V(Γ)) − k_W = 1 − 2 = −1, so ε_Z = (6 − 6k_Z)/2 = 6. Z contains no port, so the edges
   leaving Z_O go to I − Z only; ∂_B(Z) = ε_Z + e(Z_O, I − Z) gives e(Z_O, I − Z) = 0. If Z_O ≠ ∅,
   Γ[Z] is a C0 instance with saturated smaller side Z_O, of size |Z_O| ≤ |O − P| = m − 5 < m, and
   it is quartic-free: this contradicts (M). So Z_O = ∅, |Z_I| = |Z_O| − k_Z = 1, and Z = {i},
   i ∈ I.
So W = V(Γ) or W = V(Γ) − {i}, and Q_y ∩ Q_{y'} = V(Γ) − W. ∎

(The lead's outline states "minimality, or simplicity when that side has size ≤ 4" in step 5;
minimality alone suffices, since (M) covers every size from 1 to m − 1, and sizes 1 to 4 have no
instances at all.)

**Corollary 2.10 (shared vertices).** Suppose Q_y ∩ Q_{y'} = {i}. Then i has exactly 3 neighbors in
O_y, exactly 3 in O_{y'}, and no others. So i has degree 3 in Q_y and in Q_{y'}, and lies in
neither petal's 4-core. No vertex lies in three petals.

*Proof.* i ∈ I_y receives at most 3 edges of T_y (Prop. 2.7(1) for y), and its other edges go to
O_y; so i has at least 3 neighbors in O_y. Likewise at least 3 in O_{y'}. O_y ∩ O_{y'} = ∅ and
deg i = 6, so exactly 3 + 3. Its Q_y-degree is then 3, so the 4-core peeling of Q_y deletes it
first; the same for Q_{y'}. A vertex in three petals would have at least 9 neighbors. ∎

**Corollary 2.11 (1c strengthened).** For distinct ports y, y', e(y', C_y) ≥ 4.

*Proof.* y' ∈ O_{y'} and N(O_{y'}) ⊆ I_{y'}, so y' has its 5 neighbors in I_{y'}. At most one of them
lies in I_y (Theorem 2.9), and the others lie in I − I_y = C_y. ∎

**Proposition 2.12 (hub count, M1).** Let R = V(Γ) − ∪_y Q_y (the hub), R_I = R ∩ I,
R_O = R ∩ O. Call a vertex lying in two petals *shared*; let sh_y be the number of shared vertices
in Q_y and ov the total number of shared vertices. Then:
1. every petal's outside edges in Γ are its seven T_y edges (in B, add the edge yo);
2. N(R_I) ⊆ R_O;
3. T_y consists of 3·sh_y edges from the shared vertices of I_y into other petals and 7 − 3·sh_y
   edges into R_O; hence sh_y ≤ 2 and every petal sends at least one edge to R_O;
4. |R_O| − |R_I| = 7 − ov and 0 ≤ ov ≤ 6; in particular R_O ≠ ∅.

*Proof.* (1) The outside edges of Q_y leave from I_y to A_y (that is T_y) or from O_y to C_y (none,
ε = 0). (2) If r ∈ R_I had a neighbor v ∈ O_y, then r ∈ N(O_y) ⊆ I_y, which is false.
(3) A_y = R_O ∪ ⋃_{y'≠y} O_{y'}. An edge from I_y to O_{y'} has its I-end in N(O_{y'}) ⊆ I_{y'},
so at a shared vertex of I_y ∩ I_{y'}, which has exactly 3 neighbors in O_{y'} and none in R_O
(Corollary 2.10). So 7 = 3·sh_y + e(I_y, R_O). As 7 is not a multiple of 3, sh_y ≤ 2 and
e(I_y, R_O) ≥ 1. (4) R_O consists of non-ports (every port lies in its petal), so each R_O-vertex
has 6 edges, all to R_I or to ⋃ I_y; no shared vertex has a neighbor in R_O. With (2) and (3):
6|R_O| = e(R_O, R_I) + Σ_y e(R_O, I_y) = 6|R_I| + Σ_y (7 − 3·sh_y) = 6|R_I| + 42 − 6·ov, using
Σ_y sh_y = 2·ov (Corollary 2.10: each shared vertex lies in exactly two petals). And
Σ_y sh_y ≤ 12 gives ov ≤ 6. Cross-check by counting vertices: the O_y are pairwise disjoint, so
m + 1 = |R_O| + Σ_y (t_y − 1); two petals share at most one vertex and no vertex lies in three, so
m = |R_I| + Σ_y t_y − ov; subtracting gives the same identity. ∎

## 3. Size bounds

F1(N) and F2(N) are census statements, used only as hypotheses:
- **F1(N):** every simple bipartite graph with δ ≥ 4, Δ ≤ 6, e ≥ 3n − 6 and n ≤ N has a quartic
  subgraph.
- **F2(N):** the same with e ≥ 3n − 4.

F1(N) implies F2(N). What they rest on (one program each):
- F1(14): the PRUNE-modified geng run `geng_q4 -b -d4 -D6 n 3n-12:3n` for n ≤ 14 (quartic
  REPORT.md lines 269-274). It lists every bipartite graph with δ ≥ 4, Δ ≤ 6 and no 4-regular
  subgraph with e ≥ 3n − 12, and finds e ≤ 3n − 8 for n ≤ 14. Not re-run by the review (STATE.md
  line 18).
- F2(18): the Fable W1 census, `geng ... | pairc f`: all graphs with δ ≥ 4, Δ ≤ 6, e ≥ 3n − 4 for
  n ≤ 12 (CHECKPOINT-01.md line 17; command lines in `reports/585-fable/tools/README.md` lines 31-34),
  and bipartite graphs `geng -q -b -d4 -D6 n 3n-4:3n | ./pairc f` for n = 13..18 (README lines
  35-36; counts 12, 206, 588, 31,335, 196,531 in CHECKPOINT-02.md line 12 and the
  `data/bip-n1{3..7}-level-4.err` logs; 18,153,661 at n = 18 in CHECKPOINT-05.md lines 28-33 and
  `data/bip-n18-part*.err`). Every graph had a pair, and a pair is a quartic subgraph. It rests on
  geng's completeness and on pairc's positive answers; the README says a positive answer is a
  witness that can be replayed, not that all were replayed.

### 3.1 Warm-up: one port

**Theorem 3.1.** Under F1(N1) and F2(N2), a minimal C0 counterexample has 2m + 1 ≥ N1 + N2 + 2.
So C0 holds for every m ≤ ⌈(N1 + N2 + 1)/2⌉ − 1. With N1 = 14, N2 = 18: C0 for m ≤ 16.

*Proof.* Fix a port y. Γ[X_y] has |X_y| = 2c + 2 ≥ 10 vertices and 6c = 3|X_y| − 6 edges. Q_y has
2t − 1 ≥ 11 vertices (t ≥ 6 by Lemma 1.1(4)) and 6t − 7 = 3|Q_y| − 4 edges. Both are quartic-free,
simple bipartite with Δ ≤ 6 and at least 6 vertices, so by Lemma 0.4 their 4-cores are nonempty, with
δ ≥ 4, Δ ≤ 6, and e − 3n ≥ −6 and ≥ −4 respectively. F1(N1) and F2(N2) then give
|core Γ[X_y]| ≥ N1 + 1 and |core Q_y| ≥ N2 + 1. X_y and Q_y partition V(Γ), so
2m + 1 ≥ N1 + N2 + 2. With 14 and 18, 2m + 1 ≥ 34, and since 2m + 1 is odd, m ≥ 17. ∎

### 3.2 Main bound: six disjoint petal cores

**Theorem 3.2.** Under F2(N2), a minimal C0 counterexample has 2m + 1 ≥ 6(N2 + 1). So C0 holds for
every m ≤ 3N2 + 2. With N2 = 18: **C0 for m ≤ 56**, hence G110-quartic for every simple bipartite
6-regular B on at most 114 vertices. F1 is not used.

*Proof.* The six petal cores are pairwise disjoint: core(Q_y) ∩ core(Q_{y'}) ⊆ Q_y ∩ Q_{y'}, which is
empty or a vertex lying in neither core (Theorem 2.9, Corollary 2.10). Each has at least N2 + 1
vertices (as in Theorem 3.1). So 2m + 1 ≥ 6(N2 + 1), m ≥ 3N2 + 5/2, and m ≥ 3N2 + 3. ∎

### 3.3 Refinement with the hub (M1)

**Theorem 3.3.** Under F2(N2), a minimal C0 counterexample has 2m + 1 ≥ 6(N2 + 1) + 7. So C0 holds
for every m ≤ 3N2 + 5; with N2 = 18, **C0 for m ≤ 59** (B on at most 120 vertices).

*Proof.* The vertices outside all six petal cores include R (disjoint from every petal) and the ov
shared vertices (inside petals but in no core, Corollary 2.10). |R| ≥ |R_O| = |R_I| + 7 − ov ≥ 7 − ov
(Prop. 2.12). So 2m + 1 ≥ 6(N2 + 1) + (7 − ov) + ov, that is, m ≥ 3N2 + 6. ∎

### 3.4 An unconditional bound (M1)

**Lemma 3.4.** In a minimal counterexample, every petal has t_y ≥ 8, so |O_y| ≥ 7.

*Proof.* O_y = {y} ∪ U_y, where U_y = O_y − y consists of |O_y| − 1 = t_y − 2 non-ports, each with
all 6 neighbors in I_y, and y has its 5 neighbors in I_y. If U_y = ∅ then t_y = 2 < 5, impossible;
so t_y ≥ 6. If t_y = 6, any four vertices of U_y and any four of I_y span K4,4, a quartic subgraph.
If t_y = 7, each u ∈ U_y (five vertices) misses exactly one vertex μ(u) of I_y. If μ is injective,
U_y and μ(U_y) span K5,5 minus a perfect matching, which is 4-regular. If μ(u1) = μ(u2) for some
u1 ≠ u2, take four vertices of U_y including u1, u2: they miss at most three vertices of I_y, so
they have at least four common neighbors, and K4,4 appears. Both contradict quartic-freeness. ∎

**Theorem 3.5.** A minimal C0 counterexample has m ≥ 42. So **every C0 instance with m ≤ 41 has a
quartic subgraph**, and G110-quartic holds for every simple bipartite 6-regular graph on at most
84 vertices. No census is used.

*Proof.* The six sets O_y are pairwise disjoint subsets of O (Theorem 2.9), each of size at least 7
(Lemma 3.4), and R_O is nonempty and disjoint from all of them (Prop. 2.12(4)). So
m + 1 ≥ 42 + 1. ∎

(Without Prop. 2.12 the same argument gives m + 1 ≥ 42, that is, C0 for m ≤ 40.)

## 4. The residual, stated exactly

### 4.1 Per port

For a minimal counterexample and each port y (data of Prop. 2.3), all of the following hold:
1. R_X(y) ≠ ∅, and every τ ∈ R_X(y) has a repeated I_y endpoint (Prop. 2.6(1), 2.7(4));
2. R_Q(y) contains every 4-subset of T_y with four distinct I_y endpoints (Prop. 2.7(3)), and meets
   every 5-subset of T_y (Prop. 2.6(2));
3. R_X(y) ∩ R_Q(y) = ∅, and Γ[X_y], Q_y are quartic-free (Lemma 2.5(3); this is equivalent to Γ
   being quartic-free);
4. every vertex receives or sends at most 3 of the seven T_y edges (Prop. 2.7(1),(2)).

Since every I_y endpoint receives at most 3 of the 7 edges, at least three distinct I_y vertices
meet T_y. If exactly three do (receipt profile 3,3,1 or 3,2,2), every 4-subset has a repeated
endpoint and item 2's first clause is empty.

### 4.2 Cross-port facts

From §2.5: for distinct ports y, y', A_y ∪ A_{y'} = O and |I − (C_y ∪ C_{y'})| ≤ 1; the O_y are
pairwise disjoint and each contains exactly one port, its own; two petals share at most one vertex,
an I-vertex with exactly 3 neighbors in each of the two petal O sides; no vertex lies in three
petals; a petal contains at most two shared vertices and sends 7 − 3·sh_y ≥ 1 edges into the
hub; e(y', C_y) ≥ 4; the hub R has N(R_I) ⊆ R_O and |R_O| − |R_I| = 7 − ov with ov ≤ 6. In the
uncrossing, X_y ∩ X_{y'} has ε = 0 and either (k, Φ) = (3, 2) (when X_y ∪ X_{y'} = V(Γ)) or
(k, Φ) = (2, 0) (when the union is V(Γ) − i), so the submodular inequality is tight.

So the minimal counterexample is a hub R with six petals hanging from it: petal Q_y is a quartic-free
C1 instance with e = 3|Q_y| − 4, joined to the rest of Γ only by its seven T_y edges (and to o by
the edge yo in B), and two petals can share a single I-vertex.

### 4.3 Remark: contracting petals (lead's request; arithmetic only)

Contracting a vertex set Z to one vertex changes e − 3n by −e(Γ[Z]) + 3|Z| − 3. For a petal this is
−(3|Q_y| − 4) + 3|Q_y| − 3 = +1. Γ has e − 3n = −3 and Lemma 0.2 needs ≥ −2.
- **Disjoint petals.** Contracting t pairwise disjoint petals to vertices q_y gives e − 3n = t − 3,
  that is t − 1 edges over the threshold. Each q_y joins the I side (all outside edges of Q_y leave
  from I_y) and has degree 7. So for t ≥ 1 Lemma 0.2 gives a nonempty F with all degrees in {0, 4}.
  F must use some q_y: avoiding all of them, it would lie in Γ minus the contracted petals, which is
  quartic-free. F lifts to a quartic subgraph of Γ exactly when each used petal realizes the 4-set
  F uses at q_y; that lifting step is the open part.
- **Shared vertices, option 1 (contract a cluster).** If petals share vertices, contract each
  cluster K (a connected component of the "share a vertex" relation on the six petals) to one vertex.
  Γ[∪_{y∈K} Q_y] has Σ_{y∈K} e(Q_y) edges (no edges join two petals except through the shared
  vertex, whose 3 + 3 edges already lie inside the two petals) and Σ|Q_y| − ov_K vertices. The
  change in e − 3n is 4|K| − 3ov_K − 3, so contracting all clusters gives e − 3n =
  21 − 3ov − 3(number of clusters) = 3 − 3·β1, where β1 = ov − 6 + (number of clusters) is the
  cycle rank of the sharing graph (six nodes, one edge per shared vertex). With no sharing, or
  any sharing forest, this is 3 (slack 5); each independent cycle of sharing costs 3. The cluster
  vertex has degree 7|K| − 6ov_K, which is 8 for two petals sharing one vertex. So Lemma 0.2 only
  gives degrees ≡ 0 (mod 4) there, and the degree 8 is not excluded.
- **Shared vertices, option 2 (contract Q_y minus its shared vertices).** Q_y − S_y (S_y its shared
  vertices) has e − 3n = −4 − 3|S_y| + 3|S_y| = −4, so each contraction still adds 1, and contracting
  all six gives e' = 3n' + 3 whatever ov is. But the contracted vertex now sees both sides (T_y
  edges from I_y − S_y, and 3 edges from O_y to each shared vertex), so the graph is not bipartite.
  Lemma 0.2's group-ring proof still applies to the vectors e_u − e_w (they lie in the sum-zero
  subgroup), and gives degree ≡ 0 (mod 4) at original vertices but only the signed congruence
  (T_y edges used) − (shared-vertex edges used) ≡ 0 (mod 4) at q_y.

### 4.4 Remark: the open C1 sub-case (counts only; not a claim)

Setting (QUARTIC-REVIEW.md lines 240-246, renamed): G ∈ C1(s) with sides U (size s, D_U = 1, u1
the degree-5 vertex) and W (size s + 1, D_W = 7); w0 ∈ W of minimum degree d0; a violation
(A ⊆ W − w0, C' ⊆ U) of G − w0 with |A| = |C'| + 2, D_A = 5 + ε, ε ∈ {0, 1}, u1 ∉ C'. P1 =
G[(U − C') ∪ (W − A)] (smaller side W − A, deficiency 2) and P2 = G[A ∪ C'] (C' side deficiency ε).
Here ε = e(C', W − A) because D_{C'} = 0 (u1 ∉ C').
- e(A, U − C') = 6·2 − D_A + ε = 7 (QUARTIC-REVIEW.md line 256).
- **P2 + β** (β on the U side, joined to the A-ends of those 7 edges) has 2|C'| + 3 vertices and
  (6|C'| − ε) + 7 edges, which is **3n − 2 − ε**. The lead's "P2 + β at 3n − 2" holds for ε = 0 and
  is **FALSE for ε = 1**, where P2 + β has 3n − 3 edges, one below Lemma 0.2. When ε = 1 the cut
  between P2 and P1 has 8 edges (the seven, plus one from C' to W − A), and the trace identity of
  Lemma 2.5(2) becomes x − x' = 4(|V(H) ∩ A| − |V(H) ∩ C'|) with x' ≤ 1 the number of trace edges
  at C'. See FLAW.md and check C1-s in Appendix A.
- **P1 + α_τ** (α on the W side, joined to the four distinct U − C' endpoints of a 4-subset τ) is
  simple and balanced with sides of size s − |C'|; W side deficiency 2 + (6 − 4) = 4; U side: U − C'
  has deficiency 1 + 7 = 8 in P1 (u1 plus the seven removed edges), so 8 − 4 = 4. Each endpoint
  gains one edge and had P1-degree at most 5. So P1 + α_τ ∈ E4. TRUE.

## 5. What this does not prove

- **No pair statement.** Everything here is about 4-regular subgraphs. A pair needs the quartic
  subgraph to split into two edge-disjoint cycles on a common vertex set, which is a separate
  Hamilton-decomposition question (G110-REVIEW.md lines 204-207).
- **G110 and C0 remain open in general.** The residual of §4 is open: nothing here excludes a
  minimal counterexample with m ≥ 42 (unconditionally) or m ≥ 60 (given F2(18)).
- **Census dependence.** Theorems 3.1, 3.2 and 3.3 are conditional on F1(14) and F2(18), which rest
  on one program each and were not re-run here. Theorem 3.5 (m ≤ 41) uses no census.
- **The C1 sub-case** of QUARTIC-REVIEW.md lines 240-277 stays open; §4.4 only records counts, one of
  which (P2 + β) fails when ε = 1.
- The minimality argument proves statements for all sizes up to a bound; it does not give an
  explicit quartic subgraph or an algorithm beyond the reductions.
- Not claimed: any consequence for P_2 (Δ ≤ 6, e ≥ 3n − 2) through REPORT.md Theorem 5 (c = 2),
  whose minimal counterexample is a C0 instance plus one edge. That route was not re-derived here.

## Appendix A. Computational checks

All code is in `reports/585-next/G110/checks/` (shared helpers in `common.py`), run with
`/private/tmp/erdos585-research-venv/bin/python` (Python 3.11, networkx 3.6.1, pysat with
CaDiCaL 1.5.3) under `timeout 240`, from that directory:
`timeout 240 /private/tmp/erdos585-research-venv/bin/python check_<name>.py`. Each script exits
nonzero on any mismatch and writes `out_<name>.json`. Every SAT witness is re-validated in code
(all degrees exactly 4). Every run below ended with RESULT: PASS. Hosts are random simple
bipartite 6-regular graphs: a circulant, then 20·e degree-preserving double-edge swaps.

**A.1 `check_eq1.py`** (seed 20261005, 2.4 s). 400 random hosts with 7 to 14 vertices per side.

| Identity | Checks | Mismatches |
|---|---|---|
| eq. (1): direct slack of (A, C) in H_y versus 2k − p + ε | 12,000 cut pairs | 0 |
| ∂_B(A ∪ C) = 6k + 2ε | 12,000 | 0 |
| transfer Φ_{y'}(A − y', C) = Φ_y(A, C) − 1 + e(C, y'), every port y' ∈ A | 34,873 | 0 |
| (0.1) and ∂_B(S) = 6k + 2ε for arbitrary S ⊆ V(Γ), ports allowed (Lemma 2.8) | 12,000 | 0 |
| slack of S equal in H_y for every y ∈ O − S | 63,233 | 0 |
| submodularity of ε, of Φ and of ∂_B on random pairs (S, T) | 12,000 pairs | 0 violations |
| flow criterion: brute-force min slack = max flow − 4m (60 graphs H_y with m = 6, 7; 60 random balanced graphs, m = 5 to 7, Δ ≤ 6; 46 of the 120 without a 4-factor) | 120 graphs | 0 |

**A.2 `check_synthetic.py`** (seed 77110, 6 s). 55 synthetic gadgets with a (2,5,0) cut: an
X-type piece (A of size c + 2 with five ports, C of size c saturated into A) and a C1-type piece Q
glued by 7 edges, plus o; c = 4 to 8, t = 6 to 10, |V(B)| = 22 to 38, with extra profiles that
force some r(i) ≥ 4 or s(a) ≥ 4. These graphs are not quartic-free; the checks are of the counts.

| Item | Checks | Failures |
|---|---|---|
| B simple 6-regular; (k, p, ε, Φ) = (2, 5, 0, −1) (Prop. 2.3) | 55 | 0 |
| max flow of H_y ≤ 4m − 1 (it was 4m − 1 in 44 cases and 4m − 2 in 11) | 55 | 0 |
| \|T\| = 7; Q deficiency 1 (at y) and 7; X + β: 2c + 3 vertices, 6c + 7 = 3n − 2 edges, Δ = 7; Q + α: 2t vertices, 6t = 3n edges (Prop. 2.6) | 55 | 0 |
| Q + α_τ for each distinct-endpoint τ: simple, balanced, deficiencies (3, 3), Δ ≤ 6 (Prop. 2.7(3)) | 764 | 0 |
| Q − i for r(i) ≥ 4: balanced, deficiency 7 − r(i) on both sides | 16 | 0 |
| Q + a for s(a) ≥ 4: balanced, deficiency 7 − s(a) on both sides | 19 | 0 |
| transfer Φ_{y'}((A − y') ∪ C) = e(C, y') − 2 (Prop. 2.4) | 275 | 0 |
| G-1 data: ∂_B(X) = 12, \|X\| ≥ 10, \|Y\| ≥ 12 (the c = 4, t = 6 instance has \|V(B)\| = 22) | 55 | 0 |
| Lemma 2.5(3) per τ: SAT "Γ has quartic H with H ∩ T = τ" agrees with SAT "Γ[X] realizes τ" and "Q realizes τ" | 1,925 | 0 |
| Lemma 2.5(3) for x = 0: "quartic H avoiding T" agrees with "Γ[X] or Q has one" | 55 | 0 |
| trace identity x = 4(\|V(H) ∩ A\| − \|V(H) ∩ C\|) on every SAT witness H | 1,630 | 0 |
| Lemma 0.2: X + β, and Q + α minus any two α-edges, have a {0,4}-subgraph | 55 + 1,155 | 0 |

**A.3 `check_olson.py`** (seed 4242, 0.2 s). Sanity check of Lemma 0.2 by two independent
deciders: exhaustive enumeration of vertex sets W with an exact max-flow test for a 4-factor of
M[W], and SAT.

| Family | Graphs | Result |
|---|---|---|
| X + β, c = 4, 5, 6, every one with a parallel edge at β | 90 | {0,4}-subgraph in all 90 |
| random bipartite multigraphs, n = 2 to 14, 3n − 2 edges, Δ ≤ 7 | 156 | {0,4}-subgraph in all 156 |
| controls, same with 3n − 3 edges | 156 | 19 without one (n = 2, 3, 4, 6) |
| agreement of the two deciders | 402 | 402 |

None of the 90 pieces X is quartic-free (expected at c ≤ 6), so the step "F must use β" is not
exercised by this check; it is a one-line consequence of quartic-freeness.

**A.4 `check_g1.py`** (seed 1101, 0.8 s).
- G1-a, integer brute force over c, t ∈ [0, 40) for the seven negative types (k, p, ε): the least
  c is 5 for every k = 1 type and 4 for (2, 5, 0); the least t is 6 throughout; so |X| ≥ 11 or 10
  and |Y| ≥ 13 or 12, as in Lemma 1.1.
- G1-b: 6,000 triples (B, o, y) with |V(B)| = 14 to 20: every B − o − y has a spanning 4-regular
  subgraph.
- G1-c: two K5,5 joined by two perfect matchings: 6-regular, a 10-edge cut with sides 10 and 10,
  and all 60 graphs B − o − y have a 4-factor.
- G1-d: 30 synthetic hosts with a k = 1 negative cut, five of each type (1,3,0), (1,4,0), (1,5,0),
  (1,4,1), (1,5,1), (1,5,2), each type including c = 5, t = 6 (|V(B)| = 24): the cut data,
  ∂_B(X) = 6 + 2ε, |X| = 2c + 1, |Y| = 2t + 1 and max flow ≤ 4m + Φ hold in all 30. With A.2 this
  shows that every size bound in Lemma 1.1 is attained.

**A.5 `check_c1sub.py`** (seed 5150, 0.1 s). 48 C1 instances with s = 11 to 18 carrying an
actual sub-case violation (24 with ε = 0, 24 with ε = 1): slack −1, e(A, U − C') = 7, P1
deficiencies 2 and 8, and e(P2 + β) − 3n = −2 in every ε = 0 instance and −3 in every ε = 1
instance; 735 distinct-endpoint P1 + α_τ, all in E4. The ε = 1 witness is
`checks/c1sub_eps1_witness.json` (FLAW.md).

**A.6 `check_hub.py`** (seed 606, 5 s). 44 hub-and-petal gadgets built to the shape of §2.5
(|V(B)| = 88 to 116, |R_I| ∈ {0, 2, 4, 6}, ov ∈ {0, 1, 2, 3}, including three petals sharing
pairwise; 36 requested shapes did not build, for example t = 6 petals cannot carry a shared
vertex). In all 44: every X_y is a (2,5,0) cut with slack −1 (264 cuts); every pair has union V or
V − i, intersection with ε = 0 and (k, Φ) = (3, 2) or (2, 0), and the shared vertex has 3 + 3
petal neighbors (660 pairs); N(R_I) ⊆ R_O and |R_O| − |R_I| = 7 − ov; and the contraction counts of
§4.3 (100 checks): petal contraction e' = 3n' + 3 with degree-7 I-side vertices; cluster
contraction 21 − 3·ov − 3·(clusters) with cluster degree 7|K| − 6·ov_K (slack 5 for sharing
forests, 2 for the 3-cycle); petal-minus-shared contraction e' = 3n' + 3, with mixed sides exactly
at the petals that share. These gadgets contain quartic subgraphs; the check is of the counting
in Prop. 2.12 and §4.3, not of Theorem 2.9.

**Script hashes (SHA-256, first and last 8 hex digits)** at the time of the frozen runs: `common.py`
229c9ae2...2f172ce4, `check_eq1.py` b5c11887...93f92eb7, `check_synthetic.py` 45256565...9ec02550,
`check_olson.py` 2358c456...454b8cf8, `check_g1.py` e57a0441...126a7b71, `check_c1sub.py`
4f548de2...8a10994e, `check_hub.py` 906dce44...988080c9 (full values in `M1-LOG.md`). All six check
scripts were rerun from scratch after the last edit, with the counts above.

**Not covered by computation.** The minimality arguments (Props. 2.2 to 2.7, Theorem 2.9,
Corollary 2.10, Lemma 3.4) cannot be run on a counterexample, since none is known. The checks cover
every identity and count those proofs use, the gluing equivalence, and the threshold lemma.

## Appendix B. Sources (paths relative to the repository root)

- `reports/585-overnight/paper110/scout-gadget/PAPER.md`: class and gadget (lines 27-31), zero-sum
  threshold proof (33-49), eq. (1) (59-79), cut list without quartic-freeness (81-84), four types
  (86-106), last-row data (115-119).
- `reports/585-overnight/paper110/reviews/G110-REVIEW.md`: zero-sum check (100-114), four types and
  min-cut value −1 (139-181), no pair from quartic (204-207).
- `reports/585-fable-wildcard/lanes/quartic-subgraph/REPORT.md`: classes (238-241), bipartite
  criterion (243-246), reductions (249-265), census (269-277).
- `reports/585-fable-wildcard/reviews/QUARTIC-REVIEW.md`: criterion proof (187-201), reductions
  (206-231), sub-case statement (240-246), partial progress and seven-edge count (252-277).
- `585-RESEARCH-PLAN.md`: G-1 statement (200-217), G110 roadmap (184-281).
- `reports/585-next/STATE.md`: F1, F2, C0≤8, C0-9 (lines 16-26).
- `reports/585-findings/FINDINGS.md`: Corollary C (958-961).
- `reports/585-fable/CHECKPOINT-01.md` line 17, `CHECKPOINT-02.md` line 12, `CHECKPOINT-05.md`
  lines 28-33, `reports/585-fable/tools/README.md` lines 26-38, `reports/585-fable/data/`.
- Olson, J. Number Theory 1 (1969) 8-10, via Alon, Tools from Higher Algebra, Theorem 6.2 (as
  recorded in PAPER.md lines 44-49 and G110-REVIEW.md lines 89-98; not re-fetched here).
