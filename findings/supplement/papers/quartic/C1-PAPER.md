# C1: the petal lattice closes the C1 sub-case

Author lane M3, October 5, 2026. Status: frozen for independent review (SHA-256 in
`C1-FROZEN.sha256`). Written proofs with computational checks of every identity and count
(Appendix A). Not reviewed. No Lean and no `check.sh` run, so nothing here is a project oracle
PASS. Rung (a) for the theorems; Corollary 0.1 is (b).

## 0. Results at a glance

| Item | Statement | Verdict | Where |
|---|---|---|---|
| Thm 4.3 | every C1 instance (sides s and s + 1, Δ ≤ 6, D_U ≤ 1) has a 4-regular subgraph | proved on paper | §2-§4 |
| Cor 5.3 | QB(4): every bipartite graph with Δ ≤ 6, n ≥ 2 and e ≥ 3n − 4 has a 4-regular subgraph | proved, from Thm 4.3 | §5 |
| Cor 5.1, 5.2 | C0, E3, E4 for all sizes; G110-quartic for every simple bipartite 6-regular B | proved, from Thm 4.3 | §5 |
| Cor 5.4 | P_2: every graph with Δ ≤ 6, n ≥ 2, e ≥ 3n − 2 has a 4-regular subgraph | proved, from Thm 4.3 and REPORT.md Theorem 5 (c = 2) | §5 |
| Cor 0.1 | P_2 for n ≤ 2M + 2 whenever C0 holds for m ≤ M: n ≤ 84 (no census), ≤ 120 (F2(18)), ≤ 126 (F2(19)) | proved from reviewed results only; independent of Thm 4.3 | §0.1 |
| Hints | all ten true; two need a wording repair (hint 1's justification, hint 2's "smaller") | see table | §6 |

The C1 sub-case of QUARTIC-REVIEW.md lines 240-246 is closed, but not by gluing across one cut.
The new step is global: in a minimal counterexample every proper vertex set S with |S| ≥ 2 has
g(S) = 6|S| − 2e(G[S]) ≥ 10, so the complement of every violation at every port is a set with
g = 10 that contains the unique degree-5 vertex u1 of the saturated side (Lemma 3.2). Since u1 has
degree 5 and at least 3 neighbors in each such set, any two of them overlap in at least two
vertices, and they form a lattice under ∩ and ∪ (Lemma 4.2). The union of the petals of all ports
is then one set with g = 10, which can hold W-deficiency at most 2, while the ports carry 7.

**Where to attack first.**
1. Lemma 2.1 (sparsity) and (M): the induction is on the size of C1 instances in either
   orientation, and it needs E4 at the same size s (for S = V − w), which Lemma 1.5 supplies.
2. Lemma 3.1 (pure algebra) and the case analysis of Lemma 3.2, in particular D_A ≤ 6 for a port
   and the step from g(Q) ≥ 10 to D_U = 1, k = 2, u1 ∉ C.
3. Lemma 4.1(3) and Lemma 4.2(a): u1 has at least 3 neighbors in every member of 𝒫, by sparsity of
   Q − u1, and degree 5, so two members share a second vertex. Lemma 4.2(b): Q ∪ Q' ≠ V by κ.
4. Theorem 4.3: the contradiction needs every port to have a petal, that is, G − y has no
   4-factor for every W-vertex y of degree at most 5.
5. Corollary 0.1 and §5.4 rely on REPORT.md Theorem 5 for c = 2 (Tutte's f-factor theorem and
   the budget identity), reviewed in QUARTIC-REVIEW.md and re-derived here by hand.

### 0.1 Side deliverable: P_2 for small n from reviewed results only

**Corollary 0.1.** Let M ≥ 1. If every C0 instance of size m ≤ M has a 4-regular subgraph, then
every graph (not necessarily bipartite) with Δ ≤ 6, 2 ≤ n ≤ 2M + 2 and e ≥ 3n − 2 has one.

*Proof.* Suppose not, and among all counterexamples to P_2 (REPORT.md line 136: Δ ≤ 6, n ≥ 2,
e ≥ 3n − 2, no 4-regular subgraph) take G with n minimal, then e minimal; then n ≤ 2M + 2. These
are exactly the conventions of REPORT.md Lemma 4 and Theorem 5 (lines 196-214: "a counterexample to
P_c with n minimal, then e minimal"), accepted by QUARTIC-REVIEW.md lines 82-104 (Lemma 4, wording
fix only) and line 20 (Theorem 5). By Theorem 5 with c = 2 (REPORT.md line 212), G = B + f where B
is bipartite with sides S, T, |S| = |T| + 1, every T-vertex has degree 6, and f is one edge inside
S. So B is a C0 instance of size |T| (smaller side T, saturated; Δ(B) ≤ 6), and
n = 2|T| + 1 ≤ 2M + 2 gives |T| ≤ M. By hypothesis B, hence G, has a 4-regular subgraph. ∎

The c = 2 case of Theorem 5 is short enough to re-derive, and I did (§5.4). Instances:

| C0 range used | Source | P_2 holds for |
|---|---|---|
| m ≤ 41 | PAPER.md Thm 3.5 (no census), REVIEW.md ACCEPT | n ≤ 84 |
| m ≤ 59 | PAPER.md Thm 3.3 with F2(18) (two independent methods), CORRECTIONS.md | n ≤ 120 |
| m ≤ 62 | Thm 3.3 with F2(19) (two generators, one decider), CORRECTIONS.md | n ≤ 126 |
| all m | Thm 4.3 below (C0 ⊆ C1), not yet reviewed | all n |

## 1. Setting, notation, tools

All graphs are finite, simple and bipartite unless said otherwise. A *quartic subgraph* is a
nonempty edge set in which every vertex has degree 0 or 4. Classes (PAPER.md lines 53-60):
- C_j(s), s ≥ 1: sides U (|U| = s) and W (|W| = s + 1), Δ ≤ 6, D_U ≤ j, where D_Z = Σ_{v∈Z}(6 − deg v).
  C0: D_U = 0. C1: D_U ≤ 1. The size is s. Which side is called U is part of the instance: a
  bipartite graph whose smaller side Z has |Z| = s and deficiency ≤ 1 is a C1(s) instance.
- E_d(s), s ≥ 1: both sides of size s, Δ ≤ 6, deficiency at most d on each side.
"C1 holds" means every C1 instance has a quartic subgraph; likewise for the other classes.

For a graph G with sides U, W and S ⊆ V(G) write S_U = S ∩ U, S_W = S ∩ W, e(S) = e(G[S]), and
- g(S) = 6|S| − 2e(S);
- κ(S) = |S_U| − |S_W| and k(S) = −κ(S) = |S_W| − |S_U| (both modular);
- D^S(Z) = Σ_{v∈Z} (6 − deg_{G[S]} v) for Z ⊆ S, the deficiency inside G[S]; D(Z) = D^{V}(Z).

**Identity 1.1.** D^S(S_U) = 6|S_U| − e(S) and D^S(S_W) = 6|S_W| − e(S). Hence
g(S) = D^S(S_U) + D^S(S_W), D^S(S_U) − D^S(S_W) = 6κ(S), and

    g(S) = 2·D^S(S_W) + 6κ(S) = 2·D^S(S_U) − 6κ(S).

Writing j ≥ 0 for the size difference of the two sides of G[S] and d for the in-S deficiency of
the smaller side (either side if j = 0), g(S) = 2d + 6j, and the larger side has in-S deficiency
d + 6j. *Proof.* Every edge of G[S] has one end in S_U and one in S_W. ∎

**Identity 1.2.** For A, B ⊆ V: g(A ∪ B) + g(A ∩ B) = g(A) + g(B) − 2e(A − B, B − A). So g is
submodular. *Proof.* e(A ∪ B) = e(A) + e(B) − e(A ∩ B) + e(A − B, B − A), and |·| is modular. ∎

**Identity 1.3.** For v ∈ S: g(S − v) = g(S) − 6 + 2·deg_{G[S]}(v). ∎

**Lemma 1.4 (flow criterion; PAPER.md Lemma 0.1, lines 87-96, reviewed).** A bipartite graph with
sides P, Q of equal size s ≥ 1 has a spanning 4-regular subgraph iff e(A, Q − C) ≥ 4(|A| − |C|) for
all A ⊆ P, C ⊆ Q. If Δ ≤ 6, the *slack* e(A, Q − C) − 4(|A| − |C|) equals 2k − D_A + ε with
k = |A| − |C| and ε = D_C + e(P − A, C) (deficiencies in that graph), and a violation (negative
slack) has k ≥ 1.

**Lemma 1.5 (E4 reduction; REPORT.md line 254, QUARTIC-REVIEW.md lines 211-212, reviewed).** Let
H ∈ E4(a) have no spanning 4-regular subgraph. Then H has two vertex-disjoint induced subgraphs, each
a C1 instance or a single vertex, of sizes a1 + a2 = a − 1 (a single vertex counts as size 0). So if
C1 holds at every size below a, H has a quartic subgraph.

*Proof.* Lemma 1.4 gives A ⊆ P, C ⊆ Q, k ≥ 1, with D_A ≥ 2k + 1 + ε. As D_A ≤ D_P ≤ 4: k = 1,
ε ≤ 1, D_A ≥ 3 + ε. In H[A ∪ C] the side C (size |C|, |A| = |C| + 1) has in-piece deficiency
D_C + e(C, P − A) = ε ≤ 1. In H[(P − A) ∪ (Q − C)], |Q − C| = |P − A| + 1 and the side P − A has
in-piece deficiency (D_P − D_A) + e(P − A, C) ≤ (4 − 3 − ε) + ε = 1. The sizes are |C| and
a − 1 − |C|. If both were 0 then a = 1, but E4(1) is empty (one vertex per side, deficiency ≥ 5).
A piece of positive size is a C1 instance below a; its quartic subgraph is one of H. ∎

## 2. A minimal counterexample is sparse

Suppose C1 fails. Let s be the least size of a quartic-free C1 instance, and G one of them, with
sides U (|U| = s) and W (|W| = s + 1), V = V(G), n = 2s + 1. Every subgraph of G is quartic-free.

**(M)** Every C1 instance of size 1, ..., s − 1 has a quartic subgraph (minimality). Every E4(a)
instance with 1 ≤ a ≤ s has one: a spanning 4-regular subgraph is nonempty, and otherwise Lemma 1.5
gives a C1 piece of size between 1 and a − 1 ≤ s − 1.

**Lemma 2.1 (sparsity).** g(S) ≥ 10 for every S ⊆ V with 2 ≤ |S| ≤ n − 1.

*Proof.* Let 2 ≤ |S| ≤ 2s and suppose g(S) ≤ 8. By Identity 1.1, g(S) = 2d + 6j with j, d ≥ 0, so
j ≤ 1. If j = 0, G[S] is balanced, both sides of size a = |S|/2 with 1 ≤ a ≤ s, both of in-S
deficiency d ≤ 4: an E4(a) instance. If j = 1, then d ≤ 1, the smaller side has size
a = (|S| − 1)/2, so 1 ≤ a ≤ s − 1 (|S| ≥ 2 and |S| ≤ 2s), and G[S] is a C1(a) instance with that
smaller side. Either way (M) gives a quartic subgraph of G[S] ⊆ G, a contradiction. g is even, so
g(S) ≥ 10. ∎

Note that j = 0 with a = s happens only for S = V − w with w ∈ W, where G[S] = G − w is an E4
instance of the same size s; that is why (M) covers E4 at size s.

**Basic counts.** e(G) = 6s − D_U and D_W = 6(s + 1) − e(G) = 6 + D_U ≥ 6, so g(V) = 6n − 2e = 6 + 2D_U.
Call a W-vertex of degree at most 5 a *port* and write def(w) = 6 − deg(w). Ports exist. By
Identity 1.3 and Lemma 2.1, g(V − w) = 2D_U + 2deg(w) ≥ 10, so every W-vertex has degree at least
5 − D_U (for D_U = 1 this is the reviewed step "d0 ≤ 3 gives an E4 instance").

## 3. Ports and petals

**Lemma 3.1 (cut identity; no minimality used).** Let G be any C1(s) instance, y a port, and
S = A ∪ C with A ⊆ W − y, C ⊆ U. Put k = |A| − |C|, Q = V − S, and let σ be the slack of (A, C) in
the balanced graph G − y (sides W − y and U):

    σ = e(A, U − C) − 4k = 2k − D_A + ε,   ε = D(C) + e(C, W − A),

where D_A, D(C) are G-deficiencies. Then

    g(Q) = 6 + 2D_U + 2k + 2σ − 2D(C)   and   κ(Q) = k − 1.

*Proof.* Lemma 1.4 applied to G − y with P = W − y, Q-side U: A-vertices keep their G-degrees
(A ∌ y), and the deficiency of C in G − y is D(C) + e(y, C), so ε = D(C) + e(y, C) + e(W − y − A, C) =
D(C) + e(C, W − A). Now e(G[Q]) = Σ_{u∈U−C} deg u − e(A, U − C) = 6|U − C| − D_U + D(C) − (6k − D_A + ε),
using e(A, U − C) = σ + 4k = 6k − D_A + ε. With |Q| = 2s + 1 − 2|C| − k:

    g(Q) = 6(2s + 1 − 2|C| − k) − 2[6s − 6|C| − D_U + D(C) − 6k + D_A − ε]
         = 6 + 2D_U − 2D(C) + 6k − 2D_A + 2ε = 6 + 2D_U − 2D(C) + 2k + 2σ.

κ(Q) = |U − C| − |W − A| = (s − |C|) − (s + 1 − |C| − k) = k − 1. ∎

**Lemma 3.2 (petal lemma).** In the minimal counterexample G, let y be a port and S = A ∪ C ⊆ V − y
a violation of G − y (σ < 0; one exists). Then D_U = 1, k = 2, σ = −1, u1 ∉ C (u1 the U-vertex of
degree 5), D_A = 5 + ε with ε = e(C, W − A) ∈ {0, 1}, and Q = V − S has g(Q) = 10, κ(Q) = 1,
y ∈ Q and u1 ∈ Q.

*Proof.* G − y is balanced with sides of size s ≥ 1, and a spanning 4-regular subgraph of it would
be a quartic subgraph of G; so Lemma 1.4 gives a violation, and every violation has k ≥ 1 and
D_A ≥ 2k + 1 + ε ≥ 2k + 1. Since A ⊆ W − y, D_A ≤ D_W − def(y) ≤ 6 + D_U − 1 ≤ 6, so k ≤ 2.
Q contains y and U − C, and U − C ≠ ∅ (C = U would give |A| = s + k > |W − y|), so |Q| ≥ 2; and
Q ≠ V because A ≠ ∅. Lemma 2.1 gives g(Q) ≥ 10, and Lemma 3.1 turns this into
k + σ ≥ 2 − D_U + D(C). With σ ≤ −1: k ≥ 3 − D_U + D(C). With k ≤ 2: D_U ≥ 1 + D(C), so D_U = 1,
D(C) = 0 (that is, u1 ∉ C) and k = 2. Then σ ≥ 2 − 1 + 0 − 2 = −1, so σ = −1 and D_A = 2k − σ + ε =
5 + ε; hence ε = D_A − 5 ≤ 1, and ε = e(C, W − A) because D(C) = 0. Finally
g(Q) = 6 + 2 − 0 + 4 − 2 = 10 and κ(Q) = 1. ∎

So the minimal counterexample has D_U = 1, and **every violation at every port is of the sub-case
type** of QUARTIC-REVIEW.md lines 240-246 (k = 2, D_A = 5 + ε, u1 ∉ C), with P1 = G[Q] and
P2 = G[S]. This is the reviewed reduction's case analysis, rederived from sparsity in one line,
and it holds for every port, not only for a minimum-degree one.

## 4. The petal lattice

From now on D_U = 1 and u1 is the U-vertex of degree 5. Let

    𝒫 = { Q ⊆ V : Q ≠ V, |Q| ≥ 2, g(Q) = 10, κ(Q) = 1, u1 ∈ Q }.

By Lemma 3.2, every port y lies in some member of 𝒫 (the complement of any violation of G − y);
call such a member a *petal* of y.

**Lemma 4.1.** Let Q ∈ 𝒫. Then (1) |Q| ≥ 3; (2) D^Q(Q_W) = 2, so D(Q_W) ≤ 2; (3) u1 has at least
three neighbors in Q.

*Proof.* (1) κ(Q) = 1 gives |Q_U| = |Q_W| + 1; if Q_W = ∅ then Q = {u1}, against |Q| ≥ 2. So
|Q| = 2|Q_W| + 1 ≥ 3. (2) Identity 1.1: D^Q(Q_W) = (g(Q) − 6κ(Q))/2 = 2, and D(Q_W) ≤ D^Q(Q_W)
because deg_{G[Q]} ≤ deg_G. (3) Q − u1 has |Q| − 1 ≥ 2 vertices and is proper, so by Lemma 2.1 and
Identity 1.3, 10 ≤ g(Q − u1) = 10 − 6 + 2·deg_{G[Q]}(u1), that is, deg_{G[Q]}(u1) ≥ 3. ∎

**Lemma 4.2 (lattice).** If Q, Q' ∈ 𝒫, then Q ∩ Q' ∈ 𝒫 and Q ∪ Q' ∈ 𝒫.

*Proof.* (a) Q ∩ Q' ⊋ {u1}: otherwise the neighbors of u1 in Q and in Q' lie in the disjoint sets
Q − u1 and Q' − u1, and Lemma 4.1(3) gives deg u1 ≥ 3 + 3 = 6 > 5. So |Q ∩ Q'| ≥ 2.
(b) Q ∪ Q' ≠ V: otherwise κ(Q ∩ Q') = κ(Q) + κ(Q') − κ(V) = 1 + 1 − (s − (s + 1)) = 3, so by
Identity 1.1 g(Q ∩ Q') ≥ 6κ = 18, while Identity 1.2 gives g(Q ∩ Q') ≤ g(Q) + g(Q') − g(V) =
20 − 8 = 12.
(c) By (a), (b) and Lemma 2.1, g(Q ∩ Q') ≥ 10 and g(Q ∪ Q') ≥ 10; by Identity 1.2 their sum is at
most 20. So both equal 10. κ is modular, so κ(Q ∩ Q') + κ(Q ∪ Q') = 2, and a set with g = 10 has
κ ≤ 10/6 by Identity 1.1 (D^S(S_W) ≥ 0), so κ ≤ 1. Hence both have κ = 1. Both contain u1, both
are proper with at least two vertices. ∎

**Theorem 4.3. C1 holds: every C1 instance has a quartic subgraph.**

*Proof.* Suppose not and take the minimal counterexample G of §2. By Lemma 3.2, D_U = 1 and every
port y has a petal Q_y ∈ 𝒫. Let y_1, ..., y_p be the ports. By Lemma 4.2 and induction on i,
R_i = Q_{y_1} ∪ ... ∪ Q_{y_i} ∈ 𝒫 for every i. R_p contains every port, so
D((R_p)_W) = Σ_{ports} def = D_W = 7. Lemma 4.1(2) gives D((R_p)_W) ≤ 2. Contradiction. ∎

**Lemma 4.4 (core lemma, minimality-free form; this is what Appendix A tests).** Let G be a C1(s)
instance that is *sparse*: g(S) ≥ 10 for all S ⊆ V with 2 ≤ |S| ≤ n − 1. Call a port y *bad* if
G − y has no spanning 4-regular subgraph. If D_U = 0 there is no bad port. If D_U = 1, every
violation at a bad port has its complement in 𝒫, the union of these complements is in 𝒫, and the
bad ports have total deficiency at most 2.

*Proof.* Lemmas 3.2, 4.1 and 4.2 use minimality only through Lemma 2.1, that is, through sparsity
(Lemma 3.2 also uses that G − y has a violation, which is the definition of bad). Repeat the proof
of Theorem 4.3 over the bad ports only. ∎

So quartic-free implies every port is bad, minimal implies sparse, and the two are incompatible.

## 5. Consequences (each implication checked)

**Corollary 5.1 (C0, G110-quartic).** C0 ⊆ C1, so every C0 instance has a quartic subgraph. For a
simple bipartite 6-regular B and any vertex o, B − o is a C0 instance (PAPER.md lines 58-60: the
side of o minus o has m ≥ 5 vertices, all of degree 6, and the other side has m + 1 vertices), so
B − o has a 4-regular subgraph: G110-quartic holds for every six-port gadget.

**Corollary 5.2 (E4, E3).** E4 holds at every size, by Lemma 1.5 and Theorem 4.3; E3 ⊆ E4.

**Corollary 5.3 (QB(4)).** Every bipartite graph H with Δ ≤ 6, n ≥ 2 vertices and e ≥ 3n − 4 edges
has a 4-regular subgraph. Conversely QB(4) implies C1, so the two are equivalent.

*Proof.* Delete edges until e = 3n − 4 (this keeps Δ ≤ 6 and n). Now g(V) = 6n − 2e = 8 = 2d + 6j
(Identity 1.1), so j ≤ 1: if j = 0, H ∈ E4(n/2); if j = 1, d = 1 and H ∈ C1((n − 1)/2). In both
cases the size is at least 1 because n ≥ 2. Corollary 5.2 or Theorem 4.3 applies. Conversely a
C1(s) instance has n = 2s + 1 and e = 6s − D_U ≥ 3n − 4. ∎

So F2(N) (CORRECTIONS.md table: δ ≥ 4, Δ ≤ 6, e ≥ 3n − 4 implies a 4-regular subgraph, n ≤ N)
holds for every N, which agrees with the census for N ≤ 19.

**Corollary 5.4 (P_2).** Every graph with Δ ≤ 6, n ≥ 2 and e ≥ 3n − 2 has a 4-regular subgraph.
*Proof.* Corollary 0.1 with C0 for all m (Corollary 5.1). ∎

### 5.4 Re-derivation of REPORT.md Theorem 5 for c = 2

(Used by Corollaries 0.1 and 5.4; reviewed as QUARTIC-REVIEW.md item 3, line 20.) Let G be a
counterexample to P_2 with n minimal, then e minimal. Then e = 3n − 2 (delete an edge otherwise;
n ≥ 2 and Δ ≤ 6 are kept), δ ≥ 4 (deleting a vertex of degree ≤ 3 leaves n − 1 ≥ 2 vertices, as
n = 2 would need e ≥ 4, and at least 3(n − 1) − 2 edges), so D = 6n − 2e = 4, and G has no spanning
4-regular subgraph. With f = deg − 4 ≥ 0, Tutte's f-factor criterion (REPORT.md lines 140-158,
citation fixed by the review) gives a barrier (S, T) with δ(S, T) ≤ −2 (δ is even). The budget
identity (REPORT.md Lemma 2, lines 160-180) reads 3δ + 2D = 2e(S) + 4e(T) + 4D_T + Σ_C w(C) with all
terms nonnegative, so δ = −2 and the right side is 2. Lemma 4 (lines 196-204) gives, for every
component C of G − S − T with |C| ≥ 2, D_C + e(C, S) + e(C, T) ≥ 6 and so w(C) ≥ 3; a single
vertex x with a = e(x, S) has w = 12 − a − 3[a odd] ≥ 4. Hence G − S − T is empty and
2e(S) + 4e(T) + 4D_T = 2: e(S) = 1, e(T) = 0, D_T = 0. Then identity (**) of Lemma 2,
δ = 4(|T| − |S|) + 2e(S) + e(S, R) − q with R = ∅ and q = 0, gives |S| = |T| + 1. So G is a
bipartite graph with sides S, T (T saturated) plus one edge inside S: B = G − f ∈ C0(|T|), and
n = 2|T| + 1 is odd. This matches REPORT.md line 212.

## 6. The briefed hints

Sub-case notation (QUARTIC-REVIEW.md lines 240-246, PAPER.md §4.4): w0 a port, (A, C') a violation of
G − w0 with |A| = |C'| + 2, D_A = 5 + ε, u1 ∉ C', ε = e(C', W − A); P1 = G[(U − C') ∪ (W − A)],
P2 = G[A ∪ C'], c = |C'|, t = |U − C'|; T = E(A, U − C'), and f the edge from C' to W − A when ε = 1.
None of H4-H9 is used by the proof of Theorem 4.3; they were checked because the brief asked.

| # | Hint (short) | Verdict |
|---|---|---|
| H1 | combined minimality; no C0 counterexample of size s; D_U = 1; d0 ∈ {4, 5} | TRUE; the C0 step needs more than "its (2,5,0) cut" |
| H2 | g submodular; g ∈ {6, 8} gives a smaller C0/E3/C1/E4 instance; g ≥ 10; g(V) = 8; g(X) = 12 + 2ε, g(P1) = 10 | TRUE after two repairs |
| H3 | f submodular, equals the slack of G − w for w ∉ S, minimum −1 | TRUE ("w ∉ S" means w ∈ W − S) |
| H4 | trace identity x − x' = 4(\|V(H) ∩ A\| − \|V(H) ∩ C'\|) | TRUE |
| H5 | P1 + α_τ in E4 for distinct-endpoint 4-traces | TRUE (size t ≤ s; "smaller" not needed) |
| H6 | ε = 0: P2 + β at 3n − 2 | TRUE |
| H7 | ε = 1: signed contraction, 3n − 2 elements, x − x' ≡ 0 (mod 4) | TRUE |
| H8 | ε = 1: P1 + uw' is a smaller C1 instance when u ≁ w' | TRUE |
| H9 | endpoint bounds 3, 3, 2 | TRUE |
| H10 | uncross over the minimum-degree ports; P1 sides as petals | TRUE as a route; it works with all ports, and the petals all contain u1 |

**H1.** (M) gives C1 below s, and E3 ⊆ E4 at every size ≤ s (Lemma 1.5), so "C0, C1, E3 and E4 hold
at all smaller sizes" is true, and E3, E4 also hold at size s. A quartic-free C0(s) instance is
impossible, but the justification "its (2,5,0) cut leaves a smaller C1 piece" covers only the
k = 2 cuts of a minimum-degree vertex of degree 5; the reviewed argument also needs the d0 ≤ 3 case
(an E3(s) instance) and the k = 1 cuts (E3 pieces of size ≤ s), all covered by (M). Lemma 3.2
does all of it at once: if D_U = 0, every violation has g(V − S) = 6 + 2k + 2σ ≤ 8 (k ≤ 2, σ ≤ −1),
against Lemma 2.1. Then D_U = 1, D_W = 7, and every W-vertex has degree ≥ 4 (§2, basic counts), so
d0 ∈ {4, 5} (d0 ≤ 5 because the average W-degree is (6s − 1)/(s + 1) < 6).

**H2.** Submodularity is Identity 1.2. The repairs: (i) g ≤ 4 must be excluded too; it gives j = 0,
d ≤ 2, an E2 ⊆ E4 instance (Lemma 2.1 covers it). (ii) "smaller" fails for S = V − w (w ∈ W),
where G[S] = G − w is an E4 instance of the same size s; it is still excluded, because (M) contains
E4(s). With these, g(S) ≥ 10 for 2 ≤ |S| ≤ |V| − 1 (Lemma 2.1), g(V) = 6 + 2D_U = 8. In the
sub-case, g(P1) = 10 by Lemma 3.2 (or directly: e(P1) = 6t − 8 on 2t − 1 vertices), and since
g(S) + g(V − S) = g(V) + 2∂(S) with ∂(P2) = 7 + ε, g(P2) = 22 + 2ε − 10 = 12 + 2ε.

**H3.** With f(S) = e(S_W, U − S_U) − 4k(S): f(S) = Σ_{w∈S_W} deg w − e(S) − 4k(S), a modular term
minus the supermodular e(S), so f is submodular. Using Identity 1.1, f(S) = g(S)/2 − k(S) − D(S_W)
(check J3). For w ∈ W − S, the edges from S_W to U are the same in G and in G − w, so f(S) is the
slack of (S_W, S_U) in G − w (Lemma 1.4). The minimum over cuts avoiding a minimum-degree w is −1:
cuts with negative slack exist (G − w has no 4-factor) and all have σ = −1 (Lemma 3.2, which holds
for every port, not only minimum-degree ones). If w ∈ U the statement is meaningless (G − w is not
balanced).

**H4.** Let H be quartic in G, x = |H ∩ T|, x' = |H ∩ {f}| (x' = 0 if ε = 0). Every edge at a C'-vertex
goes to A or is f, every edge at an A-vertex goes to C' or is in T. Summing H-degrees over A and over
C': 4|V(H) ∩ A| = e_H(A, C') + x and 4|V(H) ∩ C'| = e_H(A, C') + x'. Subtract. So
(x, x') ∈ {(0, 0), (4, 0), (1, 1), (5, 1)} (x ≤ 7, x' ≤ ε). All four occur on built instances (S3).

**H5.** P1 + α_τ (α on the W side, joined to the four distinct U − C' ends of τ) has sides of size t;
deficiency 2 + (6 − 4) = 4 on the W side and 8 − 4 = 4 on the U side (U − C' has in-P1 deficiency
1 + 7 = 8); each end had P1-degree ≤ 5. So it is in E4(t) with t = s − c ≤ s, and (M) applies; a
quartic F must use α with all four edges (P1 is quartic-free), and F minus them realizes τ. "Smaller"
needs C' ≠ ∅; it is not needed because (M) contains E4(s).

**H6.** P2 + β (β on the U side joined to the A-ends of T): 2c + 3 vertices, 6c + 7 = 3(2c + 3) − 2
edges, maximum degree 7 (PAPER.md §4.4, line 581); Olson (PAPER.md Lemma 0.2) gives F with degrees
in {0, 4}, F uses β (P2 quartic-free), so P2 realizes a 4-subset of T.

**H7.** In the coordinate-sum-zero subgroup K ⊆ (Z/4)^{V(P2) ∪ {β}}, of rank 2c + 2, take the list:
e_u − e_a for each edge ua of P2 (u ∈ C', a ∈ A), e_β − e_a for each T-edge with A-end a, and
e_{c*} − e_β for f = c*w'. Its length is (6c − 1) + 7 + 1 = 6c + 7 = 3(2c + 2) + 1, Olson's bound
for (Z/4)^{2c+2} (the group-ring argument of PAPER.md lines 108-122 works for any list). A nonempty
zero-sum sublist has: at a ∈ A, minus the number of chosen elements at a, which is ≤ deg_G(a) ≤ 6,
so 0 or 4; at a C'-vertex, the number of chosen elements, at most 6, so 0 or 4; at β, x − x' ≡ 0
(mod 4) with x ≤ 7 chosen T-elements and x' ≤ 1. If x = x' = 0 the sublist is a quartic subgraph of
P2. So P2 realizes a trace of type (4, 0), (1, 1) or (5, 1), with "realizes" as in PAPER.md §2.3
plus deg_F(c*) + x' ∈ {0, 4}. The unsigned P2 + β has 3n − 3 edges (FLAW.md), so the f-element is
what restores the count. Checked: count, a zero-sum solution on 17 of 17 ε = 1 instances (S5).

**H8.** For a T-edge e = au (u ∈ U − C') with u ≁ w': P1 + uw' has sides W − A (t − 1) and U − C' (t),
W-side deficiency 2 − 1 = 1, Δ ≤ 6 (u sends e out of P1 and w' sends f out of P1), and it is
simple. So it is a C1(t − 1) instance, t − 1 < s, and (M) gives a quartic F that must use uw'; F − uw'
realizes {e, f} in P1. If u ~ w' the step is not available (57 of 119 checked pairs on built
instances, S7).

**H9.** For a ∈ A with s(a) ≥ 4 T-edges, P1 + a is balanced (t, t) with deficiency 8 − s(a) ≤ 4 on
both sides: E4(t). For x ∈ U − C' with r(x) T-edges, P1 − x is balanced (t − 1) with deficiency
8 − def(x) − r(x) on both sides, at most 4 when r(x) ≥ 4, or r(u1) ≥ 3. (QUARTIC-REVIEW.md lines
257-264; deficiency formulas checked, S8.)

**H10.** The route of §3-§4 is this hint, with two changes. (a) Every port (W-degree ≤ 5) has a
petal, so there are 4 to 7 ports carrying total deficiency 7 (D_W = 7, each port has deficiency
1 or 2); if d0 = 5 they are seven degree-5 vertices, as the hint says, and d0 = 4 needs no separate
treatment. (b) The petals are not disjoint: they all contain u1, and that is what makes them a
lattice (Lemma 4.2) and ends the argument.

## 7. What this does not prove

- **Not reviewed.** Theorem 4.3 and its corollaries are a written proof by one lane. The identities
  and counts are machine-checked (Appendix A); the minimality steps cannot be run on a
  counterexample, since none exists if the theorem is right.
- **No pair statement.** As in PAPER.md §5: a 4-regular subgraph is not a pair of edge-disjoint
  cycles on a common vertex set.
- **General graphs beyond P_2.** P_3 and P_4 (e ≥ 3n − 3, e ≥ 3n − 4 for all graphs with Δ ≤ 6) stay
  open: REPORT.md Theorem 5 leaves 12 types for c = 3 (one of them C0) and 58 for c = 4 (lines
  215-221), and only the bipartite ones are covered here.
- **Bipartite, e ≥ 3n − 5** (classes C2, E5) was not attempted. The argument uses D_U = 1 twice: u1
  lies in every petal and has degree 5.
- **No census used.** F1, F2 and the C0 census do not enter Theorem 4.3; they agree with it (no
  4-regular-free member was ever found in F2 for n ≤ 19, which Corollary 5.3 predicts).
- **PAPER.md.** Its structure theorems stay true as statements, but with Theorem 4.3 the minimal C0
  counterexample they describe does not exist, and the size bounds of PAPER.md §3 become special
  cases of Corollary 5.1.

## Appendix A. Computational checks

All code is in `reports/585-next/G110/c1checks/` (own code, nothing imported from `checks/` or
`review/`; helpers in `c1common.py`, the sub-case builder in `check_subcase.py` and, copied verbatim,
`c1build.py`). Interpreter `/private/tmp/erdos585-research-venv/bin/python` (Python 3.11.15,
networkx 3.6.1, pysat with CaDiCaL 1.5.3; no numpy), every run under `timeout 240`, from that
directory. Generator for the exhaustive classes: plain nauty genbg 2.9.3
(`~/.cache/erdos585/nauty2_9_3/genbg`). Deciders: SAT for "nonempty, all degrees in {0, 4}" with
every witness re-validated in code; networkx max flow for 4-factors. Every script exits nonzero on a
mismatch and writes `out_*.json`. The instances below are not quartic-free (none is known), so the
checks cover identities, counts and the minimality-free core lemma, not the minimality steps.

Reproduce with `bash run_all.sh wave1` then `bash run_all.sh wave2` (about 3 and 3.5 minutes wall on
the shared 18-core machine). Final runs: 2026-10-05 02:03-02:10 EDT, all exit 0, RESULT: PASS.

**A.1 `check_identities.py`** (seed 31337, 24 s). 159 random C1 instances, s = 5 to 8, D_U ∈ {0, 1},
W-degrees in [3, 6] or [4, 6]. For every port y, every cut S = A ∪ C ⊆ V − y (all 2^{2s} cuts for
s ≤ 7; 20,000 random cuts per port for s = 8):

| Identity | Checks | Mismatches |
|---|---|---|
| I1: σ = e(A, U − C) − 4k = 2k − D_A + ε, ε from its definition (Lemma 1.4, 3.1) | 6,158,304 cuts, plus 23,220 recomputed by explicit loops | 0 |
| I2: g(V − S) = 6 + 2D_U + 2k + 2σ − 2D(C) (Lemma 3.1) | 6,158,304 | 0 |
| I3: κ(V − S) = k − 1 | 6,158,304 | 0 |
| I4: minimum slack = maxflow(G − y) − 4s (exhaustive cuts, s ≤ 7) | 663 ports | 0 |
| I5: a violation with g(V − S) ≥ 10 has D_U = 1, k = 2, σ = −1, u1 ∉ C, g = 10, κ = 1 (Lemma 3.2) | 17 of 100 violations | 0 |
| J1: g(A ∪ B) + g(A ∩ B) = g(A) + g(B) − 2e(A − B, B − A) (Identity 1.2) | 47,700 pairs | 0 |
| J2: g = 2D^S(S_W) + 6κ and D^S(S_U) − D^S(S_W) = 6κ (Identity 1.1) | 95,400 sets | 0 |
| J3: f(S) = g(S)/2 − k(S) − D(S_W), f submodular (hint H3) | 95,400 sets, 47,700 pairs | 0 |
| J4: g(S − v) = g(S) − 6 + 2deg_S(v) (Identity 1.3) | 644,046 | 0 |
| J5: g(V) = 6 + 2D_U, g(V − v) = 2D_U + 2deg(v) | 2,149 | 0 |
| J6: g = 2d + 6j, and g ≤ 8 forces (j, d) ∈ {(0, ≤ 4), (1, ≤ 1)} (Lemma 2.1) | 95,379 | 0 |

Violation profile (k, σ, g(V − S), D(C)) in these non-minimal instances: (2, −1, 10, 0) 17 times,
(1, −1, 8, 0) 41, (1, −1, 6, 0) 32, (2, −1, 8, 0) 7, (2, −2, 8, 0) 3. So the other violation
types do occur when the instance is not sparse; Lemma 2.1 is what removes them.

**A.2 `check_core.py 7 100`** (12.5 s). Exhaustive classes from genbg 2.9.3 (SHA-256 502f5f46...):
C1 is `genbg -q -d5:4 -D6:6 s s+1 6s−1:6s−1` (exactly one U-vertex of degree 5, W-degrees ≥ 4), C0 is
`-d6:4 -D6:6 s s+1 6s:6s`. Sparsity by enumerating all subsets.

| s | C1 graphs | sparse | C0 graphs | sparse | bad ports | SAT: quartic subgraph |
|---|---|---|---|---|---|---|
| 5 | 1 | 1 | 1 | 1 | 0 | all |
| 6 | 8 | 8 | 4 | 1 | 0 | all |
| 7 | 518 | 518 | 70 | 11 | 0 | all |
| 8, slice `0/100` | 1,797 | not computed | 136 | not computed | 0 | not run |

No port is bad at these sizes, so Lemma 4.4 is vacuous here; the SAT column is a small replication
of what F2 already covers.

**A.3 `check_subcase.py`** (seed 990011; six chunks, at most 174 s each). 46 built C1 instances with
an actual sub-case violation: 13 with ε = 0 and deg y = 4, 16 with ε = 0 and two degree-5 ports in
W − A, 17 with ε = 1; c = |C'| ∈ {4, 5, 6}, t = |U − C'| ∈ {7, 8, 9}; at most 3 T-edges per vertex
(2 at u1), as in a minimal counterexample.

| Item | Checks | Failures |
|---|---|---|
| S1: C1 with D_U = 1, D_W = 7; slack of (A, C') in G − y is −1; maxflow = 4s − 1 | 46 | 0 |
| S2: 7 + ε boundary edges; g(P1) = 10, g(P2) = 12 + 2ε, κ(P1) = 1, u1 ∈ P1; in-P1 deficiencies 2 and 8 | 46 | 0 |
| S3: trace identity (H4) on SAT witnesses H, one per realizable boundary subset | 720 witnesses: types (0,0) 16, (4,0) 536, (1,1) 42, (5,1) 126 | 0 |
| S4: gluing: G has H with H ∩ ∂ = τ iff P1 and P2 both realize τ (τ = ∅: iff P1 or P2 has one) | 2,816 traces on 16 instances | 0 |
| S5: P2 + β has 3n − 2 − ε edges; ε = 1 signed list has 6c + 7 = 3n − 2 elements, SAT finds a zero-sum sublist, read back as a realization in P2 (H6, H7) | 46; 17 (solutions (4,0) 13, (1,1) 2, (5,1) 2; with β forced in: SAT 17 of 17) | 0 |
| S6: P1 + α_τ in E4 for distinct-endpoint 4-traces (H5) | 729 | 0 |
| S7: P1 + uw' in C1(t − 1) for (1,1)-traces with u ≁ w' (H8) | 62 (57 adjacent pairs skipped) | 0 |
| S8: P1 + a and P1 − x deficiencies (H9) | 330 and 369 | 0 |
| S9: P1 + α (signed when ε = 1) is 1 + ε elements above Olson's threshold | 46 | 0 |
| S10: at every bad port, the min-cut petal satisfies Lemma 3.1 and has the Lemma 3.2 data | 62 bad ports, all tight; 16 pairs | 0 |
| S11: exact sparsity (max-closure flows, `min_g_proper`) and Lemma 4.4 | 6 instances, all sparse (min g = 10) | 0 |

**A.4 `check_sparse_core.py`** (six chunks, 200 s budget each). 24 further built instances (8 with two
degree-5 ports in W − A, 9 with ε = 1, 7 with deg y = 4; c ∈ {4, 5, 6}, t ∈ {8, 9, 10}). All 24 are
exactly sparse (min over proper sets with at least 2 vertices of g is 10, by flows), so Lemma 4.4
applies, and it holds in all 24: the bad ports are y alone (deficiency 1 or 2) or y and the second
degree-5 port of W − A (deficiency 1 + 1, one common petal); every petal, and their union, is in 𝒫.

**A.5 `check_lattice_pairs.py 0|1|2`** (about 1 s each). 571 built instances; at every bad port the
minimal and maximal minimum cuts coincide, so this builder never produces two distinct petals.
Lemma 4.2 is therefore exercised only through its arithmetic (J1, J2, I3), not on distinct petals.

**A.6 `check_adversarial.py 200`** (seed 4417, 200 s budget). 145,753 random C1 and C0 instances,
s = 6 to 10, W-degrees from 1, 2 or 3 up to 6; 10,168 of them have every port bad (by s and D_U:
s = 6: 1,895 and 721; s = 7: 1,624 and 605; s = 8: 1,455 and 525; s = 9: 1,257 and 461; s = 10:
1,176 and 449, for D_U = 1 and 0). In each, the proof chain was run on one min-cut petal per port; it
broke at the first premise (some petal with g ≤ 8, Lemma 3.2) in all 10,168, and in none did every
named set have g ≥ 10, which would have refuted Theorem 4.3.

**Script hashes (SHA-256, first and last 8 hex digits)** at the final runs: `c1common.py`
9e252d96...b2f9e574, `c1build.py` c8654286...448b20f8, `check_identities.py` 6acbf9b5...7438a68d,
`check_core.py` 7c10faa3...5f0b760a, `check_subcase.py` 50846a60...90925d8b, `check_sparse_core.py`
9e1173c9...82b48f3b, `check_lattice_pairs.py` 37556e04...69587c69, `check_adversarial.py`
80e034e2...c23fe6fc, `run_all.sh` 0b9d546e...54d633f2.

**Not covered by computation.** Lemma 2.1 and the uses of minimality in Lemmas 3.2, 4.1 and 4.2 can
only be checked on paper: they say a minimal counterexample would contain a smaller one, and there is
no counterexample to run them on. What the checks do cover: every identity those proofs use, the
minimality-free core lemma (Lemma 4.4) on 24 exactly sparse built instances with bad ports, and,
adversarially, that in 10,168 random instances in which every port is bad the chain always breaks at
a named sparsity premise.

## Appendix B. Sources (paths relative to the repository root)

- `reports/585-next/G110/PAPER.md` (SHA-256 cfce4fcc...6ab0c9, frozen, refereed): classes and gadget
  (lines 53-60), flow criterion Lemma 0.1 (87-102), Olson Lemma 0.2 (104-122), E3 reduction (141-157),
  C1 sub-case remark §4.4 (573-590), what was not proved (592-606).
- `reports/585-next/G110/REVIEW.md`: summary (10-27), §0.1-§4 ACCEPT, overall verdict (269-).
- `reports/585-next/G110/CORRECTIONS.md`: census table and the bounds m ≤ 59, m ≤ 62 (lines 9-22).
- `reports/585-next/G110/FLAW.md`: the unsigned P2 + β count 3n − 3 when ε = 1.
- `reports/585-fable-wildcard/lanes/quartic-subgraph/REPORT.md`: P_c (line 136), Lemma 1 Tutte
  (140-158), Lemma 2 budget identity (160-180), Lemma 4 (196-204), Theorem 5 (205-221; c = 2 at 212),
  §5.1 classes, criterion and reductions (236-267; E4 at 254, the sub-case at 259-265).
- `reports/585-fable-wildcard/reviews/QUARTIC-REVIEW.md`: summary table (lines 19-20), Lemma 4 item
  (82-104), reductions re-derived (206-231; E4 at 211-212), "P_2 holds if C1 holds" (233-238), the
  sub-case statement (240-246) and partial progress (252-277).
- `reports/585-next/STATE.md` and `reports/585-next/census/CENSUS.md`: F1, F2 and C0 census status
  (used only in Corollary 0.1's table, through CORRECTIONS.md).
- Olson, J. Number Theory 1 (1969) 8-10, through PAPER.md Lemma 0.2 (not re-fetched).
