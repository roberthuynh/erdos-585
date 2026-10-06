> Lead's note, added after the review (2026-10-05): this lane was launched with the Fable 5.1 model override, but its transcript shows every call on claude-opus-5-5. Both C1 referees ran on Opus 5.5, in fresh contexts with their own code. The sentence near the end about "different models" is wrong on that point; the review itself is unchanged.

# Referee 2 review of G110/C1-PAPER.md (the petal lattice closes C1)

Second independent referee, wave 3, step A2. October 5, 2026.

- Reviewed file: `reports/585-next/G110/C1-PAPER.md`, SHA-256
  `3c67d183d93b8bb512dba6e46656dc6e11991bb5e29f2b22ff3f37e5dd960cf8`, checked at the start and at
  the end of this review (see section 7). Not edited. Read together with `G110/C1-CORRECTIONS.md`
  (fix R1).
- Background read: `585-fable-wildcard/lanes/quartic-subgraph/REPORT.md` (section 5: Lemmas 1, 2, 4,
  Theorem 5, section 5.1), `585-fable-wildcard/reviews/QUARTIC-REVIEW.md`, and the cited parts of
  `G110/PAPER.md` (section 0.1) and `G110/CORRECTIONS.md`.
- Method. I re-derived every step of sections 1 to 5 and 5.4 by hand before opening the first review
  (`G110/C1-REVIEW.md`) or the author's checks (`G110/c1checks/`). I wrote my own code under
  `wave3/ref2/`; it imports nothing from `c1checks/`, `checks/`, `review/` or `review-c1/`.
  Sections 0 to 5 were written before I read C1-REVIEW.md. After reading it I only added the counts
  of four tallied reruns to section 3 (seeds 31 to 33 and 41), restated the Corollary 5.3 row in the
  ACCEPT WITH FIXES format, and sharpened the A.5 remarks in 2.6 and F5. No verdict changed.
  Section 6 compares the two reviews.
- Rung. Theorem 4.3 and its corollaries are written proofs (rung (a) claims), with no Lean and no
  `check.sh` run, so none of this is a project oracle PASS. The paper says the same.

## 0. Verdicts at a glance

| Item | Verdict |
|---|---|
| Identities 1.1, 1.2, 1.3 | ACCEPT |
| Lemma 1.4 (flow criterion, slack formula) | ACCEPT |
| Lemma 1.5 (E4 reduction) | ACCEPT |
| Minimality setup (M) and its well-foundedness | ACCEPT |
| Lemma 2.1 (sparsity) | ACCEPT |
| Basic counts (section 2) | ACCEPT |
| Lemma 3.1 (cut identity) | ACCEPT |
| Lemma 3.2 (petal lemma) | ACCEPT |
| Lemma 4.1 | ACCEPT |
| Lemma 4.2 (lattice) | ACCEPT (in a sparse instance the family is even a chain; own proof in 2.6) |
| Theorem 4.3 (C1 holds) | ACCEPT |
| Lemma 4.4 (minimality-free core) | ACCEPT |
| Corollary 5.1 (C0, G110-quartic) | ACCEPT |
| Corollary 5.2 (E4, E3) | ACCEPT |
| Corollary 5.3 (QB(4), and QB(4) ⟺ C1) | ACCEPT WITH FIXES: the statement and proof are correct; the remark right after it (line 242) needs F1 = R1, insert "bipartite" |
| Section 5.4 (REPORT.md Theorem 5, c = 2) | ACCEPT (optional: the bound w(C) ≥ 3 can read ≥ 4) |
| Corollary 5.4 (P_2) | ACCEPT |
| Corollary 0.1 | ACCEPT |
| Section 6 (hints table) | ACCEPT |
| Section 7, Appendix A text | ACCEPT (one optional wording note on A.6; I did not re-run Appendix A and replaced it with my own computations) |

**Overall: ACCEPT WITH FIXES.** I found no mathematical error and no gap. The one required fix is
R1 (one missing word at line 242), as in C1-CORRECTIONS.md. The other notes are optional.

## 1. The six briefed attack points

### 1.1 Well-foundedness of the minimality setup (section 2, (M))

What could go wrong: a circular induction (E4 at size s used to prove C1 at size s, while E4 at
size s needs C1 at size s), or an orientation mismatch (a C1 piece whose smaller side is a part of W).

What I checked:
- The induction hypothesis is only "C1 at sizes 1, ..., s − 1". E4 never enters as a hypothesis.
  E4(a) for a ≤ s is derived from C1 at sizes at most a − 1 ≤ s − 1 by Lemma 1.5, so there is no
  cycle. The derivation does not need anything at size s.
- Lemma 1.5 re-derived: D_A ≤ D_P ≤ 4 with D_A ≥ 2k + 1 + ε forces k = 1 and ε ≤ 1. The piece
  H[A ∪ C] has smaller side C with in-piece deficiency D_C + e(C, P − A) = ε ≤ 1. The piece
  H[(P − A) ∪ (Q − C)] has smaller side P − A with in-piece deficiency
  (D_P − D_A) + e(P − A, C) ≤ (1 − ε) + ε = 1. Sizes |C| and a − 1 − |C|. Both zero forces a = 1, and
  E4(1) is empty (each side has deficiency at least 5). So a positive piece has size between 1 and
  a − 1.
- Orientation. A C1(a) instance is a bipartite graph whose two sides have sizes a and a + 1, with
  the smaller side of deficiency at most 1. Because the side sizes differ, the designated side is
  forced, and minimality ranges over all such graphs. So it does not matter whether the smaller side
  of a piece is a subset of U or of W. Lemma 1.5 itself produces pieces of both orientations.
- Degenerate sizes: C1(s) is nonempty only for s ≥ 5, and E4(a) only for a ≥ 6
  (6a − 4 ≤ a²). Nothing small slips through.

Verdict: the setup is well-founded. ACCEPT.

### 1.2 Lemma 2.1 (sparsity)

- Identity 1.1 at S gives g(S) = 2d + 6j, with j the side-size difference of G[S] and d the in-S
  deficiency of its smaller side. So g(S) ≤ 8 forces (j, d) = (0, ≤ 4) or (1, ≤ 1). This covers
  g ≤ 4 too.
- j = 0: G[S] is balanced with sides of size a = |S|/2, 1 ≤ a ≤ s, and both sides have in-S
  deficiency 6a − e(S) = d ≤ 4. So G[S] ∈ E4(a), covered by (M).
- j = 1: |S| is odd with 3 ≤ |S| ≤ 2s − 1, so 1 ≤ a ≤ s − 1, and G[S] ∈ C1(a), covered by (M).
- The only same-size case is S = V − w with w ∈ W (an E4(s) instance). S = V − u with u ∈ U has
  j = 2. (M) covers E4(s), so the "same size" case is handled.
- G[S] is simple, bipartite with the inherited sides, and has Δ ≤ 6. g is even. So g(S) ≥ 10.

Verdict: ACCEPT. Every proper S with |S| ≥ 2 and g(S) ≤ 8 is a covered instance (smaller, or E4
at the same size, which (M) covers).

### 1.3 Lemma 3.2 (the rigid shape)

Re-derived in full:
- G − y has s ≥ 1 vertices per side, and a spanning 4-regular subgraph of it would be a quartic
  subgraph of G, so Lemma 1.4 gives a violation. Every violation has k ≥ 1 and D_A ≥ 2k + 1 + ε.
- D_A ≤ D_W − def(y) ≤ (6 + D_U) − 1 ≤ 6, so k ≤ 2.
- U − C ≠ ∅, since C = U would need |A| = s + k > s = |W − y|. So Q = V − S contains y and a
  U-vertex (|Q| ≥ 2), and Q ≠ V because A ≠ ∅. Lemma 2.1 gives g(Q) ≥ 10.
- Lemma 3.1 (algebra re-derived: e(G[Q]) = Σ_{U−C} deg − e(A, U − C) with
  e(A, U − C) = σ + 4k = 6k − D_A + ε, and |Q| = 2s + 1 − 2|C| − k) gives
  g(Q) = 6 + 2D_U − 2D(C) + 2k + 2σ, so k + σ ≥ 2 − D_U + D(C).
- With σ ≤ −1 and k ≤ 2: D_U ≥ 1 + D(C). Hence D_U = 1, D(C) = 0 (u1 ∉ C), k = 2, σ = −1,
  D_A = 5 + ε, ε = e(C, W − A) ≤ 1, g(Q) = 10, κ(Q) = 1, y ∈ Q, u1 ∈ U − C ⊆ Q.

The ε in Lemma 3.1 is computed in G − y: D^{G−y}(C) = D(C) + e(y, C), so
ε = D(C) + e(C, W − A). This is right, and A-vertices keep their G-degrees because y ∈ W.

Verdict: ACCEPT. Computation: Lemma 3.1 on 530,960 cuts (Python), and on every violation that
`r2sub viol` enumerates (an internal assertion in C). Lemma 3.2's conclusion was checked on every
violation at every bad port of every exactly sparse built instance (section 3).

### 1.4 Lemmas 4.1 and 4.2 (three neighbors, overlap, Q ∪ Q' ≠ V, uncrossing)

- 4.1(1): κ(Q) = 1 and Q ≠ {u1} give |Q_W| ≥ 1 and |Q| = 2|Q_W| + 1 ≥ 3.
- 4.1(2): D^Q(Q_W) = (g − 6κ)/2 = 2, and D(Q_W) ≤ D^Q(Q_W).
- 4.1(3): Q − u1 is proper with |Q − u1| ≥ 2. Identity 1.3 gives
  g(Q − u1) = 4 + 2deg_Q(u1) ≥ 10, so deg_Q(u1) ≥ 3.
- 4.2(a): u1 ∈ Q ∩ Q'. If Q ∩ Q' = {u1}, the neighbors of u1 in Q and in Q' lie in the disjoint sets
  Q − u1 and Q' − u1, so deg u1 ≥ 6 > 5.
- 4.2(b): κ is modular and κ(V) = −1, so Q ∪ Q' = V forces κ(Q ∩ Q') = 3. Then g(Q ∩ Q') ≥ 18
  (Identity 1.1), while g(Q ∩ Q') ≤ g(Q) + g(Q') − g(V) = 12. (This needs g(V) = 8, that is
  D_U = 1, which Lemma 3.2 has already established.)
- 4.2(c): both sets are proper with at least 2 vertices, so both have g ≥ 10. Their g-sum is at most
  20, so both equal 10 (and e(Q − Q', Q' − Q) = 0). g = 10 forces κ ≤ 1, and the κ-sum is 2, so both
  have κ = 1.

Verdict: ACCEPT.

Remark (not a defect): in a sparse instance with D_U = 1 the family 𝒫 is a chain, so the
incomparable case of Lemma 4.2 never occurs. My proof (written before I read C1-REVIEW.md) is in
section 2.6. It uses Lemma 4.2's union closure, so the lemma is still needed.

### 1.5 The final count over every deficiency pattern of W

R_p, the union of one petal per port, is in 𝒫 by Lemma 4.2 and induction. It contains every port,
and non-ports have deficiency 0, so D(R_p ∩ W) = D_W = 7. Lemma 4.1(2) bounds this by 2. The count
uses only "every port lies in some petal", so it does not depend on how the 7 units are spread
(4 to 7 ports, each of deficiency 1 or 2, since every W-degree is at least 4 by the basic counts).
Every port has a petal, because a quartic-free G gives a G − y with no 4-factor for every y ∈ W.

Verdict: ACCEPT. The minimality-free form (Lemma 4.4) was tested on 1,724 exactly sparse instances
with bad ports (section 3): in every one the bad ports carry total deficiency 1 or 2, never more.

### 1.6 The corollaries, and P_2 through REPORT.md Theorem 5 (c = 2)

- Cor 5.1: C0 ⊆ C1. For a simple bipartite 6-regular B and a vertex o, the side of o minus o has
  m = N − 1 ≥ 5 vertices of degree 6, and the other side has m + 1 vertices (six of degree 5). So B − o
  is a C0(m) instance. ACCEPT.
- Cor 5.2: Lemma 1.5 with Theorem 4.3; E3 ⊆ E4. ACCEPT.
- Cor 5.3: deleting edges to e = 3n − 4 keeps n and Δ ≤ 6. For any bipartition of H, Identity 1.1
  at S = V gives 8 = 2d + 6j, so H ∈ E4(n/2) or H ∈ C1((n − 1)/2), of size at least 1. Conversely a
  C1(s) instance has e = 6s − D_U ≥ 3n − 4. ACCEPT. The remark at line 242 needs R1 (item F1 below).
- Section 5.4, re-derived independently of REPORT.md. Minimal (n, then e) counterexample to P_2.
  Every P_2 instance has n ≥ 7 (3n − 2 ≤ n(n − 1)/2). e = 3n − 2 and δ ≥ 4 by minimality, so D = 4.
  There is no spanning 4-factor, so there is a barrier with δ ≤ −2 (the Belck-Tutte ℓ-factor
  criterion with ℓ = 4, as cited after QUARTIC-REVIEW item 1; δ is even). I re-derived the budget
  identity: (*), (**), 2(*) + (**), then substitute D_S = D − D_T − Σ D_C. It gives
  3δ + 8 = 2e(S) + 4e(T) + 4D_T + Σ w(C) ≥ 0, so δ = −2 and the right side is 2.
  For a component with |C| ≥ 2, REPORT.md Lemma 4 (c = 2) applies, because C is proper (a barrier
  has |S| > |T| ≥ 0 by (**)). It gives D_C + e(C,S) + e(C,T) ≥ 6, so w(C) ≥ 4 (≥ 3 as written is
  also enough). A singleton has w = 12 − a − 3[a odd] ≥ 4. So R = ∅, e(S) = 1, e(T) = 0 and
  D_T = 0, and (**) gives −2 = 4(|T| − |S|) + 2, that is |S| = |T| + 1. Then G − f ∈ C0(|T|), with
  |T| ≥ 1 because n ≥ 2. ACCEPT.
- Cor 5.4: Cor 0.1 with C0 at every size (Cor 5.1). ACCEPT.
- Cor 0.1: n = 2|T| + 1 ≤ 2M + 2 gives |T| ≤ M; the table's 84, 120 and 126 follow from M = 41, 59
  and 62. ACCEPT (the C0 ranges themselves are reviewed results, not re-checked here).

## 2. Other items

### 2.1 Identities 1.1 to 1.3

All re-derived. Every edge of G[S] has one end in S_U and one in S_W, so
D^S(S_U) = 6|S_U| − e(S) and D^S(S_W) = 6|S_W| − e(S). Identity 1.2 follows from
e(A ∪ B) + e(A ∩ B) = e(A) + e(B) + e(A − B, B − A). Identity 1.3 is immediate. ACCEPT.

A useful companion identity, not stated in the paper: g(X) = D(X) + ∂(X), where
∂(X) = e(X, V − X). It follows from the degree sum 6|X| − D(X) = 2e(X) + ∂(X), and it is the
quantity D_U + e(U, V − U) of REPORT.md Lemma 4. It gives a one-line proof of the chain property
(2.6).

### 2.2 Lemma 1.4

The cut with source side {s} ∪ A ∪ C has capacity 4s + e(A, Q − C) − 4(|A| − |C|), and every s-t cut
has this form. With Δ ≤ 6: e(A, Q − C) = (6|A| − D_A) − (6|C| − D_C − e(P − A, C)). The slack is at
least −4k, so a violation has k ≥ 1. ACCEPT. My check (I6): the minimum slack over all cuts equals
maxflow − 4s on 140 ports (exhaustive).

### 2.3 Basic counts

e = 6s − D_U, D_W = 6 + D_U, g(V) = 6 + 2D_U, g(V − w) = 2D_U + 2deg w ≥ 10. ACCEPT.

### 2.4 Theorem 4.3

It assembles the lemmas as described in 1.3 to 1.5. ACCEPT.

### 2.5 Lemma 4.4

The proofs of Lemmas 3.2, 4.1 and 4.2 use minimality only through Lemma 2.1. Lemma 3.2 also needs a
violation at y, which is what "bad" means. With D_U = 0, Lemma 3.2's chain gives a contradiction at
any bad port, so there is none. With D_U = 1, every complement of a violation at a bad port is in 𝒫,
their union is in 𝒫, and so the bad ports carry deficiency at most 2. ACCEPT.

### 2.6 Own proof that 𝒫 is a chain (sparse instance, D_U = 1)

Let Q, Q' ∈ 𝒫 be incomparable, J = Q ∪ Q' (in 𝒫 by Lemma 4.2), X = Q − Q' and Y = Q' − Q. Both
are nonempty. κ(X) = κ(Q) − κ(Q ∩ Q') = 0, so |X| ≥ 2, and likewise |Y| ≥ 2. Also u1 ∉ X ∪ Y.

- Identity 1.2 with the disjoint sets J − X = Q' and X gives g(J) = g(Q') + g(X) − 2e(X, J − X).
  Since g(J) = g(Q') = 10, g(X) = 2e(X, J − X).
- With g(X) = D(X) + e(X, J − X) + e(X, V − J), this gives g(X) = 2D(X) + 2e(X, V − J).
- Sparsity gives g(X) ≥ 10, so D(X) + e(X, V − J) ≥ 5. The same holds for Y, so the sum is at
  least 10.
- But D(X) + D(Y) ≤ D(J ∩ W) (only u1 has U-deficiency), and
  e(X, V − J) + e(Y, V − J) ≤ ∂(J). With g(J) = D(J) + ∂(J) and D(J ∩ U) = 1 (u1 ∈ J),
  D(J ∩ W) + ∂(J) = 10 − 1 = 9 < 10. Contradiction. ∎

So two incomparable petals can never occur, which accounts for part of the author's observation in
A.5. The chain property alone does not rule out two nested petals at one port. In a sparse instance
every member of 𝒫 that contains a port y is the complement of a violation at y: κ = 1 gives k = 2,
and Lemma 3.1 with D(C) = 0 gives σ = −1. In my builder each bad port had exactly one violation
(seeds 31 to 33: 1,003 bad ports, 1,003 violations), so each bad port lies in exactly one member.
Two members of 𝒫 did occur (27 instances), always nested, and the smaller one contained no port.
This was checked in the 16 tallied instances and the 2 inspected ones.

### 2.7 Section 6 (hints)

I re-checked H1 to H10 against their stated justifications:
- H2: g(P2) = g(V) + 2∂(P2) − g(P1) = 8 + 2(7 + ε) − 10.
- H3: f = g/2 − k − D(S_W), and f is submodular.
- H4: x − x' = 4(|V(H) ∩ A| − |V(H) ∩ C'|).
- H5 and H9: the deficiency counts (2 + 2 and 8 − 4; 8 − s(a); 8 − def(x) − r(x)).
- H6: 6c + 7 = 3(2c + 3) − 2.
- H7: (6c − 1) + 7 + 1 = 3(2c + 2) + 1, together with the per-coordinate bounds.
- H8: W-side deficiency 1, Δ ≤ 6, simple.
- H10: 4 to 7 ports, since every port has deficiency 1 or 2.

None of these is used by Theorem 4.3. ACCEPT.

### 2.8 Section 7 and Appendix A

Section 7 is accurate: P_3 and P_4 stay open, and C2/E5 is not attempted. I did not re-run Appendix A;
section 3 replaces it with independent code. One optional wording note (F4 below).

## 3. Own computations (all exit 0, all under `timeout 240`)

Interpreter `[temporary path]` (networkx, pysat CaDiCaL 1.5.3). C code
compiled with `/usr/bin/clang -O2`. The SAT decider forbids every incident pattern with a count
outside {0, 4} and re-validates every witness.

| Script | What | Result |
|---|---|---|
| `r2_identities.py 2718 40` | I1 Identity 1.1 incl. g = 2d + 6j (12,000 sets); I2 Identity 1.2 (12,000 pairs); I3 Identity 1.3 (77,912); I4 slack formula (530,960 cuts); I5 Lemma 3.1 g(Q), κ(Q) (530,960); I6 min slack = maxflow − 4s (140 ports, exhaustive); X1 `r2sub ming` = Python brute force = max-closure flows (25 instances); X2 `r2sub viol` = Python violation count and min slack (50 ports) | 0 mismatches |
| `r2_sparse_core.py SEED 200 build`, seeds 1, 11, 12, 13, 31, 32, 33 | own builder of C1 instances carrying a sub-case cut (k = 2, D_A = 5 + ε, u1 ∉ C', 7 T-edges, ≤ 3 per vertex); exact min g over all proper sets (C, all 2^n subsets, n = 23 to 27); bad ports by max flow; all violations at each bad port (C, all cuts); all of 𝒫 (C) with closure and chain tests; SAT | 1,768 built, 1,724 exactly sparse, all with bad ports; bad-port deficiency 1 (964) or 2 (760), never more; seeds 31 to 33 tallied 1,003 bad ports and 1,003 violations (exactly one per bad port); every violation has (k, σ, D(C), g, κ) = (2, −1, 0, 10, 1) with complement in 𝒫; union in 𝒫 with W-deficiency ≤ 2; 𝒫 closed under ∩, ∪; |𝒫| = 1 (1,697) or 2 (27, nested); 0 incomparable pairs; all quartic. 0 failures |
| `r2_sparse_core.py SEED 200 random`, seeds 21, 41 | random C1/C0 instances, s = 8 to 12 | 9,511 instances, 7,536 exactly sparse (4,753 with D_U = 1, 2,783 with D_U = 0); no bad port in any sparse one; 𝒫 empty in every sparse D_U = 1 one; all quartic. 0 failures |
| `r2_adversarial.py SEED 200 G1`, seeds 77, 78 | greedy maximal quartic-free bipartite graphs, Δ ≤ 6, sides p and p + {0, 1, 2}, n = 12 to 28 | 11,727 graphs; max e − 3n = −8 (never ≥ −4) |
| `r2_adversarial.py 77 200 G2` | random C1 and E4 instances, s = 8 to 30 | 53,431 instances, all quartic |
| `r2_adversarial.py 77 200 G3` | random general graphs with Δ ≤ 6 and e = 3n − 2 (n = 7 to 40), and the Theorem 5 shape (C0 plus one edge inside the larger side, s = 5 to 25) | 7,049 instances, all quartic |
| `r2_tutte.py 6 50` | Tutte form (lane form = textbook form), budget identity, and min δ ≥ 0 iff a spanning 4-factor exists (SAT), on random graphs with 4 ≤ deg ≤ 6, n = 7 to 9, all 3^n pairs | 437,400 pairs, 0 mismatches; 44 graphs with a 4-factor, 6 without, criterion agrees on all 50 |

The two nested pairs I inspected have the same shape: the smaller member is the larger one minus an
edge {x, w'}. Here w' is the degree-5 port of W − A when ε = 1 (P1-degree 4), and x ∈ U − C' has
three T-edges. The smaller member contains no port. This matches the arithmetic of 2.6 with
X = {x, w'}.

What the computations cannot do: they cannot exercise the minimality steps (Lemma 2.1 and its uses),
because no counterexample exists if the theorem holds. They test every identity, the
minimality-free core (Lemma 4.4) on 1,724 exactly sparse instances with bad ports, the chain property,
and the conclusions directly on about 83,000 instances. The minimality steps were checked by hand
(1.1, 1.2).

## 4. Fixes

Required:
- **F1 (= R1 of C1-CORRECTIONS.md).** Line 242: "So F2(N) (CORRECTIONS.md table: δ ≥ 4, Δ ≤ 6,
  e ≥ 3n − 4 implies ...)" leaves out "bipartite". F2 in G110/CORRECTIONS.md is the bipartite
  statement. Read literally, the line asserts REPORT.md question (i) (P_4 with δ ≥ 4), which is
  open. Insert "bipartite". No statement or proof changes.

Optional:
- **F2.** Line 22: "the unique degree-5 vertex u1 of the saturated side". With D_U = 1, U is not
  saturated. Say "of the smaller side U".
- **F3.** Section 5.4: "w(C) ≥ 3" can read "w(C) ≥ 4". When e(C, S) is odd, D_C + e(C, T) is odd,
  so w ≥ 6 + 1 − 3. Both bounds suffice for budget 2.
- **F4.** A.6: "which would have refuted Theorem 4.3". An instance with every port bad and every
  named set of g ≥ 10 would refute Lemma 4.4, and so the proof, but not the theorem directly,
  because "every port bad" does not imply quartic-free. Say "would have refuted Lemma 4.4".
- **F5.** After Lemma 4.2, one sentence could add that in a sparse instance 𝒫 is a chain (2.6), so
  incomparable petals never occur. A.5 saw none. Nothing in the proof changes.

## 5. Overall verdict

**ACCEPT WITH FIXES (F1 required, wording only).** I re-derived Theorem 4.3 (C1 holds) and found it
correct. Its corollaries C0, E3, E4, G110-quartic, QB(4) and P_2 follow as stated. The
well-foundedness is sound: E4 is derived, not assumed, at size s. Lemma 2.1 covers every proper
dense set, and the same-size case S = V − w is covered by (M). Lemma 3.2 forces the rigid shape at
every port. Lemma 4.2 holds; the family is in fact a chain. The final count is independent of the
deficiency pattern. P_2 uses REPORT.md Theorem 5 only for c = 2, which I re-derived. No fatal gap.

## 6. Comparison with C1-REVIEW.md

Written after sections 0 to 5 were on disk. I read C1-REVIEW.md (lane M3-R, FINAL) once, at this
point. I did not open the author's `c1checks/` or the first referee's `review-c1/` code.

**Verdicts: identical.** Both reviews ACCEPT every lemma, Theorem 4.3 and every corollary. Both
require only R1 (line 242, "bipartite") and find no fatal gap. Neither review is a project-oracle
PASS: there is no Lean and no `check.sh`, and both checked the minimality steps on paper only.

**Points both reached independently.**
- Well-foundedness: E4 at size s is derived from C1 below s, and the class is orientation-free
  because the smaller side is determined. Lemma 2.1's same-size case is exactly S = V − w (w ∈ W).
  The C0 case is excluded inside Lemma 3.2 (with D_U = 0, g(Q) = 6 + 2k + 2σ ≤ 8).
- The final count does not depend on the deficiency pattern of W.
- w(C) ≥ 4 in section 5.4 (their N1, my F3). Not needed.
- **The chain property.** Both reviews prove that in a sparse instance 𝒫 is a chain (their N4, my
  2.6), with different arguments:
  - Theirs works at the intersection Q0 = Q ∩ Q'. From g(X) = 2e(Q0, X) ≥ 10 and the same for Y,
    10 ≤ e(Q0, X ∪ Y) ≤ ∂(Q0) = 7 + ε0 ≤ 9.
  - Mine works at the union J = Q ∪ Q', via g = D + ∂. From g(X) = 2D(X) + 2e(X, V − J) ≥ 10 and
    the same for Y, 10 ≤ D(J ∩ W) + ∂(J) = 9.

  I checked their proof. It is valid: ∂(Q0) = (g(Q0) + g(V − Q0) − g(V))/2 = 7 + ε0, and
  ε0 = 2 − D(Q0 ∩ W) ≤ 2. The two proofs are dual (they bound the same deficit at the bottom and
  at the top of the pair), so the claim in the optional line of C1-CORRECTIONS.md now has two
  independent proofs.

**Points only the first review makes.**
- N2: Lemma 3.1 holds for any y ∈ W − A, so in a sparse instance the bad ports are exactly the
  ports that lie in some member of 𝒫. I agree. While designing my builder I derived the same fact
  in the form "members of 𝒫 are exactly the complements of cuts with k = 2, σ = −1 and u1 ∉ C,
  and σ does not depend on y ∉ A". It is not in my sections 0 to 5, and I endorse it as an optional
  remark.
- "Hypotheses shown to be needed": sparsity is needed for Lemma 3.2 and Lemma 4.2(c), and
  Lemma 4.2(b) needs none (it uses only g(Q) = g(Q') = 10 and g(V) = 8). I agree with all three and
  did not repeat them.
- Computation I did not do:
  - an exhaustive QB(4) census to n = 16 (genbg at e = 3n − 4, and geng -b to n = 14);
  - Lemma 1.5 on every violation of the exhaustive E4(6) and E4(7) classes;
  - 420 sparse built instances with two or three members of 𝒫 (all nested);
  - exact 𝒫 by min-cut closures, validated against brute force.

**Points only this review makes.**
- F2 (line 22 calls U "the saturated side" although D_U = 1) and F4 (A.6 says "would have refuted
  Theorem 4.3" where it means Lemma 4.4). Both are optional wording notes.
- The identity g(X) = D(X) + ∂(X), which shortens several steps (2.1).
- Computation the first review did not do:
  - every violation (all cuts, not only minimum cuts) at every bad port of 1,724 exactly sparse
    instances with n = 23 to 27, by brute force over all 2^n subsets;
  - SAT on random C1 and E4 instances up to s = 30 (the first review's random instances reach
    s = 14 and test the core lemma by flows; its exhaustive census reaches n = 16);
  - random general P_2 graphs, including the Theorem 5 shape;
  - greedy maximal quartic-free bipartite graphs to n = 28 (max e − 3n = −8);
  - the Tutte criterion against a SAT 4-factor decider (QUARTIC-REVIEW item 1 already did this with
    a gadget-matching decider, so this is a third check, not new coverage).

**Disagreements: none.** No item where one review accepts and the other rejects, and no conflicting
numbers. Both found 0 incomparable pairs of members of 𝒫. Both observe that random instances are
far from counterexamples (no bad port in any sparse random instance), so only built instances
exercise Lemma 4.4. Both observe that the minimality steps can only be checked on paper.

**Net.** Two referees on different models reached the same verdict by independent derivations and
independent code. This review adds no new required fix. The paper plus R1 stands as a rung (a)
written proof of Theorem 4.3, QB(4), C0, E3, E4, G110-quartic and P_2, pending formalization.

## 7. Hash check and reproduction

- Paper SHA-256 at start: `3c67d183d93b8bb512dba6e46656dc6e11991bb5e29f2b22ff3f37e5dd960cf8`.
- Paper SHA-256 at end (10:31 EDT): `3c67d183d93b8bb512dba6e46656dc6e11991bb5e29f2b22ff3f37e5dd960cf8`,
  equal to the start value and to `G110/C1-FROZEN.sha256`. The paper was not edited.
- Reproduce from `reports/585-next/wave3/ref2/`:
  - `/usr/bin/clang -O2 -o r2sub r2sub.c` (do not use `cc` in this shell; it is aliased).
  - `timeout 240 [temporary path] r2_identities.py 2718 40`
  - `timeout 240 [temporary path] r2_sparse_core.py 11 200 build`
    (likewise seeds 1, 12, 13, 31, 32, 33; and `21 200 random`, `41 200 random`)
  - `timeout 240 [temporary path] r2_adversarial.py 77 200 G1`
    (likewise `78 200 G1`, `77 200 G2`, `77 200 G3`)
  - `timeout 240 [temporary path] r2_tutte.py 6 50`
- Outputs: `out_identities.json`, `out_sparse_*.json`, `out_adv_*.json`, `out_tutte.json`,
  `run_*.txt`. The time-bounded scripts process a seed-determined sequence of instances, so counts
  can differ slightly between machines.
