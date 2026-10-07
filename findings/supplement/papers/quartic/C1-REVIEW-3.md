# Independent adversarial referee report on `G110/C1-PAPER.md`

Referee lane: wave4/c1-fable-ref (Fable). Date: 2026-10-05. Paper frozen at the SHA-256 in
`G110/C1-FROZEN.sha256`; checked `OK` at the start and at the end of this review (LOG.md). I did not
open `C1-REVIEW.md`, `C1-CORRECTIONS.md`, `review-c1/` or `wave3/ref2/` before writing the verdict in
§1 to §7; §8 (added last) compares with them. All code here is my own (`code/`), nothing reused
from `G110/c1checks` or `G110/checks`; nauty `genbg`/`geng` 2.9.3 are used only as generators.

## 1. FINAL verdict: ACCEPT WITH FIXES (one required wording fix, R1; no mathematical error)

**Required fix R1 (C1-PAPER.md line 242, the remark after Corollary 5.3; wording only).** The
paraphrase of F2(N) reads "δ ≥ 4, Δ ≤ 6, e ≥ 3n − 4 implies a 4-regular subgraph" and drops the word
"bipartite". CORRECTIONS.md lines 14-16 define F1 as "bipartite, δ ≥ 4, Δ ≤ 6, e ≥ 3n − 6" and F2 as
"same with e ≥ 3n − 4". Read literally, the remark asserts P_4 for all graphs with δ ≥ 4, which is
open (the paper's own §7 says so, and by peeling P_4 with δ ≥ 4 is P_4 itself). Insert "bipartite";
with it the remark follows from Corollary 5.3. No statement or proof changes.

Honesty note on provenance: my independent pass (§2-§7 below, written before I opened any other
review) found no required fix and would have returned plain ACCEPT. R1 was found by the first
referee (C1-REVIEW.md) and confirmed by the second (wave3/ref2); I checked it against the paper's
line 242 and CORRECTIONS.md's own text and agree it is required, because a stranger would read the
remark as a claim about all graphs. I missed it because I checked the remark's mathematics (true for
bipartite graphs) and not its paraphrase of the source word for word, which rule 8 of AGENTS.md asks
for. The verdict on every theorem, lemma and corollary is unchanged: ACCEPT.

Theorem 4.3 (every C1 instance has a 4-regular subgraph) is proved as written. I re-derived every
identity and every step of Lemmas 1.4, 1.5, 2.1, 3.1, 3.2, 4.1, 4.2, Theorem 4.3, Lemma 4.4 and
Corollaries 0.1 and 5.1 to 5.4, including the Tutte/budget-identity re-derivation of REPORT.md
Theorem 5 (c = 2) in §5.4 that carries P_2 to non-bipartite graphs. I found no false statement and
no gap. Every cited input says what the paper says it says (§4). My own code reproduces every
identity, the flow and Tutte criteria, the small exhaustive cases of the theorem, the P_2 statement
for n ≤ 10, and the minimality-free core (Lemma 4.4) on exactly sparse built instances (§5).

Apart from R1 above, §6 lists three optional clarifications of wording; none changes a statement
or a proof.

Rung, in the project's vocabulary: Theorem 4.3 and Corollaries 5.1 to 5.4 are rung (a) written
proofs, not Lean-checked; this review does not change that. Not a `check.sh` result.

## 2. What the proof rests on (my reconstruction)

The whole argument is: a minimal counterexample is *sparse* (Lemma 2.1: g(S) ≥ 10 on every proper
S with |S| ≥ 2), sparsity plus the cut identity (Lemma 3.1) forces every violation at every port
into one shape whose complement Q has g(Q) = 10, κ(Q) = 1 and contains the degree-5 vertex u1
(Lemma 3.2), such sets form a lattice under ∩, ∪ (Lemma 4.2, from submodularity of g and the degree
of u1), and the union of the petals of all ports is then one such set, whose W-side carries all 7
units of W-deficiency while any such set carries at most 2 (Lemma 4.1(2)). Minimality enters only
through Lemma 2.1; everything after it is arithmetic on g and κ.

## 3. Step-by-step re-derivation

Notation as in the paper: g(S) = 6|S| − 2e(S), κ(S) = |S_U| − |S_W|, D^S(Z) the deficiency of Z
inside G[S].

**Identity 1.1.** Every edge of G[S] has one end in each side, so e(S) = Σ_{S_U} deg_{G[S]} =
Σ_{S_W} deg_{G[S]}; hence D^S(S_U) = 6|S_U| − e(S), D^S(S_W) = 6|S_W| − e(S), g = D^S(S_U) +
D^S(S_W), and the difference is 6κ. Correct. With j = |κ| and d the smaller side's in-S
deficiency, g = 2d + 6j and the larger side has d + 6j. Correct.

**Identity 1.2.** e(A ∪ B) = e(A) + e(B) − e(A ∩ B) + e(A − B, B − A): edges with both ends in A ∪ B
are inside A, inside B (those inside A ∩ B counted twice), or between A − B and B − A. Correct; g
is submodular with defect 2e(A − B, B − A). **Identity 1.3.** Immediate. Correct.

**Lemma 1.4 (flow criterion).** Network source → p (cap 4), p → q (cap 1 per edge), q → sink
(cap 4); an integral flow of value 4s is a spanning 4-regular subgraph. A cut with source side
{source} ∪ A ∪ C (A ⊆ P, C ⊆ Q) has capacity 4|P − A| + e(A, Q − C) + 4|C| = 4s + (e(A, Q − C) −
4(|A| − |C|)), and every cut has this form. Degree count: e(A, Q − C) = Σ_A deg − e(A, C) = 6|A| −
D_A − (6|C| − D_C − e(P − A, C)) = 6k − D_A + ε. Slack 2k − D_A + ε. For k ≤ 0 the slack is
e(A, Q − C) − 4k ≥ 0, so a violation has k ≥ 1. Correct. (Checked by code against max flow, I4.)

**Lemma 1.5 (E4 → C1).** Violation: D_A ≥ 2k + 1 + ε, D_A ≤ D_P ≤ 4 gives k = 1, ε ≤ 1, D_A ≥
3 + ε. Piece H[A ∪ C]: sides |A| = |C| + 1 and C, and the in-piece deficiency of C is D_C +
e(C, P − A) = ε ≤ 1, so a C1(|C|) instance when |C| ≥ 1, a single vertex when |C| = 0. Piece
H[(P − A) ∪ (Q − C)]: |Q − C| = |P − A| + 1, in-piece deficiency of P − A is (D_P − D_A) +
e(P − A, C) ≤ (4 − 3 − ε) + ε = 1 since e(P − A, C) ≤ ε. Sizes |C| + (a − 1 − |C|) = a − 1.
Both zero forces a = 1 and E4(1) is empty (one vertex per side has degree ≤ 1). Correct.

**(M).** Minimality gives C1 below s. For E4(a), 1 ≤ a ≤ s: a 4-factor is a quartic subgraph;
otherwise Lemma 1.5 gives a C1 piece of positive size ≤ a − 1 ≤ s − 1 (a = 1 is empty). Correct.
This is what covers S = V − w (an E4(s) instance) in Lemma 2.1; the paper says so explicitly.

**Lemma 2.1 (sparsity).** Let 2 ≤ |S| ≤ 2s and g(S) ≤ 8 = 2d + 6j. j ≤ 1. If j = 0: G[S] is
balanced with sides of size a = |S|/2 ∈ [1, s], both of in-S deficiency d ≤ 4, Δ ≤ 6 as a
subgraph: an E4(a) instance, so (M) gives a quartic subgraph of G[S] ⊆ G. If j = 1: d ≤ 1; |S| is
odd, so 3 ≤ |S| ≤ 2s − 1 and the smaller side has size a = (|S| − 1)/2 ∈ [1, s − 1]; G[S] is a
C1(a) instance, and minimality gives a quartic subgraph. Both contradict G quartic-free. g is even,
so g(S) ≥ 10. Correct. (A quartic edge set of G[S] has the same degrees in G: its vertex degrees
depend only on the edge set.)

**Basic counts.** e = 6s − D_U, D_W = 6(s + 1) − e = 6 + D_U, g(V) = 6 + 2D_U; g(V − w) = 2D_U +
2deg(w) ≥ 10 for every W-vertex (|V − w| = 2s ≥ 2), so deg(w) ≥ 5 − D_U. Correct.

**Lemma 3.1 (cut identity), full expansion.** In G − y the A-degrees are G-degrees (A ⊆ W − y, no
W-W edges) and the deficiency of C is D(C) + e(y, C), so ε = D(C) + e(y, C) + e(W − y − A, C) =
D(C) + e(C, W − A). e(Q) = e(U − C, W − A) = Σ_{U−C} deg − e(A, U − C) = 6(s − |C|) − (D_U −
D(C)) − (6k − D_A + ε). With |Q| = 2s + 1 − 2|C| − k:
g(Q) = 6(2s + 1 − 2|C| − k) − 2[6s − 6|C| − D_U + D(C) − 6k + D_A − ε]
     = 6 + 6k + 2D_U − 2D(C) − 2D_A + 2ε = 6 + 2D_U − 2D(C) + 2k + 2σ,
using −2D_A + 2ε = 2σ − 4k. κ(Q) = (s − |C|) − (s + 1 − |C| − k) = k − 1. Correct. Note the proof
never uses that y is a port: the identity holds for every y ∈ W − A (see §7, observation 1).

**Lemma 3.2 (petal lemma).** G − y is balanced with sides of size s ≥ 1 and has no 4-factor (one
would be a quartic subgraph of G), so a violation exists; it has k ≥ 1, D_A ≥ 2k + 1 + ε. A ⊆ W − y
gives D_A ≤ D_W − def(y) ≤ 6 + D_U − 1 ≤ 6, so k ≤ 2. Q ∋ y and Q ⊇ U − C ≠ ∅ (C = U would need
|A| = s + k > s = |W − y|), so |Q| ≥ 2; A ≠ ∅ so Q ≠ V. Lemma 2.1: g(Q) ≥ 10, i.e. D_U + k + σ −
D(C) ≥ 2. With σ ≤ −1 and k ≤ 2: D_U ≥ 1 + D(C), so D_U = 1, D(C) = 0 (u1 ∉ C), k = 2; then σ ≥
2 − 1 + 0 − 2 = −1, so σ = −1, D_A = 2k − σ + ε = 5 + ε, ε ≤ 1, ε = e(C, W − A); g(Q) = 6 + 2 − 0 +
4 − 2 = 10, κ(Q) = 1, u1 ∈ U − C ⊆ Q. Correct in every clause.

**Lemma 4.1.** (1) κ(Q) = 1 and u1 ∈ Q: Q_W = ∅ would give Q = {u1}, |Q| = 1 < 2; so |Q| =
2|Q_W| + 1 ≥ 3. (2) D^Q(Q_W) = (g − 6κ)/2 = 2 and D(Q_W) ≤ D^Q(Q_W). (3) Q − u1 is proper with
≥ 2 vertices, so 10 ≤ g(Q − u1) = 10 − 6 + 2deg_{G[Q]}(u1), giving deg_{G[Q]}(u1) ≥ 3. Correct.

**Lemma 4.2 (lattice).** (a) If Q ∩ Q' = {u1}, the ≥ 3 neighbors of u1 in Q and the ≥ 3 in Q' lie
in the disjoint sets Q − u1, Q' − u1, so deg u1 ≥ 6, against deg u1 = 5. So |Q ∩ Q'| ≥ 2.
(b) If Q ∪ Q' = V: κ(Q ∩ Q') = 1 + 1 − κ(V) = 2 + 1 = 3, so g(Q ∩ Q') ≥ 18 by Identity 1.1, while
Identity 1.2 gives g(Q ∩ Q') ≤ 20 − g(V) = 20 − 8 = 12 (g(V) = 8 because D_U = 1, Lemma 3.2).
(c) Both Q ∩ Q' and Q ∪ Q' are proper with ≥ 2 vertices, so each has g ≥ 10, and their sum is ≤
20: both are 10 (and e(Q − Q', Q' − Q) = 0). κ(Q ∩ Q') + κ(Q ∪ Q') = 2; g = 10 forces 6κ ≤ 10,
κ ≤ 1; so both κ = 1. Both contain u1. Correct.

**Theorem 4.3 (the three-set count).** Ports exist (D_W = 7). Each port y has a petal Q_y ∈ 𝒫
(the complement of any violation of G − y, by Lemma 3.2). R_i = Q_{y_1} ∪ ... ∪ Q_{y_i} ∈ 𝒫 by
induction with Lemma 4.2. (R_p)_W contains every port; the W-vertices with positive deficiency are
exactly the ports, so D((R_p)_W) = D_W = 7; Lemma 4.1(2) gives D((R_p)_W) ≤ 2. Contradiction.
Correct. The only inputs are Lemma 3.2 (existence of petals, D_U = 1), Lemma 4.2 (closure under
union) and Lemma 4.1(2) (the bound 2); each is verified above.

**Lemma 4.4.** Lemmas 3.2, 4.1, 4.2 use minimality only through Lemma 2.1, and Lemma 3.2 uses the
existence of a violation, which is the definition of a bad port. For D_U = 0: a bad port's violation
has k ≤ 2 (D_A ≤ 5), σ ≤ −1, D(C) = 0, so g(Q) = 6 + 2k + 2σ ≤ 8 on a proper set with ≥ 2 vertices,
against sparsity. Correct. (Checked by code on 529 exactly sparse graphs at s ≤ 7 and on the built
instances of §5.)

**Corollary 5.1.** C0 ⊆ C1. For 6-regular bipartite B and any o: B − o has the side of o minus o
(m ≥ 5 vertices, all still of degree 6) and the other side (m + 1 vertices, degrees 5 or 6), Δ ≤ 6:
a C0(m) instance. PAPER.md lines 58-60 define a G110 gadget as exactly such a B − o. Correct.

**Corollary 5.2.** E4(a): a 4-factor, or by Lemma 1.5 a C1 piece of positive size (a ≥ 2; E4(1)
empty) with a quartic subgraph by Theorem 4.3. E3 ⊆ E4. Correct.

**Corollary 5.3 (QB(4)).** Deleting edges to e = 3n − 4 keeps Δ ≤ 6, n and the bipartition; g(V) =
8 = 2d + 6j for that bipartition, so (j, d) ∈ {(0, 4), (1, 1)}; j = 0 gives E4(n/2) with n/2 ≥ 1,
j = 1 gives n odd ≥ 3 and C1((n − 1)/2). A 4-regular subgraph of the pruned graph is one of H.
Converse: a C1(s) instance has e = 6s − D_U ≥ 6s − 1 = 3(2s + 1) − 4. Correct. (For n ≤ 10 the
hypothesis e ≥ 3n − 4 is unsatisfiable by a bipartite graph, so the small cases are vacuous; the
proof does not need this.)

**Corollary 0.1 and 5.4 (P_2).** A counterexample to P_2 with n minimal, then e minimal, has the
Theorem 5 (c = 2) form G = B + f, B bipartite with sides S, T, |S| = |T| + 1, T saturated, so B ∈
C0(|T|) with U = T; n = 2|T| + 1 ≤ 2M + 2 gives |T| ≤ M; B's 4-regular subgraph is one of G.
Correct. The table (n ≤ 84 / 120 / 126 from m ≤ 41 / 59 / 62) matches CORRECTIONS.md lines 9-22
and 2M + 2. Corollary 5.4 is Corollary 0.1 with Corollary 5.1 for every m. Correct.

**§5.4, the c = 2 case of REPORT.md Theorem 5, re-derived.** e = 3n − 2 (else delete an edge);
δ ≥ 4 (a vertex of degree ≤ 3 deleted leaves n − 1 ≥ 2 vertices and ≥ 3(n − 1) − 2 edges; n = 2
cannot carry e ≥ 4); D = 4; no 4-factor since no 4-regular subgraph. f = deg − 4 ≥ 0; a 4-factor is
the complement of an f-factor. Tutte: no f-factor iff some disjoint S, T have δ(S, T) = f(S) − f(T)
+ Σ_T deg_{G−S} − q(S, T) < 0, q counting components C of G − S − T with f(C) + e(C, T) odd; and
f(C) + e(C, T) ≡ Σ_C deg + e(C, T) = 2e(C) + e(C, S) + 2e(C, T) ≡ e(C, S), so q counts components
with e(C, S) odd; δ ≡ f(V) = 2e − 4n ≡ 0, so a barrier has δ ≤ −2. I derived the budget identity
myself: δ = Σ_S deg − 4|S| + 4|T| − e(S, T) − q = 4(|T| − |S|) + 2e(S) + e(S, R) − q, which is
(**); and 3δ + 2D = 2e(S) + 4e(T) + 4D_T + Σ_C w(C) with w(C) = 2D_C + e(C, S) + 2e(C, T) −
3[e(C, S) odd], exactly REPORT.md Lemma 2. Single vertex: w = 12 − a − 3[a odd] ≥ 4 (a ≤ 6). For
|C| ≥ 2: C is proper (S ≠ ∅ for a barrier, since (**) gives |S| > |T|), so by n-minimality e(C) ≤
3|C| − 3, i.e. m := D_C + e(C, S) + e(C, T) = 6|C| − 2e(C) ≥ 6, and w = 2m − e(C, S) − 3[odd] ≥
m − 3 ≥ 3 (as e(C, S) ≤ m). With δ = −2, D = 4 the left side is 2, so R = ∅, e(S) = 1, e(T) = 0,
D_T = 0, and (**) gives |S| = |T| + 1. Correct; this is the REPORT.md line 212 type verbatim.
(Checked by code: T1, T2 in §5.)

**§6 hints.** Not used by Theorem 4.3. I spot-checked H1 (d0 ≤ 5 from the average W-degree), H2
(g(S) + g(V − S) = g(V) + 2∂(S); e(P1) = 6t − 8 on 2t − 1 vertices gives g(P1) = 10; g(P2) =
12 + 2ε), H3 (f(S) = g(S)/2 − k(S) − D(S_W), expanded: both sides equal 4|S_U| + 2|S_W| − e(S) −
D(S_W)), H5 (in-P1 deficiencies 2 and 2 + 6 = 8, so 4 and 4 after α), H6 (6c + 7 = 3(2c + 3) −
2 for ε = 0; β has degree 7 and parallel edges are allowed by PAPER.md Lemma 0.2), H7 (list length
(6c − 1) + 7 + 1 = 3(2c + 2) + 1 in the rank-(2c + 2) group), H8 (both ends of uw' have P1-degree
≤ 5 because each has an edge leaving P1). All correct as stated.

## 4. Cited inputs, checked against their own text

| Paper's use | Source text | Match |
|---|---|---|
| Classes C_j, E_d; G110 gadget = B − o | PAPER.md 53-60 | yes |
| Lemma 1.4 = PAPER.md Lemma 0.1 (flow criterion, slack 2k − D_A + ε) | PAPER.md 87-96 | yes; I re-proved it |
| Olson's zero-sum lemma (used only in H6, H7) | PAPER.md 104-122 (group-ring proof in F2[K], K ≅ (Z/4)^{n−1}, 3(n−1)+1 = 3n − 2) | yes; the group-ring proof is self-contained and correct (t_v^4 = 0 in char 2, a monomial of degree ≥ 3r + 1 in r variables has an exponent ≥ 4) |
| E3 → C0 reduction (k = 1, ε = 0, D_A = 3, both pieces C0) | PAPER.md 141-157; REPORT.md 252-254; QUARTIC-REVIEW.md 208-210 | yes |
| E4 → C1 reduction (Lemma 1.5) | REPORT.md 254 ("E_4(m) <= C1(m'): k = 1, ε <= 1, both pieces C1"); QUARTIC-REVIEW.md 211-212 (deficiency ≤ (4 − 3 − ε) + ε = 1) | yes |
| Sub-case statement (k = 2, D_A = 5 + ε, x1 ∉ C', C2 piece and |A| = |C'| + 2 piece) | QUARTIC-REVIEW.md 240-246; REPORT.md 259-265; PAPER.md 573-590 | yes; Lemma 3.2 derives it for every port, which is stronger |
| REPORT.md Theorem 5, c = 2 type | REPORT.md 205-212 | yes, verbatim |
| Budget identity and w(C) | REPORT.md Lemma 2, 160-180 | yes; my derivation agrees term by term |
| Lemma 4 (D_C + e(C,S) + e(C,T) ≥ 2c + 2 for proper components) | REPORT.md 196-204; QUARTIC-REVIEW.md 82-104 (barrier wording fix) | yes; the paper uses it only for barriers |
| Tutte citation fix | REPORT.md 140-146 | yes |
| Census bounds m ≤ 41, 59, 62 | CORRECTIONS.md 9-22 | yes |
| Theorem 5 and Lemma 4 accepted by the quartic review | QUARTIC-REVIEW.md 17-21, 82-104 | yes |

Olson (1969) itself was not re-fetched (the paper says so too); it is not load-bearing for Theorem
4.3, and the group-ring proof quoted from PAPER.md stands on its own.

## 5. My code checks (all in `code/`, all exit 0, outputs in `code/out_*.json`)

| Script | What it checks | Result |
|---|---|---|
| `check_identities.py` (seed 20261005) | 102 random C1 instances, s = 5..8, D_U ∈ {0,1}, W-degrees from 1, 3 or 4 up to 6. Exhaustive over all 2^{2s} cuts at every port for s ≤ 7, 30,000 random cuts per port at s = 8. I1 slack formula, I2 g(V − S) = 6 + 2D_U + 2k + 2σ − 2D(C), I3 κ(V − S) = k − 1: 6,291,456 cuts each. I4 min slack = maxflow(G − y) − 4s on 546 ports. I5 every violation with g(Q) ≥ 10 has the Lemma 3.2 data (D_U = 1, k = 2, σ = −1, u1 ∉ C, D_A = 5 + ε, ε ≤ 1, κ = 1, y, u1 ∈ Q): 12 of 33 violations, all pass; violation profiles (k, σ, g, D(C)) seen: (1,−2,6,0), (1,−1,6,0), (1,−1,8,0), (2,−1,8,0), (2,−1,10,0). J1 Identity 1.2 on 306,000 pairs; J2 Identity 1.1, J4 Identity 1.3, J6 g = 2d + 6j and the (j, d) table for g ≤ 8 on 1,198,370 sets; J5 g(V), g(V − v) on 102 instances. | 0 mismatches |
| `exhaustive_small.py 5/6/7` | genbg `-d5:0 -D6:6 s s+1 6s−1:6s`: every C1(s) instance up to isomorphism (W-degree ≥ 0, D_U ∈ {0,1}). Own SAT decider (exact per-vertex forbidden-assignment encoding, witness re-validated). s = 5: 2 graphs; s = 6: 39; s = 7: 1,170. Theorem 4.3 holds for all. Among graphs with min W-degree ≥ 4 (2, 12, 588), exact sparsity by subset DP: 2, 9, 529 sparse; Lemma 4.4 holds on every sparse one (no bad port when D_U = 0; bad-port deficiency ≤ 2). | PASS; the counts 588 = 518 + 70 and 529 = 518 + 11 agree with Appendix A.2 |
| `sparse_core.py 1/2/3` | Own sub-case builder (c ∈ {4,5}, t ∈ {6,7}, ε ∈ {0,1}, optional nesting bias). Exact sparsity by subset DP (n ≤ 23). For every exactly sparse instance: full enumeration of 𝒫 = {Q ≠ V, |Q| ≥ 2, g = 10, κ = 1, u1 ∈ Q} over all 2^n subsets; (E) every member of 𝒫 containing a W-vertex w is the complement of a violation of G − w and G − w has no 4-factor; (L41) |Q| ≥ 3, D^Q(Q_W) = 2, deg_Q(u1) ≥ 3; (L42) 𝒫 closed under ∩ and ∪, all pairs; (L44) the union of 𝒫 is in 𝒫, every bad port is in it, bad-port deficiency ≤ 2. | 52 built (seeds 1, 2, 3; s = 10, 11; n = 21, 23), 50 exactly sparse (min g = 10), 2 non-sparse (min g = 8, skipped). On the 50: E, L41, L42, L44 all hold, 0 failures. Bad-port deficiency 1 (9 instances) or 2 (41). \|𝒫\| = 1 in 41 instances and 2 in 9; every pair comparable (0 incomparable pairs), as §7.2 predicts. |
| `tutte_budget.py` | T1: on 15 random graphs (n = 7..9, degrees 4..6), min over all 3^n pairs (S, T) of δ(S, T) ≥ 0 iff a 4-factor exists (SAT, all degrees exactly 4). T2: budget identity, identity (**), parity of δ, single-vertex w, w ≥ 0, on 111,537 pairs (S, T). T3: P_2 exhaustively with geng `-D6 n 3n−2:` for n = 7, 8, 9, 10 (4, 19, 191, 3,867 graphs): every one has a 4-regular subgraph. T4 (vacuous at n ≤ 10: no graph with e = 3n − 2, δ ≥ 4, Δ ≤ 6 lacks a 4-factor). | 0 mismatches |
| `adversarial.py 7/8` | R1: 391,745 random C1 instances (s = 6..10, W-degree floors 1..4, D_U ∈ {0,1}) all have a quartic subgraph. R2: 406 of them have every port bad; each is non-sparse (some proper set with ≥ 2 vertices has g ≤ 8), as Lemma 4.4 demands. R3: 14 E4 instances built to lack a 4-factor, 16 violations, all with the Lemma 1.5 piece structure. | 0 failures |

What the code cannot check: Lemma 2.1 itself and the use of minimality in Lemmas 3.2, 4.1, 4.2
(no counterexample exists to run them on). Those I checked only by hand (§3), as the paper says.

## 6. Optional clarifications (not required; no statement changes)

1. **Lemma 2.1, proof, j = 1 case** (C1-PAPER.md line 122-123): "so 1 ≤ a ≤ s − 1 (|S| ≥ 2 and
   |S| ≤ 2s)" also uses that |S| is odd when j = 1, so |S| ≥ 3 and |S| ≤ 2s − 1. Add "(|S| odd)".
2. **Lemma 3.1** (line 137): the hypothesis "y a port" is not used in the proof; the identity holds
   for every y ∈ W − A. Stating it that way would make §4's definition of 𝒫 and check (E) below
   read directly from the lemma. Harmless as written.
3. **§5.4** (line 258): "D_C + e(C, S) + e(C, T) ≥ 6 and so w(C) ≥ 3" is right because e(C, S) ≤
   D_C + e(C, S) + e(C, T) =: m gives w = 2m − e(C, S) − 3[odd] ≥ m − 3; one clause saying so
   would save the reader the step. Also the component C must be proper, which holds because a
   barrier has S ≠ ∅ by (**); the paper's cite to the reviewed Lemma 4 covers it.

## 7. Observations (mine, not claims of the paper)

1. **Lemma 3.1 for every y.** Because the cut identity does not use deg(y), a member Q of 𝒫 that
   contains a W-vertex w is the complement of a violation of G − w for *every* w ∈ Q_W, port or
   not: κ(Q) = 1 gives k = 2, g(Q) = 10 and u1 ∈ Q give D(C) = 0 and σ = −1. So in a sparse
   instance G − w has no 4-factor for every W-vertex of the union of petals. My first version of
   check (E) wrongly demanded that such w be a *port* and flagged degree-6 vertices; that was my
   error, corrected (LOG.md 15:29).
2. **In a sparse C1 instance with D_U = 1, 𝒫 is a chain.** Suppose Q1, Q2 ∈ 𝒫 are incomparable.
   By Lemma 4.2, Q = Q1 ∪ Q2 and Q0 = Q1 ∩ Q2 are in 𝒫 and e(X1, X2) = 0 for X_i = Q_i − Q0 ≠ ∅;
   κ(X_i) = 0, |X_i| ≥ 2, so g(X_i) ≥ 10 by sparsity, and g(Q_i) = g(Q0) + g(X_i) − 2e(Q0, X_i)
   gives e(Q0, X_i) = g(X_i)/2. Edges from X_i to V − Q: Σ_{X_i} deg − 2e(X_i) − e(X_i, Q0) =
   g(X_i)/2 − D(X_i) ≥ 5 − D(X_i), and D(X_1) + D(X_2) ≤ D(Q_W) (u1 ∈ Q0). So ∂(Q) ≥ 10 − D(Q_W).
   But V − Q has κ = −2 and D(U − Q_U) = 0, so g(V − Q) = 12 + 2e(U − Q, Q_W), ∂(Q) = (g(Q) +
   g(V − Q) − g(V))/2 = 7 + e(U − Q, Q_W) = 7 + (2 − D(Q_W)) = 9 − D(Q_W), using D^Q(Q_W) = 2.
   Contradiction. Consequence: no built instance can exercise Lemma 4.2 on incomparable petals
   (Appendix A.5 and my §5 runs agree: every 𝒫 found is a chain), and in the minimal
   counterexample the union of all petals is simply the largest one. The proof of Lemma 4.2 is
   still the right tool: it is what shows the union is in 𝒫 without knowing this.
3. **Where minimality is used.** Only Lemma 2.1. Lemma 4.4 is the honest minimality-free content
   and is what Appendix A and my `sparse_core.py` test. The exhaustive data at s ≤ 7 (no bad ports
   on sparse instances with D_U = 1 either, in my runs the bad-port deficiency was always ≤ 2)
   is consistent but, as the paper says, cannot test the minimality step.

## 8. Comparison with the other reviews

(Written after §1-§7; see LOG.md for the time.)

Read after §1-§7 were written: `G110/C1-REVIEW.md` (lane M3-R), `G110/C1-CORRECTIONS.md`, the
verdict table of `wave3/ref2/REVIEW.md`, and the file listings of `G110/review-c1/` and
`wave3/ref2/` (their code was not read).

- **Verdicts agree on every item.** Both earlier referees: ACCEPT WITH FIXES, no mathematical
  error, every lemma, theorem and corollary ACCEPT. Mine, independently: every lemma, theorem and
  corollary ACCEPT, no gap.
- **R1.** Both found the missing word "bipartite" at line 242; I had not. Adopted above as the one
  required fix, after checking the paper's text against CORRECTIONS.md myself.
- **Shared independent observations.** Both earlier reviews and this one derived, separately,
  that Lemma 3.1 does not use "y a port" (C1-REVIEW.md N2 = my §7.1) and that 𝒫 is a chain in any
  sparse instance (C1-REVIEW.md N4, ref2 §2.6, my §7.2; the three proofs differ in the final
  counting step but reach the same contradiction). All three also note w(C) ≥ 4 is the sharp
  bound in §5.4 (my §6.3 only spells out the ≥ 3 step).
- **Second referee's optional wording notes** (from C1-CORRECTIONS.md): line 22 "saturated side"
  should read "side U" (U is not saturated when D_U = 1; I agree, it is loose), and Appendix A.6
  "would have refuted Theorem 4.3" should read "Lemma 4.4" (I agree: an instance where every port
  is bad and every named set has g ≥ 10 would contradict the minimality-free lemma, not by itself
  produce a quartic-free instance, since the "named sets" are not all proper sets). Both optional.
- **Coverage.** C1-REVIEW.md went further computationally than I did: 438 pairs of distinct
  members of 𝒫 on planted chain instances (s = 16-18), a QB(4) census to n = 16, exact 𝒫 by
  min-cut closures on 9,200 instances. My runs are smaller (50 sparse built instances, 9 with
  |𝒫| = 2; Theorem 4.3 exhaustive at s ≤ 7 with all W-degrees; P_2 exhaustive for n ≤ 10 for
  general graphs, which neither summary mentions) and reach the same conclusions. Everything I
  found is consistent with both earlier reviews; nothing in them changes my reading of the proofs.
