# S6 at all sizes: frames of the split graph, a Kempe-descent reduction, and the cuts of B

wave4/s6 (theory lane for S6), October 5, 2026. Status: see the end of the file and `FROZEN.sha256`.
Written proofs plus computer checks. Not reviewed. No Lean, no `check.sh`. Rungs as in STATE.md:
proofs are (a), computations (b).

"va6 PAPER" is `wave4/va6/PAPER.md` (frozen, refereed in `wave4/va6/REVIEW.md`); "theory PAPER" is
`wave4/theory/PAPER.md` (draft); "pairs PAPER" is `wave3/pairs/PAPER.md` (frozen, refereed).

## 0. Results

| Item | Statement | Kind |
|---|---|---|
| Lemma 1.1 | B − o is sparse iff B has no edge cut of fewer than 10 edges with ≥ 2 vertices on each side (independent of o) | proof |
| Lemma 1.2 | cut bounds in Y = B − o − y: ∂_Y(S) ≥ max(10 − a − b, 4 + \|a − b\|, a + b) ≥ 5 | proof |
| Lemma 2.1 | Y has a 4-factor, for every size | proof |
| Lemma 2.2, 2.3 | frames (1-factorizations of the split graph Y⁺ with the five split edges in two classes) exist, and S6 at (o, y) holds iff some frame has Φ = 2 | proof |
| Lemma 3.1 | parity: (−1)^Φ is a product of matching signs; a Kempe swap on a chain with ℓ edges per colour changes a cycle count by ℓ − 1 mod 2; consequences for merging | proof |
| Theorem 4.1 | **rung 2: Lemma K (Kempe descent, all sizes) implies S6 for all sizes** | proof |
| Example 4.2 | the one-move form of Lemma K is false (\|B\| = 16, certified by two programs) | certificate |
| §4.2 | Lemma K holds in every test: all 1,532 strict local minima reached from 4,472 random frames (\|B\| = 16-62, PG(2,5), two Haar graphs) escape; its bounded form K3 (three moves) is false (PG(2,5), two programs) | computation |
| §5 (bank) | fixed sizes: S6 for \|B\| ≤ 24 from H22 and the assumed 2EC for Y; census evidence | conditional proof |
| §6 | part (ii): which cuts of B of 6 or 8 edges a smallest VA6 counterexample can have, and what S6 needs to give B6 | proofs + exact residual |

## 1. Setting and the cut structure of Y

B is a finite simple bipartite 6-regular graph with colour classes I ∋ o and O, oy ∈ E(B) (so
y ∈ O), Γ = B − o, Y = B − o − y. In Y put Q := I − o and P := O − y, so |P| = |Q| =: m and
n := |Y| = 2m. The deficient vertices of Y are the five ports P_o := N(o) − y ⊆ P and the five
vertices Q_y := N(y) − o ⊆ Q; they have degree 5 in Y, all others degree 6, and e(Y) = 6m − 5.
For S ⊆ V(Y): S_P = S ∩ P, S_Q = S ∩ Q, a = a(S) = |S ∩ P_o|, b = b(S) = |S ∩ Q_y|,
j = j(S) = |S_Q| − |S_P|, g(S) = 6|S| − 2e_Y(S), ∂_P(S) = e(S_P, Q − S), ∂_Q(S) = e(S_Q, P − S),
∂_Y(S) = ∂_P(S) + ∂_Q(S). D(Z) = Σ_{v∈Z}(6 − deg_Y v), so D(S_P) = a and D(S_Q) = b.
A *pair* is two edge-disjoint cycles on the same vertex set; S6 asks for a pair spanning Y, i.e.
two edge-disjoint Hamilton cycles of Y.

Degree sums over S_P and S_Q (with e_Y(S) = 3|S| − g(S)/2) give

    ∂_P(S) = g(S)/2 − 3j − a,      ∂_Q(S) = g(S)/2 + 3j − b.                          (1.1)

Since B is 6-regular, 6|S| = 2e_B(S) + ∂_B(S) for S ⊆ V(B), and for S ⊆ V(Y), e_Y(S) = e_B(S), so

    g(S) = ∂_B(S)   for every S ⊆ V(Y),     ∂_Y(S) = g(S) − a − b.                     (1.2)

**Lemma 1.1.** Γ = B − o is sparse (g_Γ(S) ≥ 10 whenever 2 ≤ |S| ≤ |Γ| − 1) if and only if every
edge cut of B with at least two vertices on each side has at least 10 edges. In particular the
condition does not depend on o. (Cut sizes in B are even: ∂_B(S) ≡ 6|S| mod 2.)

*Proof.* As in (1.2), g_Γ(S) = ∂_B(S) for S ⊆ V(Γ). The sets S ⊆ V(B) − o with 2 ≤ |S| ≤ |B| − 2 are
exactly the sides avoiding o of the bipartitions of V(B) with both sides of size at least 2, and
each such bipartition has exactly one side avoiding o. ∎

Call such B *essentially 10-edge-connected* (E10). From now on B is E10.

**Lemma 1.2 (cut bounds).** For S ⊆ V(Y):
(i) if |S| ≥ 2 then g(S) ≥ 10;
(ii) if ∅ ≠ S ≠ V(Y) then g(S) ≥ 4 + 2a and g(S) ≥ 4 + 2b;
(iii) if |V(Y) − S| ≥ 2 then g(S) ≥ 2a + 2b.
Hence ∂_Y(S) ≥ max(10 − a − b, 4 + |a − b|, a + b) ≥ 5 whenever 2 ≤ |S| ≤ n − 2, and Y is
5-edge-connected.

*Proof.* (i) is Lemma 1.1 with (1.2): the complement of S in B contains o and y. (ii) N(o) ∩ S =
P_o ∩ S, so ∂_B(S + o) = g(S) + 6 − 2a; S + o and its complement (V(Y) − S) + y both have ≥ 2 vertices.
The same with y and Q_y. (iii) ∂_B(S + o + y) = g(S) + 6 − 2a + 6 − 2(b + 1) = g(S) + 10 − 2a − 2b
(the edge oy becomes internal), and S + o + y and V(Y) − S both have ≥ 2 vertices. The bound on ∂_Y
follows from ∂_Y(S) = g(S) − a − b; the maximum is ≥ 5 since either a + b ≥ 5 or 10 − a − b ≥ 5.
Single vertices have degree ≥ 5. ∎

So Y is far from the R20 or B24 examples (va6 PAPER Ex. 4): for a balanced S (j = 0) with
2 ≤ |S| ≤ n − 2, (1.1) gives ∂_P(S) − ∂_Q(S) = b − a, and ∂_P(S) + ∂_Q(S) ≥ 4 + |a − b|, so
min(∂_P(S), ∂_Q(S)) ≥ 2: no balanced set has fewer than two edges leaving either colour class
(no thin set).

## 2. The split graph Y⁺ and frames

**Lemma 2.1.** Y has a 4-factor (a spanning 4-regular subgraph), for every size.

*Proof.* By max-flow min-cut (source → P with capacity 4, the edges of Y with capacity 1, Q → sink
with capacity 4; |P| = |Q|), Y has a 4-factor iff 4|A| ≤ 4|C| + e(A, Q − C) for all A ⊆ P, C ⊆ Q.
With S = A ∪ C this reads s'(S) := 4|S_Q| − 4|S_P| + ∂_P(S) ≥ 0, and by (1.1),
s'(S) = g(S)/2 + j − a. For S = ∅ and S = V(Y), s' = 0 (g(V(Y)) = 10, j = 0, a = 5). Otherwise
Lemma 1.2(ii) gives s'(S) ≥ 2 + j, which is ≥ 0 if j ≥ −2; and if j ≤ −3, then ∂_Q(S) ≥ 0 in (1.1)
gives g(S)/2 ≥ b − 3j, so s'(S) ≥ b − a − 2j ≥ 6 − 5 > 0. ∎

(This re-proves from Lemma 1.2 the good-port statement of va6 SCOUT (N5)(i), which there rests on
`G110/C1-PAPER.md` Lemma 4.4.)

**Splitting off oy.** Let π: P_o → Q_y be a bijection, Λ = Λ_π = {p π(p) : p ∈ P_o} (five new edges;
a new edge may be parallel to an edge of Y), and Y⁺ = Y + Λ. Every vertex of Y⁺ has degree 6, so Y⁺
is a 6-regular bipartite multigraph on V(Y). If M_1, ..., M_6 is a 1-factorization of B with
oy ∈ M_1, and M_i ∋ o p_i, y q_i for i ≥ 2, then with π(p_i) = q_i the classes
M_1 − oy and M_i − o p_i − y q_i + p_i q_i (i ≥ 2) form a 1-factorization of Y⁺: Y⁺ is B with the edge
oy contracted and the resulting vertex of degree 10 split into five pairs.

**Definition (frame).** A frame (for π) is a 1-factorization N_0, ..., N_5 of Y⁺ with Λ ⊆ N_4 ∪ N_5.
Then C := N_0 ∪ N_1 and C' := N_2 ∪ N_3 are edge-disjoint 2-factors of Y (no Λ edge), and
N_4 ∪ N_5 = H + Λ where H := Y − C − C' is the leftover of B. Write c(·) for the number of cycles
(components) and

    Φ := c(N_0 ∪ N_1) + c(N_2 ∪ N_3) ≥ 2.

**Lemma 2.2.** For every π there is a frame.

*Proof.* Let F be a 4-factor of Y (Lemma 2.1) and H = Y − F. Then deg_H = deg_Y − 4 is 1 on
P_o ∪ Q_y and 2 elsewhere, so H + Λ is 2-regular and bipartite: its components are even cycles (a
2-cycle is a Λ edge parallel to an H edge). Colour each cycle alternately 4 and 5. F is 4-regular
bipartite, hence the union of four perfect matchings N_0, ..., N_3 (König). ∎

**Lemma 2.3.** For every π: Y has two edge-disjoint Hamilton cycles iff some frame for π has Φ = 2.

*Proof.* If Φ = 2 then N_0 ∪ N_1 and N_2 ∪ N_3 are connected 2-factors of Y, i.e. two edge-disjoint
Hamilton cycles. Conversely, if C, C' are edge-disjoint Hamilton cycles of Y, then H = Y − C − C' has
degree deg_Y − 4, H + Λ is 2-regular bipartite (two perfect matchings N_4, N_5 ⊇ Λ), and C, C' are
even cycles, each the union of two perfect matchings. ∎

**Moves.** On frames for a fixed π:
- a *Kempe swap* (i, k; Z): Z is a component of N_i ∪ N_k (an even cycle alternating colours i and
  k); exchange the colours i and k on Z. It is *legal* if the result is a frame, i.e. if
  {i, k} ⊆ {4, 5} or Z contains no Λ edge;
- a *re-pairing*: permute the colours 0, 1, 2, 3 (so Φ becomes c(N_0 ∪ N_2) + c(N_1 ∪ N_3) or
  c(N_0 ∪ N_3) + c(N_1 ∪ N_2));
- a *Λ re-pairing* (changes π): if p π(p), p' π(p') ∈ Λ have the same colour k ∈ {4, 5}, replace them
  by p π(p'), p' π(p) in colour k. The result is a frame for the new π; C and C' do not change.
Every move keeps the frame property. It is not claimed that all frames are connected by moves;
§3 gives an invariant of Kempe swaps (INV) that only Λ re-pairings change.

## 3. Parity

Fix a bijection β: P → Q. For a perfect matching N of Y⁺ let τ_N: P → Q send p to its N-partner and
put sgn(N) := sign(β^{-1} τ_N) (a permutation of P).

**Lemma 3.1.** (a) For perfect matchings N ≠ N' with no common edge, (−1)^{m − c(N ∪ N')} =
sgn(N) sgn(N').
(b) For a frame, (−1)^Φ = sgn(N_0) sgn(N_1) sgn(N_2) sgn(N_3); re-pairings keep the parity of Φ.
(c) A Kempe swap (i, k; Z) with |Z| = 2ℓ multiplies sgn(N_i) and sgn(N_k) by (−1)^{ℓ−1} and keeps the
other signs. So for j ∉ {i, k} it changes c(N_i ∪ N_j) by an amount ≡ ℓ − 1 (mod 2); if i, k are both
in {0, 1, 2, 3} or both in {4, 5} it keeps the parity of Φ; if i ≤ 3 < k it changes the parity of Φ
iff ℓ is even.
(d) INV := Π_{i=0}^{5} sgn(N_i) is unchanged by Kempe swaps and re-pairings and changes sign under a
Λ re-pairing, and (−1)^Φ = INV · (−1)^{m − c(H + Λ)}.

*Proof.* (a) Let σ = τ_N^{-1} τ_{N'}, a permutation of P. Walking p → τ_{N'}(p) → σ(p) traces the cycle
of N ∪ N' through p, so the cycles of N ∪ N' (of length 2ℓ, ℓ ≥ 1; ℓ = 1 for a pair of parallel
edges) correspond to the cycles of σ (of length ℓ), and sign σ = (−1)^{m − c(σ)}. Also
σ = (β^{-1}τ_N)^{-1}(β^{-1}τ_{N'}), so sign σ = sgn(N) sgn(N'). (b) Multiply (a) for (N_0, N_1) and
(N_2, N_3); the product of four signs does not depend on how they are paired. (c) After the swap,
τ'_i equals τ_k on Z ∩ P and τ_i elsewhere, so τ_i^{-1} τ'_i is the identity off Z ∩ P and on Z ∩ P is
p ↦ τ_i^{-1}(τ_k(p)), one cycle of length ℓ (by (a), Z being one cycle of N_i ∪ N_k). Its sign is
(−1)^{ℓ−1}; the same holds for k. The rest follows from (a) and (b). (d) A Kempe swap multiplies two
signs by the same number; a re-pairing permutes signs. A Λ re-pairing composes τ_{N_k} (k ∈ {4, 5})
with a transposition of Q. The identity is (b) times (a) for (N_4, N_5), with N_4 ∪ N_5 = H + Λ. ∎

**Corollary 3.2.** (i) A Kempe swap along a chain with ℓ odd (for example a 6-cycle) never changes the
number of cycles of C or of C' by exactly one; merging two cycles of C' into one by a swap of a
C'-colour needs a chain whose length is divisible by 4. (ii) From a frame with Φ odd, every sequence
of moves reaching Φ = 2 contains a swap of a colour in {0, ..., 3} with a colour in {4, 5} along a
Λ-free chain of length divisible by 4: the leftover of B must supply the last merge. (iii) Kempe
swaps alone preserve INV, so a Kempe class of frames for a fixed π meets only one value of INV.

So a merging move (NOTES §A) is constrained by parity: in girth-6
hosts such as PG(2, 5) there are no Kempe 4-cycles, and a single merge needs a chain of length
≥ 8.

## 4. The all-sizes lemma and the reduction (rung 2)

### 4.1 Lemma K and the reduction

**Lemma K (Kempe descent; open, all sizes).** Let B be a simple bipartite 6-regular graph with no
edge cut of fewer than 10 edges having at least two vertices on each side, oy an edge of B, and π a
bijection P_o → Q_y. Every frame for π with Φ ≥ 3 can be changed, by a finite sequence of moves
(Kempe swaps, re-pairings, Λ re-pairings; §2) none of which increases Φ, into a frame with smaller Φ.

**Theorem 4.1 (reduction).** If Lemma K holds for (B, o, y), then B − o − y has two edge-disjoint
Hamilton cycles. Hence Lemma K for all E10 graphs B implies S6 for all sizes.

*Proof.* Lemma 2.2 gives a frame. Apply Lemma K repeatedly: Φ never increases and drops at the end of
each sequence, and Φ ≥ 2 is an integer, so after finitely many sequences a frame with Φ = 2 is
reached (for the π current at that point). Lemma 2.3 for that π gives the two Hamilton cycles. ∎

Everything in this reduction except Lemma K is proved here for every size: E10 gives the cut bounds
(Lemma 1.2), the cut bounds give a 4-factor (Lemma 2.1), a 4-factor gives frames (Lemma 2.2), and a
frame with Φ = 2 is the pair (Lemma 2.3).

**What Lemma K uses of B.** (B1) the hypothesis E10, through Lemma 1.2; (B2) the split graph
Y⁺ = Y + Λ: a frame is a 1-factorization of B cut open at o and y, so the four classes forming the
two Hamilton cycles are chosen together with the two leftover classes of B, not as a 4-factor in
isolation; (B3) the leftover classes N_4, N_5 ⊇ Λ are the source of exchanges, and by
Corollary 3.2(ii) they must supply the last merge whenever Φ is odd. Nothing in Lemma K refers to
2-edge cuts of a 4-factor. The 350-vertex Meredith-type graph (theory PAPER §8) is a 4-regular,
4-connected bipartite graph that is not Hamilton-decomposable; Lemma K never fixes the 4-factor
C ∪ C', since Kempe swaps with colours 4, 5 change it.

**The hypothesis is needed.** For B24 with o = 7 (va6 PAPER Ex. 4 and its referee's fix), all six
ports are good, so frames exist, but the balanced set T = copy 1 has at most one edge of Y leaving
each colour class, every 4-factor F of Y has ∂_F(T) ≤ 2, and no frame has Φ = 2. A frame of minimum Φ (≥ 3) then
admits no Φ-lowering sequence: Lemma K fails without E10.

### 4.2 Stronger forms are false

**Example 4.2 (one move is not enough).** ML-1, "every frame with Φ ≥ 3 has a single legal Kempe swap
or re-pairing that lowers Φ" (Λ re-pairings never change Φ), is false. Certificate
`data/ml1_counterexample.json`: B on 16 vertices (I = 0..7, O = 8..15), minimum essential cut 10,
o = 0, y = 11, π (the five virtual edges are listed in the file) and a frame with Φ = 3
(c(C) = 2, c(C') = 1); its 17 legal Kempe swaps and the
two re-pairings all give Φ ≥ 3. Found by `code/frames.py` + `code/test_ml.py` (descent), checked by
`code/verify_min.py`, which shares no code with them (own E10 check over all 2^15 vertex sets, own
frame check, own component counts by union-find).

How often single moves fail (strict local minima reached by descent from random frames; random B
from six random perfect matchings, E10 checked; `code/test_ml.py`, `code/escape.py`):

| Host | frames | strict local minima | escape depth 2 / 3 / 4 | no escape |
|---|---|---|---|---|
| random B, \|B\| = 16 | 400 | 78 | 75 / 3 / 0 | 0 |
| random B, \|B\| = 20 | 400 | 95 | 95 / 0 / 0 | 0 |
| random B, \|B\| = 24 | 1,150 | 348 | 345 / 3 / 0 | 0 |
| random B, \|B\| = 30 | 400 | 142 | 140 / 2 / 0 | 0 |
| random B, \|B\| = 40 | 894 | 333 | 326 / 7 / 0 | 0 |
| random B, \|B\| = 50 | 144 | 64 | 63 / 1 / 0 | 0 |
| random B, \|B\| = 62 | 144 | 74 | 71 / 3 / 0 | 0 |
| PG(2, 5) incidence graph (62 vertices, girth 6) | 340 | 174 | 162 / 11 / 1 | 0 |
| H(Z_19, {3,7,8,14,15,16}) (38 vertices) | 300 | 105 | 104 / 1 / 0 | 0 |
| H(Z_23, {3,5,9,13,17,20}) (46 vertices) | 300 | 119 | 118 / 1 / 0 | 0 |

A frame is a random frame: Lemma 2.2's frame for a random π after 300 random legal Kempe swaps and Λ
re-pairings, at a random o and port y. Descent takes a random Φ-lowering single move until none
exists; every descent that did not stop at a strict local minimum reached Φ = 2. "Escape depth" is
the least number of moves (Kempe swaps and re-pairings, never raising Φ; Λ re-pairings not used, so
the counts are upper bounds for the full move set) after which Φ is lower, found by breadth-first
search (cap 3,000 to 20,000 frames; never reached). One method (`code/escape.py`,
`code/escape_fixed.py`); outputs in `data/escape_*.txt`, `data/escapeB_*.txt`.

**Example 4.3 (three moves are not enough).** K3, "Lemma K with sequences of at most three moves",
is false. Certificate `data/pg25_depth4.json`: the PG(2, 5) incidence graph (E10: `code/frames.py`
max flow; the networkx check of `code/verify_depth.py` is reported in Appendix A), a frame with Φ = 3
from which no sequence of at most three moves (all move types, including Λ re-pairings) that never
raises Φ lowers Φ, while four moves do. Checked by `code/escape.py` (breadth-first search, depth 4)
and by `code/verify_depth.py` (shares no code with it: 9, 47, 211 Φ-neutral frames at depths 1, 2, 3,
none with a Φ-lowering move; an escape at depth 4). So any proof of Lemma K has to allow sequences of
unbounded or at least growing length, and girth 6 is where the long sequences appear first.

### 4.3 Where the proof of Lemma K is stuck (the main obstruction)

1. *The objective is not a cut function.* The repair tools that work in this project (pairs PAPER
   Lemma 7, va6 Lemma D', theory PAPER Theorem 2.1) maximize the number of factor edges across one
   fixed set; 4-factors are the integer points of a flow polytope, so a failure produces a closed set
   X of an auxiliary digraph whose cut contradicts sparsity. "C is a Hamilton cycle" asks C to cross
   every set at once, and a failure of one exchange does not produce a closed set. This is the step
   where Lemma 1.2 has to enter and where no argument is known.
2. *Parity* (Corollary 3.2): from odd Φ the last step is a swap of a cycle colour with a leftover
   colour along a Λ-free chain of length ≡ 0 (mod 4). The five Λ edges lie in N_4 ∪ N_5 and block
   every leftover chain through them; in small hosts N_i ∪ N_4 often has only one to three
   components, so most leftover chains are blocked. Λ re-pairings exist to move the blocks.
3. *No local potential.* Single moves (Example 4.2), single moves after recolouring inside C, C' and
   H + Λ (5 to 15% of minima still stuck, `code/escape2.py`), a lexicographic potential
   (Φ, −Σ|K|², `code/lexdesc.py`: 53 to 72 of 225 descents stuck per size) and three moves
   (Example 4.3) all fail. What survives is reachability within a level set of Φ.

What a proof has to show is a statement about the frame graph: no nonempty set of frames with
Φ ≥ 3 is closed under the moves that do not raise Φ (this is Lemma K restated). E10 is necessary
(§4.1, B24). The natural shape of the missing argument: from a closed set of frames at level
Φ_0 ≥ 3, extract a vertex set S with g(S), g(S + o), g(S + y) or g(S + o + y) below the bounds of
Lemma 1.2.

## 5. Bank: fixed sizes (not the target; recorded separately)

- **Census.** S6 holds for every B with |B| ≤ 18, every o and every port y (va6 PAPER §4, reproduced
  by its referee with independent code; every B on 16, 18 or 20 vertices is E10, va6 REVIEW). At |B| = 20 it holds
  on the slice 0/600 (227 graphs), and on random graphs at |B| = 22, 24 (40 each, every o, every y)
  and 28, 30 (14,277 graphs, 2,474,427 decisions; `wave4/va6/S6-RESULT.md`), one method each.
- **Conditional, |B| ≤ 24.** Let 2EC_Y be: *Y has a 4-factor with no edge cut of at most 2 edges.*
  If 2EC_Y holds and |B| ≤ 24, then |Y| ≤ 22 and H22 (every bipartite 4-regular graph on at most 22
  vertices with no cut of at most 2 edges is Hamilton-decomposable; `wave3/pairs/SCOUT.md` §2.3, one
  method at 22, two methods below) gives two edge-disjoint Hamilton cycles of Y. 2EC_Y is the
  theory-2 lane's 2EC' transplanted to Y (owned there; assumed here, not proved). Lemma 2.1 gives
  the 4-factor; what 2EC_Y adds is the absence of 2-edge cuts.
- **Why the bank is not the target.** Beyond 22 vertices "no 2-edge cut" does not give a Hamilton
  decomposition (the Meredith-type 350-vertex graph), and §4 replaces the fixed 4-factor by frames.

## 6. Part (ii): what S6 needs in order to give B6

VA6: for every simple bipartite 6-regular B and every vertex o, B − o has a pair. VA6 implies B6
trivially, and B6 implies VA6 (Corollary B of `585-fable/PROOF-R1.md`). Let (B, o) be a counterexample
to VA6 with N = |B| minimum. Then (F0) VA6 holds below N, and N ≥ 22 (va6 PAPER §4: VA6 for all
|B| ≤ 20); (F1) B[T] has no pair for every T ⊆ V(B) − o; (F2) B is connected (a component avoiding o
is a smaller 6-regular bipartite graph, and VA6 at any of its vertices gives a pair in it). (F3) If B
is E10, S6 gives a pair in B − o − y ⊆ B − o for any port y. So **S6 implies that a smallest VA6
counterexample has an essential cut (both sides ≥ 2 vertices) of 2, 4, 6 or 8 edges**, and S6 gives
B6 exactly when such cuts are ruled out.

For a cut (T, T̄) with o ∉ T write c = |∂T| and, for v ∈ T, d(v) for the number of cut edges at v.
By va6 PAPER (1), ∂_I(T) − ∂_O(T) = 6(|T_I| − |T_O|); for c ≤ 8 the types are the balanced (1,1),
(2,2), (3,3), (4,4) (k = c/2 cut edges at each class) and the *one-passage* types (6,0), (7,1) with
|T_I| = |T_O| + 1 (and their colour swaps (0,6), (1,7)).

**Lemma 6.1 (sides are large).** If c ≤ 8 and |T|, |T̄| ≥ 2, then both sides have at least 11
vertices, and at least 12 if the cut is balanced.

*Proof.* With class sizes k and k + δ (δ ∈ {0, 1}), 2e(T) = 6|T| − c and e(T) ≤ k(k + δ). For δ = 0:
k² − 6k + c/2 ≥ 0, so k ≥ 3 + √(9 − c/2) > 5.2. For δ = 1: k² − 5k + (c − 6)/2 ≥ 0, so
k ≥ (5 + √(37 − 2c))/2 ≥ 4.79. (In both cases the other root is below 1, and k ≥ 1 since the side
has at least two vertices.) The other side is a side of the same cut. ∎ (K_{6,5} = K_{6,6} − vertex is a (6,0) side with 11 vertices.)

**Lemma 6.2 (one-passage 6-cuts).** Let (T, T̄) be of type (6,0) with o ∉ T and |T̄| ≥ 2. If the six
cut edges have six distinct ends in T, then B − o has a pair. The same holds for type (0,6).

*Proof.* Add a new O-vertex z joined to the six ends. B[T] + z is simple, bipartite (|T_I| =
|T_O| + 1), 6-regular, and has |T| + 1 < N vertices. VA6 at z gives a pair in B[T] ⊆ B − o. ∎

**Lemma 6.3 (concentration on one class).** Let (T, T̄) be balanced with c = 2k (1 ≤ k ≤ 4) and
o ∉ T. If one vertex p ∈ T_I carries all k cut edges at T_I, and the k cut edges at T_O have distinct
ends q_1, ..., q_k, none adjacent to p, then B − o has a pair. The same with I and O exchanged.

*Proof.* B[T] + pq_1 + ... + pq_k is simple, bipartite and 6-regular on |T| < N vertices; VA6 at p
gives a pair in B[T] − p. ∎ (k = 1 is va6 PAPER Lemma 1, case 1; for k = 2 this needs no size
condition, unlike Lemma 1, case 3.)

**Lemma 6.4 (removing an end).** For v ∈ T, ∂(T − v) = c + 6 − 2d(v). (The d(v) cut edges at v
leave the cut and the 6 − d(v) edges from v into T join it.)

**Theorem 6.5 (residual cuts).** Let (B, o) be a smallest counterexample to VA6 that is not E10.
Among its essential cuts take one with c minimum and then, T being the side avoiding o, with |T|
minimum. Then:
- c = 2: |T| ≥ |T̄|, the two ends in T are adjacent, and |T| ≥ 22 (va6 PAPER Cor. 2(a));
- c = 4: 2|T| ≥ N, or each class of T carries both of its cut edges at one vertex and 3|T| ≥ N
  (va6 PAPER Lemma 1, cases 3 and 4), and T is not as in Lemma 6.3;
- c = 6 or 8: every vertex of T carries at most two cut edges; the cut is balanced ((3,3) or (4,4)),
  or of type (7,1)/(1,7), or of type (6,0)/(0,6) with some end carrying exactly two cut edges.

*Proof.* The cases c = 2, 4 are the cited results and Lemma 6.3. Let c ∈ {6, 8} and v ∈ T with
d(v) ≥ 3. By Lemma 6.4, (T − v, T̄ + v) is a cut of size c + 6 − 2d(v) ≤ c, essential (|T − v| ≥ 10
by Lemma 6.1), with o ∉ T − v, and |T − v| < |T|: against the choice of the cut. So d ≤ 2 on T, and
for type (6,0) the ends are not distinct by Lemma 6.2. ∎

**Corollary 6.6.** S6, together with (R) "no smallest counterexample to VA6 has a cut as in
Theorem 6.5", implies VA6 and hence B6. By Lemma 6.1 a non-E10 B has at least 22 vertices
(consistent with va6 REVIEW: every B on 16, 18 or 20 vertices is E10).

### 6.1 Why the residual cuts resist, and the exact missing statement

The doubling of va6 PAPER Lemma 1 joins two copies of B[T] by the c cut edges crossed over and
deletes one vertex; a pair is confined to one copy (by (C): a pair crosses a cut at least four times)
only if at most three cross edges survive. With every end carrying ≤ 2 cut edges, one deletion
removes at most 2 of 2k ≥ 6 cross edges, so at least 4 survive, and a pair of the doubled graph can
pass between the copies. Completions inside T (Lemmas 6.2, 6.3) need a new vertex on distinct ends,
or all new edges at one vertex; under Theorem 6.5 the new edges spread over at least two vertices
for (3,3) and (4,4) cuts (each end carries ≤ 2 of k ≥ 3 edges), and (6,0) with a repeated end has no
simple completion by one vertex.

What S6 needs, stated exactly, is (R) of Corollary 6.6 for the residual types of Theorem 6.5.
A natural strengthening does not supply it. Let VA6_f be: for every simple bipartite 6-regular B,
every vertex v and every set F of at most f edges, B − v − F has a pair. In a smallest VA6
counterexample, VA6_f for smaller graphs would close a residual balanced cut: complete B[T] by k new
edges μ between the ends (when this can be done simply) and apply VA6_f at an end p with F = the
new edges not at p (f = 2 for (3,3), f = 3 for (4,4); one less if some end carries two cut edges).
But VA6_f is then the statement to be proved by minimality, its smallest counterexample carries its
own F, and the same completion needs |F| + k − d(p) forbidden edges, more than f. So the forbidden-edge
induction does not close, and the E10 case would in any event need S6_f (if B is E10, B − o − F has a
pair for every F of at most f edges), which S6 does not imply. The one-passage residual types
((6,0) with a repeated end, (7,1)) need completions with at least two new vertices, which one deletion
cannot remove. These residual cuts are open.

## 7. Not proved here

- Lemma K (§4.1), hence S6, at any size beyond the census. §4.3 records where the proof stops.
- The residual cuts of Theorem 6.5, hence "S6 implies B6".
- 2EC_Y (§5), assumed for the banked conditional result; it belongs to the theory-2 lane's 2EC'.
- A rigid-set exclusion for Y. Unlike the E4 case, the cut bounds do not exclude edges that lie in
  no 4-factor: with s(S) = g(S)/2 − j − b (theory PAPER Lemma 1.1), Lemma 1.2 and (1.1) leave exactly
  one shape of set with s(S) = 0 that excludes an edge, namely j = 2, b = 5, a = 0, g(S) = 14,
  ∂_P(S) = 1, ∂_Q(S) = 8; then S + y is the side of a 10-edge cut of B of type (8,2) that contains the
  edge oy. Whether such sets occur was not pursued.

## Appendix A. Computations (rung (b)) and files

All code is in `code/`, outputs in `data/`. Python 3 (`/usr/bin/python3`); networkx only in
`verify_depth.py`. Every command was run under `timeout 240` or a longer cap noted in `LOG.md`.

- `frames.py`: random B (six successive random perfect matchings in the complement, restart on
  failure; not uniform), E10 test `ess10` (max flow from each edge to each pair {o, w}; validated on
  B24 (finds the 2-cut), on two copies of K_{6,6} minus a k-edge matching joined by 2k edges
  (k = 1..4: the cuts of 2, 4, 6, 8 edges are found; k = 5 passes), and against
  `wave3/pairs/ptool2 s` on 48 random graphs with 16 to 30 vertices (all agree)), the frame of
  Lemma 2.2 (4-factor by augmenting paths, König 1-factorization), Kempe chains, legal moves.
- `test_ml.py` (descent), `escape.py` and `escape_fixed.py` (breadth-first escape from strict local
  minima; random B, or a fixed graph from JSON), `escape2.py` (recolouring inside C, C', H + Λ, then
  one move), `escape3.py` (types of first moves), `lexdesc.py` (lexicographic potential).
- `save_min.py`, `save_deep.py`: write the certificates `data/ml1_counterexample.json` and
  `data/pg25_depth4.json` (B as an edge list with I = 0..M−1, o, y, and the coloured edges of Y⁺ with
  the Λ flag).
- `verify_min.py` (no shared code): B simple, bipartite, 6-regular; minimum essential cut of B by
  enumeration of all 2^15 vertex sets (= 10); Y⁺ rebuilt from B, o, y and the Λ list; frame check; all
  17 legal Kempe swaps and both re-pairings keep Φ ≥ 3.
- `verify_depth.py` (no shared code; networkx max flow over all pairs of disjoint edges for E10,
  `data/pg25_e10_check.txt`: minimum essential cut ≥ 10 for PG(2, 5)): breadth-first search over all
  move types including Λ re-pairings, keeping only Φ-neutral frames. On `pg25_depth4.json`: 9, 47, 211
  neutral frames at depths 1, 2, 3, none with a Φ-lowering move; a Φ-lowering move at depth 4. (A
  first version kept Φ-raising frames in the frontier and reported a spurious escape at depth 2; fixed
  before the reported run, `LOG.md`.)
- Hosts: PG(2, 5) from `wave4/va6/tools/gen.py pg25`; H(Z_19, {3,7,8,14,15,16}) and
  H(Z_23, {3,5,9,13,17,20}) from `gen.py haar` (graph6 decoded to JSON in the lane's scratch space).

## Status

Frozen for review: the SHA-256 of this file is in `FROZEN.sha256`. Rung reached: 2 (Theorem 4.1:
S6 reduced to the all-sizes Lemma K, every other step proved). Not reached: rung 1 (Lemma K open),
rung 3 (no counterexample to S6 found; in the 4,472 test frames on E10 hosts every strict local
minimum of Φ had a Φ-lowering escape).
