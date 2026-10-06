# REVIEW3: QB(5) round 3, cores reduce to one block lemma (wave4/qb5/PAPER3.md)

Independent adversarial referee, October 5, 2026. Status: FINAL.
Object: `PAPER3.md` as frozen in `FROZEN3.sha256` (`shasum -a 256 -c FROZEN3.sha256`: all 20 entries OK at the
start and at the end of this review). Working files, log and code: `review3/` (`review3/LOG.md`, `review3/code/`,
`review3/data/`, `review3/runs/`). Nothing here is a project-oracle PASS: no Lean, no `check.sh`.

Method. Every proof step was re-derived by hand, including the cited steps of PAPER.md and PAPER2.md that PAPER3
uses. Every computation was redone with code written from scratch in `review3/code/`. Nothing in `qb5/code/` was
run, imported or read; the author's `.g6` files and search logs were used as data only. Generators: my own
enumerations of 7-edge cuts (row multisets with a brute-force canonical form, and the full matrix grid), plain nauty
genbg 2.9.3 only to cross-check class counts, own Dinic max flow, own block checker in C, and PySAT 1.9 (CaDiCaL
1.9.5, research venv) for a SAT search. Compute used: about 40 core-minutes.

## 1. Verdicts

| Claim | Verdict | Short reason |
|---|---|---|
| **Theorem 2.1** (M-form: a good pair exists iff some 4 of the 7 cut edges leave a free vertex in both blocks; the blocks decouple) | **ACCEPT** | Both directions re-derived. "If": a ∈ V(M) makes A − a under-supplied (dem = 4 > 4 − m(a)), so p ∉ V(M), then PAPER2 Corollary 2.3. "Only if": the counting converse recorded in REVIEW2 §2, with Fact 2.1 under G1. Own max flow agrees on every P × Q pair of all 35 instances, for both 2-block decompositions of each (12,450 pair decisions, 0 disagreements). |
| Lemmas 3.1, 3.2, 3.3 | ACCEPT | Re-derived: the split of C into C'(T), C''(T) needs nothing about T; (iv) is sparsity of T ∪ C', A1 ∪ C'' and A1 ∪ C'' − x. Checked on every T of every block below (0 violations). |
| **Lemma 3.4** (case (b) is rigid) | **ACCEPT** | Re-derived (w(a) = 3, κ = 1 gives 7 > 6, so κ = 0 and w(T − a) = e'' = 0, θ = 1). Shape checked by own code at every case-(b) occurrence I could produce: the §6.1 block over all 336 admissible cut vectors (96 occurrences) and two blocks found by SAT, \|X\| = 20 and 22, over all their admissible cut vectors (66 occurrences): 0 violations. |
| **Lemma 4.1** (refined covering lemma, computed) | **ACCEPT** | Two own enumerations, literal subset search for K: 142 classes (= genbg in all 25 cells), 36,339 labellings, 0 failures; 22,792 matrices, 15,342,638 labellings, 0 failures. Loose mode (any K): 338,494 failures, equal to the paper. |
| **Theorem 4.2, Corollary 4.3** (KL1 for both blocks ⇒ E5 pair statement ⇒ QB(5); KL1 for generic blocks) | **ACCEPT** | The reduction is complete; I found no gap (chain in §3). Lemma 3.4 makes K = (T − a) ∩ V(E) rigid exactly in the sense of Lemma 4.1, so Lemma 4.1's M is X-good and Y-good, and Theorem 2.1 finishes. |
| **Propositions 5.2, 5.3; §5.4** (two under-supplied sets meet; s = 2 never fails; exact remaining case s ≥ 3) | **ACCEPT** | Weight count and the degree bound at the shared vertex re-derived; correct. |
| §6.1 example (case (b) occurs; the strong form of KL1 is false; KL1 holds for it) | ACCEPT | Every number confirmed by own code. I also embedded the block in a sparse E5 instance without a 4-factor (n = 32), where the same three M are X-bad, so the strong form fails for blocks of actual E5 instances too (optional addition, §2). |
| §6.2 data, Appendix A | **ACCEPT WITH FIX** (H1) | 1,750 blocks and 89,194 covering multisets reproduced, 0 failures; 25 blocks with a non-generic vertex, as stated. The planted search logs show 1,600 starts, not "about 1,300". |

No REJECT. I found no mathematical error. **"KL1 implies QB(5)" is a complete reduction**: KL1 for both blocks of
a minimal counterexample contradicts minimality.

**KL1 counterexample: none found.** In addition, §6 below proves (referee observation, not part of any verdict)
that a KL1 failure needs a minimal family with at least **four** core-type sets: the case s = 3 is impossible.

## 2. Required fix, with location

- **H1** (§6.2, line 263, and A.5, line 283). "about 1,300 starts" for `klplant.c`: the frozen logs
  `code/data/kl/kp_10.err` to `kp_13.err` end with `done starts 400 withcore 400 found 0` each, 1,600 starts in all.
  Correct the number (or say which starts are counted).

Optional, editorial:
- Lemma 4.1, lines 162-163: "it rejects a side 33.5 million times" is a counter whose value depends on the search
  order (the search stops at the first good M). Say what is counted, or drop it. For reference, the number of
  (labelling, M, side) triples rejected only by the rigid condition on the grid is 375,034,802 (own count).
- §6.1: the block is checked for sparsity as a block. It also sits in a sparse E5 instance without a 4-factor:
  Y = K_{4,6}, cut 0-0, 1-1, 2-2, 3-3, 6-4, 7-5, 8-0 (A index, D index); n = 32, e = 91, every proper S with
  \|S\| ≥ 3 has e(S) ≤ 3\|S\| − 6, and the M with A-ends {t2, t3, t4, x}, x ∈ {6, 7, 8}, are X-bad there
  (`review3/data/ex61_embedded_n32.g6`; it has 61 good pairs, so it is no counterexample to the pair statement).
  Adding this places "the strong form of KL1 is false" in the setting of KL1. Case (b) occurs already at
  \|X\| = 20 (`review3/data/caseb_sat.blk`, line 1).
- Corollary 4.3(b): "both blocks of every minimal counterexample" should read "both blocks of some 2-block
  decomposition of every minimal counterexample"; Theorem 4.2 fixes one decomposition.
- §4: the rigid test reduces to one line. With a the uncovered L-vertex and F = {v ≠ a : m(v) = c_v ≥ 1, and
  v ∉ L or c_v = 3}, a rigid K exists iff m(F) ≥ 3, since c(F) = m(F) ≤ 4 (checked equal to the subset search on
  every case of both enumerations).

## 3. Proof notes (re-derivation, adversarial points)

- **§1.1.** min(4, 6 − x) = 4 − (x − 2)^+ on 0 ≤ x ≤ 6 gives dem_X(A − T) = 8 − φ_X(T). θ(T) = m(T) − ρ(T) =
  dem_X(A − T) − m(A − T), so I_X(M) = A minus the union of overloaded sets; {v} is overloaded iff m(v) ≥ 1; pairs
  never are (ρ = 4). w(A) = 12 − 4 = 8; with L_A covered, w ≤ 2 everywhere.
- **Theorem 2.1.** In "only if", every c ∈ C keeps H-degree 4 because q ∈ D, so 4\|A1\| = e_H(A1, C) + m(A1) ≤
  Σ_c min(4, e(c, A1)) + m(A1). The "hence" clause needs Fact 2.1 with G1 to restrict good pairs to A × D; PAPER3
  cites it.
- **Lemma 3.1.** (i) uses only \|A\| − \|C\| = 2 and the threshold e(c, T) ≥ 3. (iv) applies sparsity to subsets of X,
  which are proper subsets of V; X'(A) = X gives κ + k = 2 + 0, consistent.
- **Lemma 3.2.** \|A − T\| ≤ 4 makes dem_X(A − T) = Σ(4 − d_a) ≤ \|(A − T) ∩ L_A\| ≤ m(A − T) (PAPER2 Lemma 3.1(b));
  this is where "every L-vertex outside T is an end of M" enters. k = θ + m(A − T) ≥ 1; κ ≥ −1 from 2κ + 3 ≥ 0.
- **Lemma 3.4.** Lemma 3.2 applies because a ∈ T. c(T − a) = 5 − k ∈ {3, 4} is exactly the size window of the rigid
  sets; L-vertices of T − a have def = 0, so c = 3 by (B2).
- **Lemma 4.1 vs. its use.** Lemma 4.1 imposes no deficiency condition on ends outside L, so it excludes more sets
  K than Theorem 4.2 needs; this is the remark after Lemma 4.1, and it is right. The hypotheses hold for the cut of
  G by (B1), (B2).
- **Theorem 4.2 and Corollary 4.3: the complete chain.** Minimal counterexample → sparse E5, no 4-factor, no good
  pair (PAPER.md Lemma 2.1, Theorem 7.1) → 2-block decomposition (PAPER.md Theorem 6.1) → Lemma 4.1 gives one M
  for both sides → on each side: L covered, then KL1; one L-vertex a uncovered, then Lemma 3.4 plus Lemma 4.1 put a
  in I(M); two uncovered is excluded by Lemma 4.1 → Theorem 2.1 gives a good pair → contradiction. Every step is
  proved or computed; KL1 is the only hypothesis.
- **Corollary 4.3(c).** \|A\| ≥ 6 > 4 ≥ \|V(M) ∩ A\| gives p ∉ V(M); PAPER2 Lemma 3.3(a) needs only that M covers
  L_A − p and has no edge at p.
- **§5.1.** A minimal family with empty intersection never contains A, and its trivial vertices are exactly the
  intersection of its core-type members.
- **Proposition 5.2.** κ_1 + κ_2 ≥ 1 forces a κ_i = 1, then e''_i ≥ 3 and κ_1 + κ_2 ≥ 5/2 > 2. The s ≤ 1 cases are
  right (\|A1\| ≥ 5 > 4 ≥ \|V(M) ∩ A\|).
- **Proposition 5.3.** C''(T_1) ∩ C''(T_2) = ∅ (7 > 6 neighbours); the degree bound at u uses c_u ≥ m(u) ≥ 1, so
  d_u ≤ 5; the final inequality uses κ_1 + κ_2 ≥ (e''_1 + e''_2)/2. Correct.

## 4. Computations (own code, `review3/code/`)

| Check | Code and input | Result |
|---|---|---|
| Lemma 4.1, enumeration I | `lemma41.c classes`: row multisets, canonical form by all row permutations | 142 classes (per-cell counts equal to genbg `-d1:1 -D3:3 na nd 7:7` in all 25 cells), 36,339 labellings: 0 failures; loose 607; plain 0 |
| Lemma 4.1, enumeration II | `lemma41.c grid`: every 0/1 matrix with non-increasing row and column sums in {1, 2, 3} | 22,792 matrices, 15,342,638 labellings: 0 failures; loose 338,494 (= PAPER3); plain 0 |
| Lemma 4.1, decision | literal subset search for K vs. the one-line rule m(F) ≥ 3 | identical on every (L, M) in both enumerations |
| Theorem 2.1 | `thm21.py`, `r3lib.py` (own graph6, Dinic, decomposition finder) on the n = 28 certificate, `core28.g6` (24), first 5 of `e5_n22.g6` and `e5_n24.g6` | every instance has 2 decompositions (X and Y swapped); every P × Q pair in both: 0 disagreements; all 35 M X-good and Y-good everywhere; good pairs 54 to 60 on core28 |
| §6.1 block | `blk3.c` (own: sparsity, demands, all overloaded T, Lemmas 3.1, 3.2, 3.4, Props 5.2, 5.3) on `ex61.blk` | block-sparse, L_A = {a}, dem_X(U) = 2; with the stated cut vector exactly the 3 M with A-ends {t2, t3, t4, x} have I_X = ∅; 129 extendable covering multisets, KL1 holds; Lemma 3.4 shape at all 96 case-(b) occurrences over 336 cut vectors |
| §6.1 embedded | `embed.py` (Y = K_{4,6}; sparsity by enumerating S ∩ P) | n = 32, e = 91, sparse, no 4-factor, case (b) for the same 3 M; 61 good pairs |
| Smaller case (b) | `kl1sat.py ... caseb`, then `blk3.c` | blocks with \|A\| = 11 (\|X\| = 20) and 12; I_X = ∅ confirmed; shape holds at all 66 occurrences (all admissible cut vectors); KL1 holds on both |
| KL1 on built blocks | `extract_blocks.py`, `blk3.c` on 875 instances (cert, core28, e5_n22, e5_n24, dump_mixed), both blocks | 1,750 blocks, 89,194 extendable covering multisets (= PAPER3), 0 failures. Over all 194,055 admissible cut vectors: 2,431,923 covering (c, m), 0 failures; 0 violations of Lemmas 3.1(i), (ii), (iv), 3.2, Props 5.2, 5.3; case (b) never occurs in these blocks |
| "25 blocks with a core" | `generic3.c` (PAPER2 Definition 3.2, actual cut vector) | 25 of 1,750 blocks have a non-generic vertex (76 vertices) |
| Search logs | author's `kls_*.err`, `kp_*.err` (data only) | kls: best 6 to 9 = \|A\| − 4 (no core-type set); kp: 4 × 400 = 1,600 starts, 0 found (H1) |
| KL1 SAT search | `kl1sat.py`, `kl1sat2.py`: block, cut vector, covering m and s under-supplied sets as variables, lazy block sparsity, exact re-check of every model | (\|A\|, s) = (12, 3): no model in 2.3 CPU-min; (14, 3), (16, 3), (16, 4): no block-sparse model in 7 min each. Inconclusive; CDCL is weak at the weight arithmetic here. No counterexample |

## 5. F1 to F7, G1 to G3 carried over

PAPER3 §1.2 lists all ten with the content of REVIEW.md §2 and REVIEW2.md §2. The ones PAPER3 uses are applied
correctly: G1 in Theorem 2.1 (pairs p ∈ P, q ∈ Q; Fact 2.1 then gives A × D), F2 in §0 (n ≥ 3), the counting
converse of PAPER2 Corollary 2.3 in Theorem 2.1. F3 to F7, G2 and G3 concern statements PAPER3 does not use.

## 6. KL1: where a counterexample could still be (referee observation, not refereed)

Offered to the author; no verdict depends on it. Setting of §5: M covers L_A, U = V(M) ∩ A. I_X(M) = ∅ iff some
family of core-type under-supplied sets has intersection inside U; take one minimal under inclusion,
{A1_1, ..., A1_s}. Props 5.2, 5.3 give s ≥ 3, and minimality gives x_i ∈ ⋂_{j≠i} A1_j − A1_i − U for each i.

**Claim.** s = 3 is impossible. So KL1 can fail only through a minimal family with s ≥ 4.

Notation for s = 3: T_i, κ_i, k_i, θ_i, e''_i, C''_i as in §3, X''_i = A1_i ∪ C''_i (κ = 2 − κ_i, g = 12 − 6κ_i +
2e''_i); V_0 = A1_1 ∩ A1_2 ∩ A1_3 ⊆ U; I_ij = A1_i ∩ A1_j − V_0 (contains x_k); Ex = vertices in exactly one A1_i;
N = A − ⋃A1_i; Z_ij = (A1_i ∩ A1_j) ∪ (C''_i ∩ C''_j); f_ij = edges from C''_i ∩ C''_j leaving A1_i ∩ A1_j;
U'' = ⋃X''_i; ε = e(⋃C''_i, N); C_0 = C − ⋃C''_i. Tools, all from Lemma 3.1 and sparsity:
(a) w(T_i) = 2κ_i + 4 − θ_i − e''_i, and Σ_v w(v)·#{i : v ∈ A1_i} = Σ_i (8 − w(T_i)).
(b) u ∈ A1_i has at least 3 + 3κ_i − e''_i neighbours in C''_i, so u ∈ A1_i ∩ A1_j has
    δ_u ≤ e(u, C''_i ∩ C''_j) + e''_i + e''_j − 3κ_i − 3κ_j.
(c) If C''_i ∩ C''_j ≠ ∅, then 12 ≤ g(Z_ij) ≤ 6κ(Z_ij) + 2f_ij, so κ(Z_ij) ≥ 2 unless f_ij ≥ 3; if it is empty,
    κ(Z_ij) = \|A1_i ∩ A1_j\|. Also Σe''_i ≥ Σf_ij + ε.
(d) If no C-vertex lies in all three C''_i: κ(U'') = Σ(2 − κ_i) − Σκ(Z_ij) + \|V_0\|, g(U'') = 6κ(U'') + 2ε ≥ 12,
    \|C_0\| = \|N\| + κ(U'') − 2, and g(N ∪ C_0) = 6(\|C_0\| − \|N\|) + 2δ(N) + 2ε.

*V_0 = ∅.* A = T_1 ∪ T_2 ∪ T_3 gives Σw(T_i) ≥ 8, which with (a) leaves (A) κ = 0, θ = 1, e'' = 0;
(B) κ = 0, θ = (2, 1, 1), e'' = 0; (C) κ = 0, θ = 1, e'' = (1, 0, 0); (D) κ = (1, 0, 0), θ = 1, e'' = (3, 0, 0).
In (A), w(⋃I) ≥ 7 and w(Ex) ≤ 1; in (B) to (D), w(N) = w(Ex) = 0 and I_12, I_13, I_23 weigh 3, 3, 2. By (b), a
weighted pair with κ = e'' = 0 on both sides has C''_i ∩ C''_j ≠ ∅, hence κ(Z) ≥ 2 by (c). (A): (d) gives
Σκ(Z) ≤ 4, so one such pair, the other two are single vertices of weight 0, and w(A1_3) ≤ 1 < 5. (B): Σκ(Z) ≥ 6.
(C): Σκ(Z) ≥ 6 (f ≤ 1), so g(U'') ≤ 2. (D): κ(Z_23) ≥ 2 and (d) give κ(Z_12) + κ(Z_13) ≤ 1 + ε/3, while each is
≥ 2 unless its f ≥ 3 and f_12 + f_13 + ε ≤ 3. All impossible. (D) includes the sub-case left open in `NOTES.md`
§7.6: three C''_1-edges at a single N-vertex is ε = 3.

*V_0 ≠ ∅.* m(A1_i) ≥ m(V_0) forces k_i ≥ 2 and κ_i ≤ 0; \|V_0\| ≥ 2 or m(V_0) ≥ 2 makes every κ_i = −1 and
w(A) ≤ 4 + 3. So V_0 = {v0}, m(v0) = 1, and (a) gives w(v0) = Σθ + Σe'' − 2Σκ − 4 + w(Ex) + 2w(N) ≤ 2: at most one
κ_i = −1, and no C-vertex lies in all three C''_i.
All κ_i = 0: θ_i = 1, m(A1_i) = 1, m(N) = 3, Σe'' + w(Ex) + 2w(N) ≤ 3, κ(U'') = 7 − Σκ(Z). If \|N ∪ C_0\| ≥ 3,
(d) gives κ(U'') ≥ 2, so one κ(Z_ij) = 1 with f_ij = 3, then ε = 0 and g(N ∪ C_0) = 6. Otherwise N = {z} with
d_z ≤ \|C_0\| + ε: \|C_0\| = 1 gives κ(U'') = 2 and Σe'' ≥ 3 + 2; \|C_0\| = 0 gives ε = 3, all f = 0, all κ(Z) = 2,
w(v0) = 2, d_{v0} = 3. By (b) Σ_i e(v0, C''_i) ≥ 6, so each neighbour of v0 lies in some C''_i ∩ C''_j, and a tight
Z_ij containing v0 needs 3 of them; so all lie in C''_12, e''_3 = 3, Z_13 and Z_23 have empty C''-parts, \|I_13\| =
\|I_23\| = 1, while w(A1_3) = 8 needs w(I_13) + w(I_23) = 6.
One κ_1 = −1: Σe'' ≤ 1, so every κ(Z) ≥ 2, κ(U'') = 8 − Σκ(Z) = 2, \|C_0\| = \|N\|, and N = ∅ (d_z ≤ 2, or
g(N ∪ C_0) ≤ 8). The three M-units off v0 then lie in A1_1 only: m(A1_1) = 4 > k_1 − 1. ∎

So the exact remaining case of §5.4 can be sharpened from "at least three" to "at least four" core-type members.
The same tools (b) to (d) look usable for s ≥ 4, where the union U'' has more inclusion-exclusion terms; I did not
pursue it.
