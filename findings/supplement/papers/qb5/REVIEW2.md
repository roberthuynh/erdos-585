# REVIEW2: QB(5) round 2, the E5 pair statement for generic blocks (wave4/qb5/PAPER2.md)

Independent adversarial referee, October 5, 2026. Status: FINAL.
Object: `PAPER2.md` as frozen in `FROZEN2.sha256` (`shasum -a 256 -c FROZEN2.sha256`: all 22 entries OK at
the start and at the end of this review; `FROZEN.sha256` of PAPER.md also all OK). Working files, log and
code: `review2/` (`review2/LOG.md`, `review2/code/`). Nothing here is a project-oracle PASS: no Lean, no
`check.sh`.

Method. Every proof step was re-derived by hand. Every computation was redone with code written from scratch in
`review2/code/`. Nothing in `qb5/code/` was run, imported or read; the author's `.g6` files and search logs were
used only as inputs. Generators: my own enumerations, plus plain nauty genbg 2.9.3, checked against my own class
count (7-edge cuts) and by an orbit count and labelg (2-blocks). Compute used: about 35 core-minutes.

## 1. Verdicts

| Claim | Verdict | Short reason |
|---|---|---|
| **Fact 2.1** (a 4-factor of G − p − q forces p ∈ A, q ∈ D and exactly 4 cut edges, none at p, q) | **ACCEPT WITH FIX** (G1) | Proof correct for p ∈ P, q ∈ Q, the convention of §0. Fact 2.1 and the definition of a pair (§1.1) do not state it, and with the labels swapped the statement is false as written. Checked: no good pair outside A × D in 125 instances, all P × Q pairs. |
| **Theorem 2.2** (pair criterion) | **ACCEPT** | Re-derived: the decomposition A' = A1 ∪ B1, C' = C1 ∪ (D − q − D1) is a bijection, e(B1, C − C1) = 0, the two brackets separate, both minima and the identity Σ_b (4 − e(b, D1))^+ = 4\|B\| − 4\|D1\| + dem_Y(D1) are right, and \|D\| − \|B\| = 2 gives the constant 4. Only PAPER.md Lemma 1.5 and Theorem 6.1 structure used. Criterion = own max flow on every A × D pair of 185 instances. |
| Corollary 2.3, Lemmas 3.1, 3.3, Corollary 3.4 | ACCEPT | Re-derived, including the three cases of Lemma 3.3(a) and the relevance case (ii). |
| **Lemma 4.2** (covering lemma, computed) | **ACCEPT** | Confirmed by three of my own programs, two of them independent in both enumeration and decision method; 0 failures; both of the paper's counts reproduced exactly (§4). |
| **Theorem 4.1** (every vertex of A and D generic ⇒ some G − p − q has a 4-factor) | **ACCEPT** | §4.1 checked: the cut of G meets every hypothesis of Lemma 4.2 by (B1), (B2). Then Lemma 4.2 plus Corollary 3.4 (converse). |
| **Proposition 5.1** (a non-generic vertex forces a core; block ≥ 18) | **ACCEPT** | Steps 1 to 7 re-derived, in particular Step 4 (\|C''\| = 1, 2 each contradict e(C'', T) + δ_p ≤ 2κ + 3) and Step 6 (all t < 5 + κ excluded for κ = −1, 0, 1). Exhaustive part reproduced exactly: 0 relevant non-generic sets in blocks ≤ 16. (a) to (d) hold on all 76 actual cores found. |
| **Corollary 5.2** (pair statement for n ≤ 26) | **ACCEPT** | \|X\|, \|Y\| ≥ 10 and n ≤ 26 give both blocks ≤ 16, so every vertex is generic, then Theorem 4.1. No counterexample in 8,000 instances from my own generator. |
| Corollary 5.3, Remark 5.4 | ACCEPT | Corollary 3.4's converse applied to a covering pair. Remark 5.4's slack formula re-derived (with D1 = D the optimal B1 is empty); checked on 875 instances. |
| **§6: natural step first fails at n = 28; the pair statement still holds there** | **ACCEPT** | The lower bound is Corollary 3.4 + Proposition 5.1 + \|Y\| ≥ 10 (n is even). The certificate verified independently: sparse (all 2^28 sets), E5, no 4-factor, (0, 25) bad (flow 51 of 52) while E − E(0) − E(25) is a covering 4-set, non-generic vertices exactly T = {0, 1, 2, 3}, 56 good pairs. |
| **§7: data and exact residual** | **ACCEPT WITH FIXES** (G2, G3) | (R1) ⇒ QB(5) and (R2) ⇒ QB(5) are correct. Every data claim I could re-run is right. Two text fixes: the citation for (R1), and the "permissive model" sentence, which the text never defines. |

No REJECT. I found no mathematical error. The E5 pair statement is now proved for n ≤ 26 and for every instance
whose big-side vertices are all generic. It remains open in general, as the paper says.

## 2. Required fixes, with locations

- **G1** (Fact 2.1, lines 91-97; also the definition of a pair, line 61). The proof sums H-degrees over A − p
  and reads "[q ∈ C] = 0" as "q ∈ D". Both steps need p ∈ P, q ∈ Q. If q ∈ A, then q ∈ A − p is not in H. If the
  pair is written (d, a) with d ∈ D, a ∈ A and G − d − a has a 4-factor (56 such pairs in the §6 certificate),
  the conclusion "p ∈ A" is false. Fix: state p ∈ P, q ∈ Q in §1.1 or in Fact 2.1. Equivalently, add "a 4-factor
  of a bipartite graph has equal sides, so p and q lie on opposite sides; call the P-vertex p". Theorem 2.2 and
  everything after it already assume p ∈ A, q ∈ D.
- **G2** (§7, line 315). "By Theorem 4.1 and Corollary 5.3, QB(5) follows from either of (R1), (R2)." (R2) ⇒ QB(5)
  is Theorem 4.1 or Corollary 5.3, as cited. (R1) does not need all vertices to be generic, so it does not go
  through Theorem 4.1. It goes through Corollary 3.4 (converse): a covering pair with generic ends is good. That
  gives the E5 pair statement, and then PAPER.md §8.4 and Theorem 7.1 give QB(5). Cite Corollary 3.4 for (R1).
- **G3** (§7, lines 319-322). "a permissive model that admits every vertex set satisfying them as a core
  (`code/core_model.py`) can make every vertex of one side non-generic, even with Remark 5.4". The paper never
  states which constraints the model imposes or what instance it produces, so a reader cannot check the claim
  from the text, and I did not run the author's code. Either define the model and give the assignment in the
  text, or label the sentence as an unrefereed observation from `code/core_model.py`. Nothing else depends on it.

Optional, editorial:
- Line 270: PAPER2's own "Theorem 6.1" (the natural step) has the same number as PAPER.md Theorem 6.1, which
  PAPER2 cites on lines 51, 246, 259. Renaming it (for example Proposition 6.1) avoids confusion.
- Line 227 (Proposition 5.1, Step 5): the set "Q = A1 ∪ C''" reuses the name of the side Q.
- Lines 127-129: the converse of Corollary 2.3 is elementary and needs no matroid intersection. If H is a
  4-factor of G − p − q with cut edges M, then 4\|A1\| = e_H(A1, C) + m^A(A1) ≤ Σ_c min(4, e(c, A1)) + m^A(A1),
  so m^A(A1) ≥ dem_X(A1), and the same holds on the D side.
- Lemma 4.2 has slack. With the budget raised to 6 or 7 on both sides, my program still finds 0 failures; at
  budget 9 it finds 7,820. A one-line remark could help later work.

## 3. Proof notes (re-derivation, adversarial points)

- **§1.** (B1): g(K − v) = 12 − 6 + 2d_v ≥ 12 with \|K − v\| ≥ 9. If c_v = 3, then δ_v ≥ 3 forces d_v = 3 and
  def(v) = 0. (B2): deg v = 3 + c_v ≥ 4 and def(v) = 3 − c_v, so Σ_{L_A} def ≤ D(A) = 5. Σ_A δ = 6\|A\| − 6\|C\|
  = 12 = 7 + 5.
- **Fact 2.1.** With p ∈ P, q ∈ Q: e_H(A, D) = 8 − 4[p ∈ A] + 4[q ∈ C] ∈ {0, ..., 7} and is divisible by 4. So
  p ∈ A, q ∉ C, e_H = 4 (see G1).
- **Theorem 2.2.** Lemma 1.5 (max-flow min-cut: s → P cap 4, Q → t cap 4) applies to H. Edges at p and q cannot
  appear in e(A', Q' − C'). First bracket: put c in C1 iff e(c, A1) > 4, giving −dem_X(A1). Second bracket: put b
  in B1 iff e(b, D1) < 4, giving 4\|D\| − 4 − 4\|D1\| − (4\|B\| − 4\|D1\| + dem_Y(D1)) = 4 − dem_Y(D1).
- **Corollary 2.3.** E(A1) ∩ E(D1) = E(A1, D1), and \|M ∩ (E(A1) ∪ E(D1))\| ≤ 4.
- **Lemma 3.1.** e(c, A − p) ≥ 5 for every c. For \|A1\| ≤ 4 the minimum with 4 is never active.
- **Lemma 3.3.** (i) is the single set A − p. (ii): E(A1) and E(A − p − A1) partition M ∩ E(A − p) = M. (iii):
  distinct vertices of A1 ∩ L_A are the A-ends of distinct M-edges. (b) uses dem_X({a}) = 1.
- **Lemma 4.2 decision.** For fixed (p, q), with F = E − E(p) − E(q) and L' = (L_A − p) ∪ (L_D − q), a covering
  4-set exists iff \|F\| ≥ 4, every vertex of L' has an F-edge, and \|L'\| − ν(F[L']) ≤ 4 (minimal edge covers
  are star forests). By König, max over A1, D1 of \|A1\| + \|D1\| − e(A1, D1) equals \|L'\| − ν. So the
  paper's rule (a) to (d) in program (2) is exactly the failure condition.
- **Proposition 5.1.** Step 1: e(c, A1) ≥ 4 on C'' and ≤ 3 on C'. Step 2: t = 2 gives C' = ∅, κ = 2, k = 0.
  Sparsity of T ∪ C' gives κ + k ≤ 2. Step 3: δ(T) = 6t − e(C', T) − e(C'', T). Relevance, with c_v ≤ δ_v, gives
  e(C'', T) + δ_p ≤ 2κ + 3, hence κ ≥ −1 and k ≤ 3. Step 4: C'' = ∅ gives k = Σ_{A1}(4 − d_a) ≤ \|A1 ∩ L_A\|. For
  \|C''\| = 1: κ = −1, \|A1\| = 4, e(C'', T) ≥ 2 > 1. For \|C''\| = 2: κ = −1 gives 2 > 1, and κ = 0 gives 4 > 3.
  Step 5: g(A1 ∪ C'') = 12 − 6κ + 2e(C'', T). Step 6: (6 − t)(t − κ) ≤ 7 − 4κ excludes t = 3 (κ = −1),
  t = 3, 4 (κ = 0) and t = 3, 4, 5 (κ = 1); κ = 2 is impossible since k ≥ 1. Step 7: \|X\| ≥ 2(5 + κ) + 6 + 2 − 2κ = 18.
  The §6 certificate attains κ = −1, e(C'', T) + δ_p = 2κ + 3, c(T − p) = 5 − k, \|C''\| = 3, t = 5 + κ and
  \|X\| = 18.
- **Corollaries 5.2, 5.3; Theorem 6.1 of PAPER2.** As stated. n is even, so n = 27 does not occur.
- **Remark 5.4.** With D1 = D, every b has e(b, D) = 6 > 4, so B1 = ∅, and the slack is c(A1) − dem_X(A1) ≥ −1.
  Equality gives the violation (A1, {c : e(c, A1) ≥ 5}), whose X-side is strictly inside X when A1 ⊊ A.
  P-violations and Q-violations correspond by complement ((A, C) ↔ (D, B), slack 7 − 8 in both), so making X
  minimal makes Y maximal. That fits the last sentence of the remark.

## 4. Computations (own code, `review2/code/`)

| Check | Code and input | Result |
|---|---|---|
| Lemma 4.2, program I | `lemma42.c`: own enumeration (rows sorted, every column used), direct search over p, q, M, superset closure | 4,941 labeled graphs, 142 classes (own canonical form; per-(na, nd) counts equal to genbg `-d1:1 -D3:3 na nd 7:7` in all 25 cells), 1,617,633 labelings, 0 failures (p, q ends of cut edges), 0 failures (outside vertices allowed) |
| Lemma 4.2, program II | `lemma42_konig.py` on genbg classes; decision by the edge-cover formula, no search | 142 classes, 36,339 labelings (= PAPER2), 0 failures in both modes |
| Lemma 4.2, paper's enumeration | `lemma42_grid.c`: the enumeration as described in §4 (1), own decision | 22,792 graphs, 15,342,638 labelings (both = PAPER2), 0 failures in both modes |
| Lemma 4.2, sensitivity | `lemma42.c` with changed parameters | budget 6, 7: 0 failures; budget 9: 7,820; \|M\| = 5: 3,268 (so the decider can fail) |
| Prop. 5.1 exhaustive | `prop51.c` (own sparsity DP, demands, relevance over all cut vectors allowed by §1.2) on genbg `-q -d6:0 -D6:6 c c+2 6c:6c` | graphs 1, 7, 197, 18,208; sparse with d_a ≥ 3: 1, 3, 94, 11,842; candidate sets 0, 0, 2, 442; relevant: 0. All as in PAPER2. Generator complete: side-preserving orbit sum = labeled count by inclusion-exclusion for c = 4 to 7; labelg finds no duplicates |
| §6 certificate | `sparse_gray.c` (Gray code, all 2^28 sets), `cert_check.py` + `e5lib.py` (own graph6 parser, own Dinic) | string equal to PAPER2 line 280; n = 28, e = 79, Δ = 6, δ = 4, D(P) = D(Q) = 5; max e(S) − 3\|S\| = −6 (tight: X, Y, V − 5, V − 22, V − 23), 0 violating sets; one violation (A, C); all listed neighborhoods, cut and degrees as stated; L_A = L_D = ∅; no 4-factor (55/56); G − 0 − 25 none (51/52); witness numbers 2, 4, 1 and relevance 5; 56 good pairs, all in A × D, (0, 22), (4, 22) good; criterion = flow on all 60 A × D pairs; covering rule wrong exactly at (0..3, 25); non-generic vertices exactly {0, 1, 2, 3}, none in D |
| Sparsity checker | perturbed certificate (+ edge 5-22); 40 random graphs, n = 8 to 14 | flagged (V − 23); 40 of 40 equal to brute force |
| §7 core instances | `data_check.py core28.g6` | 24: sparse E5, no 4-factor, one decomposition each; good pairs 54 to 60, none outside A × D; covering rule wrong on exactly 20 pairs, all at a non-generic p; non-generic vertices all in {0, 1, 2, 3}; criterion = flow on every A × D pair |
| §7 built instances | `data_check.py e5_n22.g6, e5_n24.g6` | good pairs 35 to 40 and 40 to 47, none outside A × D; every vertex generic; criterion = flow on every pair |
| §7 random dump | `data_check.py dump_mixed.g6` | 750 (n = 24, 26): sparse E5, no 4-factor; every vertex generic; covering rule = flow on every A × D pair; criterion = flow on the first 60; fewest good pairs 23 |
| §7 search logs | author's `ps_*.err`, `st_*.err` (data only) | 54 runs, 34,255 sparse instances, fewest good pairs 23, n = 20 to 26: as stated (generator not re-run) |
| Prop. 5.1 on actual cores, Remark 5.4 | `core_props.py` on certificate + core28 + built + dump (875 instances, both blocks) | 76 cores (p, A1) (4 + 72); every condition of (a) to (d) holds; dem_X(A1) ≤ c(A1) + 1 for all A1, ≤ c(A1) for proper A1; c(A1) ≥ k on every core |
| Stress test (extra) | `stress.py`: own generator (random sparse 2-blocks, random admissible 7-edge cut), half with a cut vertex cover of size ≤ 3 | 8,000 sparse E5 instances without a 4-factor (n = 20, 22, 24, 26: 426, 1,653, 2,546, 3,375; cut matching number 3 in 4,046): every vertex generic, every instance has a good pair (at least 27), covering rule = flow on every A × D pair |

## 5. F1 to F7 carried over

All seven are in PAPER2 §1.3 with the content of REVIEW.md §2. F1 (coefficient 1 in the h-form), F2 (n ≥ 3;
t ≥ 1), F3 (0, 0, 3 at n = 11, 13, 15), F4 (n = 19 for W-vertex petals of degree 6, n = 21 for ports;
`review/data/cert_portsplit_n21.g6` present with the REVIEW.md string), F5 (18 and 33 classes; good pairs only in
A × D, now proved as Fact 2.1), F6 (`reports/585-next/STATE.md` line 31 records F1(18) as complete; CENSUS.md line
37 records it as projected; REVIEW.md §4's second method), F7 (9, 447 and 115,932 graphs). PAPER.md's hash in
Appendix B matches. Where PAPER2 relies on PAPER.md, it uses the corrected forms (F5: classes and "only";
F6: n ≥ 40).

## 6. What this review adds

1. Lemma 4.2 confirmed by enumerations and deciders independent of the author's code, with both of the paper's
   counts reproduced. It still holds with the budget raised to 7.
2. The obstruction rule of program (2) is proved to be exactly the failure condition (edge covers plus König).
3. The converse of Corollary 2.3 has a two-line counting proof.
4. Corollary 5.2 is backed by 8,000 instances from an independent generator, 4,046 of them with cut matching
   number 3, the case a minimal counterexample must have (PAPER.md Lemma 6.2).
