# REVIEW3 log (referee lane for PAPER3)

- start 2026-10-05: FROZEN3.sha256 check all OK (PAPER3.md + 19 code/data files). Created review3/ and review3/code/.
- read PAPER3, PAPER2, PAPER, REVIEW2, REVIEW (fix list). Hand re-derivation so far:
  - Thm 2.1 both directions OK (if: PAPER2 Cor 2.3; only-if: REVIEW2's counting converse). I_X(M) avoids V(M) via dem(A-a)=4.
  - Lemma 3.1 (i)-(iv) OK; Lemma 3.2 OK; Lemma 3.3 trivial; Lemma 3.4 OK (kappa=0, e''=0, theta=1, w(T-a)=0).
  - Thm 4.2 chain OK given Lemma 4.1 (K=(T-a) cap V(E) is rigid). Cor 4.3 (b),(c) OK.
  - Prop 5.2, 5.3 OK on paper.
  - Observation: rigid K exists iff m(F) >= 3, F = {v in A-a : m(v)=c_v>=1, (v notin L or c_v=3)}, since c(F)=m(F)<=4.
- next: own code for Lemma 4.1 (own enumeration + canonical forms, literal subset check of K).
- Lemma 4.1 own code review3/code/lemma41.c (own enumeration: row-multisets + brute-force canonical form; and the grid enumeration; literal subset search for rigid K, cross-checked vs shortcut m(F)>=3):
  - classes: 142 (per-cell counts equal genbg -d1:1 -D3:3 na nd 7:7 in all 25 cells), 36,339 labelings, 0 failures (paper), 607 (loose), 0 (plain).
  - grid: 22,792 matrices, 15,342,638 labelings, 0 failures (paper), 338,494 (loose, = paper), 0 (plain). shortcut == literal everywhere.
  - => Lemma 4.1 confirmed; paper's counts reproduced exactly.
- hand analysis toward KL1: case s=3, t=0, all kappa=0, e''=0, all |I_ij|<=2 is impossible (weight count forces |N|=|C_0|=1 and then e(c0, union A1) >= 5 > m(z) <= 3). Other cases open.
- Thm 2.1 vs own Dinic max flow (review3/code/thm21.py, r3lib.py): cert n28 (1), core28 (24), e5_n22 first 5, e5_n24 first 5 = 35 instances; every P x Q pair, BOTH decompositions of each instance (each instance has 2: X/Y swap): 0 disagreements (392 + 9408 + 1210 + 1440 pairs). good pairs on core28: 54..60. All 35 M X-good and Y-good in all 35 instances (both decompositions). Claim A.1 confirmed.
- next: C checker for KL1 / Lemma 3.2 / 3.4 / Prop 5.2 / 5.3 on blocks (all admissible cut vectors), then the 6.1 example, then the 1,750 blocks.
- blk3.c (own block checker: KL1, Lemma 3.1(i),(ii),(iv), 3.2, 3.4 shape, Prop 5.2, 5.3, extendable-multiset count):
  - 6.1 example: block-sparse, L_A={a}, 129 extendable covering multisets (= paper), KL1 holds; case (b) occurs (3 M's with the stated cut vector, 96 over all 336 admissible cut vectors); Lemma 3.4 shape holds every time; dem(U)=2 by hand.
  - 1,750 blocks (875 instances, both blocks): 89,194 extendable covering multisets, 0 failures (= paper). With all 194,055 admissible cut vectors: 2,431,923 covering (c,m), 0 KL1 failures, 0 violations of L3.1/3.2/5.2/5.3; case (b) never occurs in these blocks.
- hand: s=3, t=0, all kappa=0, e''=0: also the (one 2-block intersection + two singletons) and (all 2-block intersections) sub-cases are impossible (union of the three X'' has g = 36 - 6*sum kappa(Z_ij); weight count). So that whole sub-case is closed.
- SAT search tool review3/code/kl1sat.py (PySAT/CaDiCaL in the research venv; own totalizers; lazy block sparsity; exact re-check of I_X by enumeration).
  - test mode caseb: finds case-(b) blocks at once at |A|=11 (|X|=20, smaller than the paper's 22) and |A|=12; blk3 confirms: sparse, I_X=empty, Lemma 3.4 shape holds in all 69 case-(b) occurrences, KL1 holds on them. (data/caseb_sat.blk)
- next: KL1-failure search, s = 3, 4, nA = 11..16.
- 6.1 block embedded in a full sparse E5 instance (Y = K_{4,6}, cut 0-0 1-1 2-2 3-3 6-4 7-5 8-0): n=32, e=91, sparse (S_P enumeration, max e(S)-3|S| = -6), no 4-factor; the three M with A-ends {1,2,3,x}, x in {6,7,8}, miss only L-vertex 0 and have I_X = empty. So case (b) occurs in an actual sparse E5 instance without a 4-factor (contains K_{4,4} in Y, so not a QB(5) counterexample). 61 good pairs. data/ex61_embedded_n32.g6.
- SAT KL1 search v1 at |A|=12, s=3: first solve did not finish in 2.3 CPU-min (killed). s=1 UNSAT at once (as Prop 5.2 predicts); s=2 gives non-sparse models that need lazy constraints. Next: v2 with WLOG anchors x_i (minimal core family: x_i in all A1_j, j != i, not in A1_i, m(x_i)=0) and symbolic sparsity constraints for S_A in {A1_i, T_i, A1_i - x, unions}.
- SAT v2 (anchors+symsp) s=2 nA=12: first solve > 230 s (CDCL weak at the weight arithmetic). Search by SAT at these sizes is not productive; switching effort to hand analysis + targeted checks.
- HAND (referee observation): s = 3, t = 0 is impossible in all four parameter cases allowed by the weight count:
  (A) kappa=0, theta=(1,1,1), e''=0; (B) kappa=0, theta=(2,1,1), e''=0; (C) kappa=0, theta=1, e''=(1,0,0); (D) kappa=(1,0,0), theta=1, e''=(3,0,0).
  Tools: u in A1_i cap A1_j has >= 3+3kappa_i-e''_i nbrs in C''_i (L3.1(iv)) for each, so small pairwise intersections carry no weight; c in C''_i cap C''_j forces a sub-2-block Z_ij (kappa >= 2); union U'' of the X''_i has kappa(U'') = sum kappa(X''_i) - sum kappa(Z_ij), g(U'') = 6 kappa(U'') + 2 e(C'', N) >= 12; N u C_0 has g = 2 delta(N) (+2eps). Details in REVIEW3 appendix.
- 6.2 data claims: author's search logs (data only): kls_10..13 'best 6..9' (= |A|-4, no core-type set), kp_10..13: 400 starts each = 1,600 starts (text says 'about 1,300'): minor text discrepancy. 25 of the 1,750 blocks have a non-generic vertex (own generic3.c; 76 non-generic vertices), matching 'only the 25 blocks with a core are informative'.
- Lemma 4.1 '33.5 million' rigid rejections: not a definitional count (depends on search order with early exit); my full count over (labeling, M, side) is 375,034,802 on the grid. Immaterial; the activity of the rigid condition is confirmed by loose-mode failures.
- running: SAT v2 anchors-only, (nA,s) = (14,3), (16,3), (16,4), 400 s each.
- SAT v2 anchors-only runs (14,3), (16,3), (16,4): killed at 420 s; (14,3) reached 1 non-sparse model (66 s/solve); others no model. No counterexample; SAT not effective here.
- HAND (referee observation, continued): s = 3 with a trivial member also impossible. |V_0| = 1, m(v0) = 1, kappa_i <= 0; at most one kappa_i = -1. All-kappa-0: m(N) = 3, union U'' has kappa = 7 - sum kappa(Z'_ij), Z'_ij = (A1_i cap A1_j) u (C''_i cap C''_j), kappa(Z') = 1 needs f >= 3 edges leaving it, sum e'' >= sum f + eps, N u C_0 has g = 6(kappa(U'') - 2) + 2 delta(N) + 2 eps; the only branch left (|N| = 1, C_0 empty, eps = 3) dies at v0 (each tight Z'_ij containing v0 needs 3 nbrs of v0). One kappa = -1: sum e'' <= 1 forces kappa(U'') = 2, N empty, then m(A1_1) = 4 > k_1 - 1. => a KL1 failure needs a minimal core family with s >= 4.
- re-checked the s = 3 closure line by line (t = 0 cases A-D; t = 1 all-kappa-0 incl. |C_0| = 1 sub-branch; one kappa = -1). Writing REVIEW3.md now. Compute so far ~40 core-min.
- REVIEW3.md written (FINAL). End check: shasum -a 256 -c FROZEN3.sha256 -> 20 OK, 0 failures. Nothing edited outside review3/ and REVIEW3.md. Total compute ~40 core-min.
