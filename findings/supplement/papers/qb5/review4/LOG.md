# REVIEW4 log

- 23:19 start. FROZEN4.sha256: all 16 entries OK.
- 23:19 read PAPER4, PAPER3, REVIEW3. Next: PAPER, PAPER2, REVIEW, REVIEW2.
- 23:20 read PAPER, PAPER2. Next: REVIEW, REVIEW2, then hand re-derivation of PAPER4 §2-3.
- 23:31 hand re-derivation of PAPER4 §2 (Lemmas 2.1, 2.2) and §3 (Lemmas 3.2-3.5, Thm 3.1) done once: no error found yet.
  Lemma 3.3 m(v)=3 equality case, 3.4(c) single-vertex case, 3.5(a) S_i ∩ S_j = K+, final counts all re-derived.
- 23:31 (N1) analysis by hand: using g(X'(T) - a) >= 12 for every a in a big overloaded T gives e(a, C'(T)) >= 5 - m(T) + kappa + theta.
  For an (N1) pair this forces m(a) = 3, |J| = 1 with a ~ c*, b in exactly one of T, T' (m(T)+m(T') = 7), (kappa,kappa') in {(-1,-1),(-1,0)}.
  m(a) = 2 impossible. So (N1) needs |X| >= ~28; the data blocks have |X| <= 22, which explains 0 (N1) in the data.
- 23:31 data: blocks1750_all.blk has |A| <= 10; caseb_sat |A| = 11, 12; §6.1 block |A| = 12. Next: own C checker review4/code/kl1rev.c.
- 23:33 code/kl1rev.c (own, from scratch): validates (H1)-(H3) incl. block sparsity via the subset form
  sum_c (e(c,T)-3)^+ <= 3|T| - 6 for |T| >= 3; enumerates m; checks Lemma 2.1 identities (random S), 2.2(b)(c),
  3.2 on all pairs of maximal sets, 3.3 (hub-free family never covers; minimal subcovers), 3.4/3.5 on the whole
  maximal family whenever two maximal sets share >= 3, per-petal bounds of Thm 3.1 for covering m, and KL1.
  §6.1 block rebuilt from PAPER3 text: identical to the last line of code/r4/blocks_r4.txt.
- 23:33 run on 1,753 blocks (data/data1753.blk): counts identical to merge_check.out (165,610 / 89,438 covering;
  pairs 332,806 disjoint, 0 one-vertex, 0 two-vertex, 9,612 >= 3; I_X empty 0 covering, 9,612 non-covering;
  9,612 minimal subcovers, 0 hub-free; all 9,612 with a w=3 one-vertex petal). All violation counters 0.
- 23:35 (N1) by hand, sharpened: the only possible (N1) pair is m(a)=3, theta*=(1,1), m(T)=3, m(T')=4 (b in T'),
  kappa(X'(T)) = kappa(X'(T')) = -1, C'(T) n C'(T') = {c*} with a ~ c*, T-a and T'-a saturated (except deg b = 5),
  c* with exactly 3 nbrs in T-a and 2 in T'-a. ((-1,0) and (0,-1) die on deg c* >= 7 / the h(S') budget.)
  Then no third big maximal set can contain a (it would need b, already in T'), so the maximal family is {T, T'}
  and I_X = A - T - T' is nonempty: (N1) configurations are harmless for KL1, consistent with Lemma 3.3.
- 23:35 code/gen_n1.py plants exactly that structure (|A| = 15, |X| = 28): 200 generated, 148 block-sparse.
  kl1rev -v: 148 (N1) pairs, every one with m(a)=3, theta*=(1,1), m(T)=(3,4), kappa=(-1,-1), |J|=1, a~c*, covering,
  I_X = Z (4 vertices). All violation counters 0. So (N1) DOES occur in sparse blocks (first time exercised).
- 23:40 (N1) sweep (code/run_n1.sh, data/run_n1_sweep.log): |A| = 15..19, 8 size configs x 40 blocks; 241 sparse
  blocks, each realizes the planted (N1) pair (plus 196 from the first two runs: 437 in all). Every (N1) has exactly
  the predicted shape; I_X = Z nonempty every time; 0 violations of any check. (W nonempty needs |Z| >= 6.)
- 23:40 next: hub + covering m (never in the data: all 9,612 data hubs are non-covering), via planted hubs.
- 23:41 kl1rev now counts hubs under covering m. Data: 0 of the 9,612 data hubs are under a covering m, so the
  covering part of the Thm 3.1 count was never exercised by the author's data. Hand note: {y,c} and {y,y'} petals
  are impossible (c in P_i needs e(c,Q_i) >= 2; {y,y'} would need e(X,y)+e(X,y') = 7-m(Q) while theta*(K+y) <= 1
  caps it at 6-m(Q)), so petals are {y} or |P_i| >= 3; the paper's extra cases are harmless.
- 23:42 code/gen_hub.py (planted K+ templates A45, B56, D55 + {y} petals): first sweep 259 blocks, all sparse,
  hubs under covering m: 259 (beta 227, delta 32), 584 {y} petals; 0 violations; I_X never empty.
- 23:43 second hub sweep (data/run_hub2_sweep.log): 12 configs, |A| 11-13; hubs under covering m: 3,305
  (beta 2,741, delta 564), {y} petals 7,782; no big petal produced by the planted generator; 0 violations; I_X
  never empty. Hand note: in case beta a petal's C-part has no K-neighbor (d_A(K+) = 0), so big petals need
  e(c, Q_i) >= 3; tight kappa = 0 big petals need |P_i| >= 10. Next: SA perturbation from planted-hub starts.
- 23:46 SA (code/sa_kl1.c, energy 10*min_cov |I_X| - bigcov - ...; 2 workers, starts = planted hubs, (N1)
  blocks, data blocks; 300k steps each): ~570k distinct hub blocks dumped so far, no covering m with I_X empty.
- 23:46 (N1) supplement by hand: with an (N1) pair the maximal family is exactly {T, T'} and
  |A - T - T'| >= 4 (|C| >= |C'(T) u C'(T')| = |T| + |T'| + 1), so |I_X(M)| >= 4 for every M with an (N1) pair.
- 23:46 code/lem41.c (own Lemma 4.1 check, literal rigid-subset search) compiled; run after the SA workers.
- 23:48 code/lem41.c: 8 degree sequences per side, 22,792 matrices, 15,342,638 labelings; refined 0 failures,
  loose 338,494, plain 0 (27 s). Equal to PAPER3 A.2b and REVIEW3 §4.
- 23:49 code/zcheck.py (side check of the §0 heuristic, own max flow): p in I_X(M) iff X+z-p has a 4-factor on
  4,912 (block, m, p) triples, 0 disagreements. X+z has parallel edges (424 of the sampled m) and fails sparsity
  also at {z, a, c} with m(a) = 3, a ~ c (g = 10; 156 cases), which is not of the "z + S, S tight with every end"
  form stated in §0. Unused in PAPER4's proofs: editorial only.
- 23:49 SA finished: 45 runs (3 invalid starts skipped), 717,372 distinct dumped blocks (|A| = 10..15): 712,463 with a
  hub under some covering m, 4,909 with an (N1) pair; 0 with a covering m and I_X empty. kl1rev now running on all
  dumps (dump_1 407,566 lines, dump_2 309,806), one process each.
- 23:50 kl1rev on SA dump_1 (407,566 blocks, |A| = 12, 13): 45.4M multisets (37.3M covering); 408,692 hub
  multisets under covering m (beta 408,550, delta 142), 818,554 {y} petals; I_X empty only for 32,353
  non-covering m, each with a w=3 one-vertex petal; all violation counters 0. Still no petal with |P| >= 3.
  Next: planted big petal (tight kappa=0 petal K_{5,5}-e on Q u P_C, E = 5) next to an A45 hub.
- 23:52 big petal: code/gen_big.py (A45 hub + {y} + tight K_{5,5}-e petal, E = 5): 300 blocks, 300 big petals
  (|P| = 10, kappa = 0) under covering m; 0 violations. kl1rev on SA dump_2 (309,806 blocks): 0 violations;
  all 4,909 (N1) pairs of the predicted shape. Covering hubs with a singleton member (Lemma 3.4(d)) occur
  (2,198 in planted files), up to 3 big maximal sets around one hub.
- 23:52 totals (own instances, all sparse): data 1,753; planted (N1) 397; planted hubs 1,806; big petal 300;
  SA 717,372. Covering hub multisets: 3,704 + 300 + 713,808; violations 0 everywhere; covering I_X empty: 0.
- 23:53 hand: {y,c} and {y,y'} petals cannot occur ({y,y'} needs E = 7 - m(Q) but Lemma 3.4(a) caps
  e(y, K+_C) <= 3 - m(y)). PAPER4 line 27 "every lemma of §3 checked" overstates F1-F5 (no Lemma 3.5,
  no hub under covering m in the data): wording fix J1. Writing REVIEW4.md now.
- 23:56 note: stamps from 23:33 on were corrected to file modification times (hand-typed stamps had drifted).
- 23:56 end. FROZEN4.sha256: all 16 entries OK. REVIEW4.md written: FINAL, overall ACCEPT WITH FIXES (J1 required wording at PAPER4 line 27 / §5; J2-J4 optional). SA dumps gzipped (data/sa/*.gz). Compute about 20 core-minutes.
