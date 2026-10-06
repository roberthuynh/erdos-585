# wave3/pairs LOG (scout, CONTINUE.md step C1)

Lane: Pass 3 wave 3, pairs scout. Writes only in this folder. No git, no check.sh, no subagents.

## Done
- 2026-10-05: read STATE.md, CONTINUE.md, G110/C1-PAPER.md, 585-fable/W1-MINIMAL.md, 585-fable/REPORT.md,
  585-RESEARCH-PLAN.md lines 127-330, 585-fable/tools/README.md.

## Next
- Survey tools (pairc, genbg, census dir), write a spanning-pair tester.
- Generate sparse E4 / sparse C1 instances (bipartite) at small sizes; test candidate statements.
- 10:05-10:20: wrote ptool.c (sparsity by flows, validated vs brute force on 42 graphs; spanning-pair test;
  C1 port test). Results so far:
  - sparse E4 (genbg -d4:4 -D6:6 a a 6a-4): a=6: 10/10 sparse, all spanning pair; a=7: 267/267, all SP;
    a=8: 52,280 of 52,295 sparse, all 52,295 have a spanning pair (two edge-disjoint Ham cycles).
  - sparse C1 (genbg -d5:4 -D6:6 s s+1 6s-1): s=5..8 (1, 8, 518, 182,908; all sparse): every port good
    and every G - y has two edge-disjoint Hamilton cycles.
  - connected bipartite 4-regular, a=5..10: non-HD counts 0,0,0,1,2,17; all non-HD ones have a 2-edge cut.
- 10:22: E4 a=9 (n=18) census DONE: genbg -q -d4:4 -D6:6 9 9 50:50 in 100 shards piped to ptool H:
  31,662,400 graphs, every one has two edge-disjoint Hamilton cycles (sparse or not). Files data/e4a9/.
- q4 a=11 (connected bipartite 4-regular, n=22) running (run_q4a11.sh); built sparse C1 instances with bad
  ports (C1 lane builder, n=27,29) under port test (data/built_c1_*).
- 10:40: built sparse C1 instances (C1 lane builder c1build.py, imported read-only with no bytecode):
  8 at n=27 and 22 at n=29, all exactly sparse; every port is good except 1-2 bad ones (bad deficiency <= 2,
  as Lemma 4.4 says); at EVERY good port y, G - y has two edge-disjoint Hamilton cycles (ptool2 with a
  randomized Warnsdorff first-cycle search; witnesses found, so these answers are certain).
  So "every port" must read "every good port" (bad ports have no 4-factor at all).
- C1 s=9 census for W1b(19) is ~150M graphs and ~17 core-h of generation alone (two 1/1000 slices: 149,488
  and 150,429 graphs, 59-62 s each): NOT run.
- 10:55: general graphs, one-mark statements (part (b)). Built every pair-free level -5 graph Z on <= 11
  vertices from the 17 cores (frontier-n7..10-level-5.g6) plus degree-3 vertices (5,625 graphs: 1, 4, 41,
  457, 5,122 at orders 7..11; labelg dedupe). mpair.c (exhaustive marked pair test):
  - T1 (prescribed pairing, W1-MINIMAL 4a "free-partner one-mark" claim): Y = Z + ab + cd, 76,975 marked
    instances; 6 have NO compatible pair, all on 11 vertices. Verified independently by full cycle
    enumeration (verify_t1.py, networkx simple_cycles): no compatible pair, Z pair-free, and X = Z + v
    (12 vertices, level -4) has pairs through v only with the two other pairings. So W1-MINIMAL 4a's
    statement is FALSE at m = 11 (not only its proof). data/t1_none.txt.
  - T2 (pairing richness): for X = Z + v, deg v = 4, Delta <= 6 (66,992 graphs X on <= 12 vertices),
    pairs through v realize >= 2 of the 3 pairings in every case; exactly 2 in 82 cases (4 at n=11, 78 at
    n=12). data/t2_res.txt, data/t2_none.txt.
- 11:05: q4 a=11 DONE: genbg -q -c -d4:4 -D4:4 11 11 44:44 in 24 shards piped to ptool H: 5,582,592
  connected bipartite 4-regular graphs on 22 vertices (genbg keeps the color classes, so asymmetric
  graphs may appear twice), 236 without a Hamilton decomposition, and every one of the 236 has a 2-edge
  cut (cuts.c Gray-code enumeration). With a <= 10: every connected bipartite 4-regular graph on <= 22
  vertices without a 2-edge cut is HD ("H22"). data/q4bip_a11_nonhd.g6.
- Plan: closure attempt on Lemma 2EC (sparse instance has a 4-factor with no 2-edge cut; for C1 at some
  good port). With H22 it would give W1b for n <= 23 (minimal counterexamples are sparse).
- 11:30: SP REFUTED at n = 20. data/rigid20.g6 = two K_{5,5} (T, W) joined by a perfect matching T_P-W_Q
  (5 edges) and one edge T_Q-W_P. Sparse E4 (ptool s and brute force: min g over proper sets = 10),
  e = 56 = 3n - 4, degrees 5^8 6^12. No two edge-disjoint Hamilton cycles (exhaustive: 1,658,880 Hamilton
  cycles through vertex 0 enumerated, none with a Hamiltonian complement). Reason: T is balanced and only
  ONE edge leaves T_Q, so every 4-factor F has boundary_F(T) = 2 * (F-edges leaving T_Q) <= 2. Pair exists
  (K_{4,4} inside T). So Lemma 2EC is false and SP is false; rigid cuts are real.
  In a sparse E4 instance, a balanced T with <= 1 edge leaving one color class is exactly a "(5,1) set":
  g(T) = g(V-T) = 10, T_Q holds all 4 units of Q-deficiency and sends 1 edge out, T_P sends 5, P - T holds
  all P-deficiency (proof in SCOUT.md).
- 11:50: L5 census DONE: no pair-free bipartite graph with delta >= 4, Delta <= 6, e = 3n - 5 on <= 17
  vertices (sides 5,5..8,8 and 4,5..8,9; 1,471,650 graphs). Hence (Lemma 1.4/Cor 1.5 in SCOUT.md) a smallest
  E4-type W1b counterexample with a (5,1) set has n >= 36.
- SCOUT.md written (full draft): Lemmas 1.1-1.4, Cor 1.5, census tables, T1 refutation, T2, closure attempt
  (Lemma 2EC' via one-swap Lemma D), exact gap. Corrected one claim of mine (a "flow-rigid" example was
  in fact thin on the Q side).
- Next: computational check of Lemma D's mechanism (greedy one-swap repair on random 4-factors of sparse
  instances) if time allows; then final reply.
- 12:05: witness check. ptool2 mode w prints both Hamilton cycles; verify_sp.py (networkx, own code)
  checks spanning, edges present, edge-disjoint. E4 a=8: 52,295/52,295 verified; q4 a=10: 121,768 HD
  verified + 17 non-HD (matches); E4 a=9 shard 37/100: 319,185/319,185 verified; q4 a=11 shard 5/24:
  233,873 verified + 13 non-HD (matches the census shard summary 233,886 / 233,873). The non-HD graphs
  are certified non-HD by their 2-edge cuts (cuts.c). Added Corollary 1.6 to SCOUT.md.
- Next: PAPER.md with the complete pieces, freeze, final reply.
- 12:20: PAPER.md written (Lemmas 1, 2, 7; Props 3, 5; Cor 6; Examples 4 (R20) and 8 (T1)) and frozen:
  see FROZEN.sha256. SCOUT.md final. Stop condition reached (one closure attempt, stopped at the
  rigid-set classification and the multi-swap potential).
- 12:25: DONE. Final files: SCOUT.md, PAPER.md (frozen 6fad9b43...), LOG.md, tools and data/. No jobs
  running. Nothing written outside wave3/pairs (G110/c1checks/__pycache__ timestamps unchanged, 02:03-02:06).
