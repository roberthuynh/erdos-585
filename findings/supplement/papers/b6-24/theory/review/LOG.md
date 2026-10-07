# Referee log, wave4 theory (PAPER.md + ADDENDUM-B.md)

- start: FROZEN.sha256 OK (PAPER.md), FROZEN-B.sha256 OK (ADDENDUM-B.md).
- created review/ and review/code/. Next: read both papers and the wave3 pairs inputs.
- 17:35 read PAPER.md, ADDENDUM-B.md, wave3 PAPER.md, REVIEW.md, SCOUT.md (sec 2.3 H22, 2.4 L5).
- Hand pass 1 (by hand, before any code): Lemma 1.1, (1.1), (1.2), Thm 2.1 (TU + level rewrite), Cor 2.2,
  Lemma 3.1 (all seven rows re-derived), Prop 4.1 (3 cases), Thm 5.1, Lemma 6.1(a)(b), Identity 6.2,
  Thm 6.3, Remark 6.4, Prop 6.6, the "every F connected" paragraph (both K55-PM Hamilton cycles checked
  edge by edge), Lemma 7.1, Cor 7.2, Lemma 7.3 (all four cases), Lemma B1, (D1)-(D3), B2, B3, Thm B
  4.1, 4.2, 4.3 Steps 1-5 and mirrors, Cor B. No error found yet. Minor wording: Cor 7.2 needs T
  nonempty and proper (T = empty set has dQ = 0). Checked: 308,832 = 24 x (C(16,8) - 2).
- Next: own code in review/code/: (1) LP/rigidity brute force, (2) low-slack classifier in C,
  (3) 5+5 pair census in C, (4) B2 side census, (5) own SAT model of (star) for Thm B.
- 17:50 records read: check_lp_*.out (4 seeds x 6 instances x 12,868 balanced T = 308,832; rigid 6+6+4+4 = 20),
  census55.out, census_side.out match the numbers quoted in App. A and Addendum section 5.
- own code/bipcensus.c (all labeled subgraphs of K_{np,nq} by missing-edge subsets, two pair testers:
  DFS cycles grouped by vertex set, and minimal pair masks of K_{np,nq}; canonical form = min over
  column perms of sorted rows). Validated: totals 36 (3x3) and 317 (4x4) = OEIS A002724; K44 has
  204 cycles and 1 minimal pair mask; 4+4 only K44 has a pair; 3+5 all pair-free.
- own side census: 4+6 e=23,24: 1+1 classes, all with K44 and a pair; 5+6 e=27..30: 6+3+1+1 = 11
  classes, all with K44 and a pair. Matches census_side.out and Lemma B2's K44 argument.
- 5+5 census e=18..25 running (census55_own.out).
- 18:05 own 5+5 census (bipcensus 5 5 18 25): iso classes e=18..25: 130,69,34,16,6,3,1,1; pair-free
  125,62,24,8,0,0,0,0. Equal to census55.out and PAPER App. A. Methods A and B agree on all 726,206
  labeled graphs. Lemma 6.1(a)'s census input confirmed by a second method.
- own code/lowslack.c on all 52,557 sparse E4 instances (a=6,7,8) + R20: all sparse by brute force,
  every S with s <= 1 matches a row of Lemma 3.1 (0 unmatched), identities (1.1)/Lemma 1.1 last form hold
  for every S, complement remarks hold. Orientation P = genbg first class: F1 38,802; F2 8,732;
  U2 132,624; U3 60,140; U4 60,140; U0 = U1 = 0. Equal to App. A. (Swapped orientation: same totals;
  U3 <-> U4 by complement.) R20: one U0 set per orientation, 4 U2.
- own code/rigidcheck.c written (4-factor enumeration, Lemma 1.1 out-degree, Cor 2.2 (i)/(ii) for E0 and
  E1, Thm 2.1 min over pi in {0..R}^V); running on own random/two-block instances, a6, a7, a8 head, R20.
- next: own SAT model of (star) for Theorem B (pysat; co-reach closure per y', lazy sparsity cuts).
- 18:20 rigidcheck results (own code): 0 failures of Lemma 1.1 (out-degree = s on every S for 6 sampled
  4-factors per graph), Cor 2.2(i), Cor 2.2(ii) for E0 and for E1, rigid(T) = rigid(V-T), PAPER (1).
  Graphs: 180 random a+a (a = 4..7), 180 two-block (gen_inst.py; 138 without a 4-factor, skipped),
  240 two-block with compensating edges (gen_inst2.py), 10 + 267 + first 150 of the a = 8 census, R20.
  About 9.7M balanced T; 408 rigid (17 only via (B)); R20: T and V - T rigid. Thm 2.1: 1,440 tests
  (n <= 10, random E0 and E0(T)): brute-force max = min of Phi over pi in {0..2 or 3}^V every time;
  weak duality and the level-form = direct dual objective identity held for every pi tried.
- own SAT model code/lemmaB_own.py (co-reach certificates per y'; also per-x' reach mode): controls
  without (star) SAT in all 90 configurations (each decoded model BFS-verified: 4-factor, h <= 2,
  n - 4 H-edges, and it has a one-crossing cycle). Relaxed count tests (k E0H and k E1H edges instead
  of the count): k=1: 90 SAT, k=3: 63 SAT, k=5: 3 SAT; every decoded SAT model re-checked by BFS:
  no one-crossing cycle, so the (star) clauses really forbid one-crossing cycles.
  Full model: n = 20 part (45 configs) UNSAT in coreach, reach and no-B-side modes; n = 22 running.
  (star') of 4.2 (pairs blocked by Fbar edges only, n = 20, 44 configs): UNSAT in all 44.
- 18:40 (resumed after a network interruption; state re-read from this log.) Interim REVIEW.md
  (PARTIAL) saved.
- record check of the repair experiments (exp7-12 logs): exp7 79 + 36 = 115 sparse necklaces; exp8
  116 + 118 + 128 = 362 dyn_good; exp9 inst 135, M_tests 1,000, rand 3,996, rand_newbad 13; exp11 inst
  204, tests 1,727; exp12 inst 199, atoms 1,388; all viol files empty. All equal to PAPER 6.2 / App. A.
- own identities_own.py (networkx flow 4-factor, random alternating-cycle walk): Identity 6.2 6,116
  + 5,337 + 2,000 tests (4,022 of the first batch with runs, 1,349 with nonzero change), H-balance of
  Remark 6.4, s = out-degree, (1.1), (1.2) 26,000 tests each, flip gives a 4-factor: 0 failures
  (a = 8 sample, a = 7 sample, R20).
- SAT n = 22, |A| = 10 (idx 46-89), full mode: 35 of 44 UNSAT so far (about 10 s each). idx 45 (K44,
  B = 7 + 7) is hard for CaDiCaL (> 80 s); running glucose/maple/lingeling and a WLOG case split.
- 18:55 SAT n = 22: all 44 configs with |A| = 10 UNSAT in full mode and in no-B-side mode; reach mode
  running. idx 45 (K44, B = 7 + 7): unsplit runs did not finish in 80-180 s (CaDiCaL, Glucose; stopped).
  WLOG split (model symmetric in y1..y3 and in B_P - p'; the count forces an E0H edge at some y != q1):
  e0(y1, p') UNSAT, e0(y1, u1) UNSAT (CaDiCaL). Split runs in nobside and reach modes queued.
- own c1ports_own.py: Lemma 7.1 (i), (iii) and the identity s = g/2 - j - D(S_Q) on every nonempty
  proper S at every port: C1(5) 1 inst / 6 ports, C1(6) 8 / 42, C1(7) 12 sampled / 59; 0 failures
  (thin and forced-excluding sets do not occur at these sizes, so Cor 7.2 / Lemma 7.3 untested there).
- C1-PAPER Lemma 4.4 read: bad ports carry total deficiency <= 2 when D_U = 1; D(W) = 7, so good ports
  exist. PAPER 7 cites it correctly. check_identities.py counts are assertion passes (record = 0 failures).
- FLAW F1 (randfail.txt): own flaw_own.py running (instance numbers, sparsity by max-closure flows over
  every edge uv and excluded vertex w, F, T, both cycles, bad sets before/after by 2-edge removal).
- 19:10 SAT complete. n = 22 |A| = 10 (44 configs): UNSAT in coreach (full), reach (full_reach) and
  no-B-side modes. idx 45 (K44, B 7+7): both WLOG split cases UNSAT in full, full_reach and nobside.
  With n = 20 (45 configs, all three modes): all 90 configurations UNSAT; controls SAT; relaxed tests
  consistent with the author's shape-level description (k = 5 UNSAT exactly for the two n = 20 shapes).
- FLAW F1 own check (flaw_own.py): n = 40, e = 116 = 3n - 4, Delta 6, D(P) = D(Q) = 4, sparse (min g
  over proper sets with an edge = 10 by max-closure flows over all edges uv and excluded w), F a
  4-factor, T balanced with c_F(T) = 1 (an atom; F has 2 bad pairs), Z_random (length 6) and
  Z_shortest (length 4) are directed cycles of D^- through an E0 H-arc; Z_random repairs T and creates
  2 new bad pairs (sides {0-4, 20-24} and V - U_new, both disjoint from T); Z_shortest creates none.
- RIGID.md record: PAPER 6.2 quotes 1,187,256 / 1,162,095 (rounds 1-2); RIGID.md now gives
  1,187,258 / 1,162,097 after the summarize fix logged in rigid/LOG.md (two sparse no-rigid instances
  had been filed as skipped). Stale numbers, conclusion unchanged: wording fix. 975,700 good ports and
  "within 10 swaps" match.
- Next: final hash check, write FINAL REVIEW.md.
- 19:25 FINAL REVIEW.md written. Count corrections against the earlier log lines: rigidcheck used 300
  random a + a graphs (180 with a = 4, 5 and 120 with a = 6, 7), not 180; balanced T total 10,850,962;
  Identity 6.2 tests 19,924 in all, other identities 28,000 each. Verdicts: 1a-1d ACCEPT, 1e ACCEPT WITH
  FIXES (P1 Cor 7.2 range of T, P2 Lemma 7.3 good port, P3 stale rigid-lane counts, P4/P5 optional),
  2a ACCEPT, 2b ACCEPT. End hashes: PAPER.md OK, ADDENDUM-B.md OK.
