# Referee report on wave4/theory: PAPER.md and ADDENDUM-B.md

Referee lane, Pass 3 wave 4, October 5, 2026. Status: FINAL.

Papers (neither was edited):
- `PAPER.md`, SHA-256 `521a1139...24b7`: matches `FROZEN.sha256` at the start and at the end of the review.
- `ADDENDUM-B.md`, SHA-256 `555b8ef3...b496`: matches `FROZEN-B.sha256` at the start and at the end.

Method. Every proof was re-derived by hand before any code was written (log: `review/LOG.md`). Every
computational claim was then re-checked with code written for this review (`review/code/`), validated
on known cases, and compared with the author's records only afterwards. The author's `tools.py`,
`check_lp.py`, `classify.c`, `check_identities.py`, `lemmaB_sat.py` and `pairc` were not run; graph6 was
passed through files only. Nothing was written outside `review/` and this file; `check.sh` was not run.
Compute used: about one core-hour.

## Verdicts

| # | Result | FINAL verdict |
|---|---|---|
| 1a | Thm 2.1 (LP duality), Cor 2.2 (rigidity criterion), with Lemma 1.1 | **ACCEPT** |
| 1b | Lemma 3.1 (sets with s ≤ 1 in a sparse E4 instance) | **ACCEPT** |
| 1c | Prop 4.1, Thm 5.1 (no rigid set below 36 vertices) | **ACCEPT** (given PAIRS Prop 5 with \|S\| ≥ 3 and census L5) |
| 1d | Lemma 6.1, Prop 6.6 (n ≤ 22: connected, one bad pair, one-crossing repair) | **ACCEPT** (given L5 and the 5 + 5 census, which this review reproduced) |
| 1e | §7 C1 ports, results table, Appendix A | **ACCEPT WITH FIXES** (P1-P3 below; wording and one stale count, no mathematical error) |
| 2a | Theorem B (one-crossing cycle exists, all shapes) | **ACCEPT** |
| 2b | Corollary B (no smallest E4-type W1b counterexample with n ≤ 22) | **ACCEPT** (given F2, L5, the 5 + 5 census and H22; H22 is still one method at n = 22) |

No numbered result is wrong. Every step of the chain behind Corollary B (Lemma 6.1, Proposition 6.6,
Theorem B, the "every 4-factor is connected" paragraph of §6.2a) was re-derived line by line, and the
case analysis of Theorem B was re-checked with an independent SAT model.

## Fixes (exact)

- **P1 (PAPER §7, Corollary 7.2, first sentence; wording).** As written, "T ⊆ V(Y) balanced with
  ∂_Q(T) ≤ 1" includes T = ∅ and T = V(Y), for which the conclusion u1 ∈ T fails (and Lemma 7.1(iii),
  used in the proof, needs T nonempty and proper). Read: "If T ⊆ V(Y) is balanced with
  2 ≤ |T| ≤ |V(Y)| − 2 and ∂_Q(T) ≤ 1, ...".
- **P2 (PAPER §7, Lemma 7.3, last sentence, and the §0 row "Lemma 7.3"; wording).** "So for n = 19 no
  edge of Y is excluded" holds at a good port: the step from "no forced set with ∂_P ≥ 1" to "no edge
  lies in no 4-factor" is Corollary 2.2(i), which needs a 4-factor of Y. At a bad port every edge lies
  in no 4-factor. Read: "So for n = 19, at every good port y, every edge of Y lies in some 4-factor."
- **P3 (PAPER §6.2, "Evidence" paragraph; stale numbers).** The rigid-lane totals for rounds 1-2 are
  now 1,187,258 sparse instances and 1,162,097 without a rigid set (RIGID.md: 1,062,855 + 69,324 +
  55,079 and 1,042,361 + 69,082 + 50,654). The paper quotes 1,187,256 and 1,162,095, the counts before
  the summarize fix recorded in `wave4/rigid/LOG.md` (two sparse instances without a rigid set had been
  filed as skipped). Conclusions unchanged; 975,700 good ports and "within 10 swaps" match RIGID.md.
- **P4 (optional, PAPER §1).** "A sparse instance has δ ≥ 4 (PAPER Lemma 1)": PAIRS Lemma 1 is stated
  for smallest counterexamples. The step used, g(V − v) = 2 + 2 deg v ≥ 10, holds in every sparse
  instance with n ≥ 3; cite that step.
- **P5 (optional, PAPER App. A, PAPER §0 row Lemma 6.1, ADDENDUM-B §6 row "5 + 5 pair-free census").**
  The 5 + 5 census now has a second method (this review, below); L5 and H22 at n = 22 are unchanged
  (one method).

## 1. PAPER.md

### 1a. Lemma 1.1, Theorem 2.1, Corollary 2.2: ACCEPT

By hand. (1.1) from the degree sums over S_Q and S_P with e(S) = 3|S| − g(S)/2; (1.2) from
e(S) + e(V − S) = e − ∂(S). Lemma 1.1: subtracting the F-degree sums gives
4|S_P| − 4|S_Q| = e_F(S_P, Q − S) − e_F(S_Q, P − S), so s(S) = e_F(S_P, Q − S) + e_H(S_Q, P − S), the
out-degree of S in D(F); the last form is (1.1). Theorem 2.1: the primal (bipartite incidence matrix
plus identity) is totally unimodular, so is its transpose; the dual polyhedron is not pointed (the
lineality space y = t on P, −t on Q), but every nonempty face of a TU system with integral right-hand
side contains an integral point, so an integral dual optimum exists. The level rewrite uses |P| = |Q|
for Σ_P π − Σ_Q π = Σ_t (|S_t ∩ P| − |S_t ∩ Q|), and the edge terms are as stated (for pq ∈ E0 with
π(p) ≤ π(q) the term is 1 plus the number of levels with q ∈ S_t ∌ p). Corollary 2.2: (i) from E0 = {e}
and Φ = 0; (ii) both directions as written, including "a set repeated at two levels counts twice";
E1(T) = E0(V − T) and c_F(V − T) = c_F(T) by PAPER (1).

Own code (`code/rigidcheck.c`, all 4-factors by backtracking, all 2^n sets):
- Lemma 1.1: out-degree of S in D(F) equals s(S) for every S, six sampled 4-factors per graph: 0 failures.
- Corollary 2.2(i): Ex equals the union of E(S_P, Q − S) over forced S: 0 failures.
- Corollary 2.2(ii): brute-force rigidity (max over all 4-factors of |F ∩ E0(T)| ≤ 1) against
  "(A) or (B)" with all sets S of slack 1, for E0(T) and for E1(T), and rigid(T) = rigid(V − T), on about
  10.9 million balanced T: 0 mismatches. Graphs: 300 random a + a graphs (a = 4 to 7, degrees 4 to 6),
  42 two-block graphs with a 4-factor (`gen_inst.py`), 240 two-block graphs with compensating edges
  (`gen_inst2.py`, n = 16, 18), the 10 + 267 sparse E4 instances at a = 6, 7, the first 150 at a = 8,
  and R20. 408 rigid sets occur (17 certified only by (B)); in R20 exactly T and V − T are rigid.
- Theorem 2.1: 1,440 tests on n ≤ 10 (random E0 and E0(T)): the brute-force maximum equals the minimum of
  Φ over π ∈ {0..2}^V or {0..3}^V every time; weak duality and "level form = direct dual objective" held
  for every π evaluated.
Record check: `check_lp_1{1..4}.out` give 4 × 77,208 = 308,832 = 24 × (C(16,8) − 2) sets and
6 + 6 + 4 + 4 = 20 rigid, as App. A says.

### 1b. Lemma 3.1: ACCEPT

By hand: all seven rows re-derived from s = g/2 − j − D(S_Q), ∂_P = s + D(S_Q) − 2j − D(S_P) ≥ 0,
g ≥ 10 and D(S_Q) ≤ 4, with the converse (each row has s = g/2 − j − d_Q). The complement remarks (F1
with |V − S| ≥ 2 has d_P = 0, ∂_P = 2, g(V − S) = 10; a U0 set is a (5,1) set, and a balanced S with
|S| ≤ n − 1 automatically has |S| ≤ n − 2) also hold.

Own code (`code/lowslack.c`, Gray code over all subsets, own bipartition and own sparsity test) on all
52,557 instances of `wave3/pairs/data/e4_a{6,7,8}_sparse.g6` and on R20: every instance is a sparse E4
instance; every S with 2 ≤ |S| ≤ n − 1 and s ≤ 1 matches a row (0 unmatched); (1.1) and the last form of
Lemma 1.1 hold for every S; the complement remarks hold. With P = genbg's first class: F1 38,802,
F2 8,732, U2 132,624, U3 60,140, U4 60,140, U0 = U1 = 0, exactly App. A. (The swapped orientation gives
the same totals; complementation maps U3 sets to U4 sets of the swapped orientation, which explains
U3 = U4.) R20: one U0 set per orientation.

### 1c. Proposition 4.1 and Theorem 5.1: ACCEPT

Re-derived. Trivial sets: s(∅) = s(V) = 0, s({q}) = deg q − 4, s({p}) = 4, s(V − p) = deg p − 4,
s(V − q) = 4, and ∂_P vanishes on {q}, V − p, ∅, V, so the sets used have 2 ≤ |S| ≤ n − 2. Case 1: a
forced set with ∂_P > 0 is F1 (F2 has ∂_P = 0), both sides odd with at least 2 vertices, so at least 3.
Case 2: U0 = (5,1) set (PAIRS Prop 3), sides at least 4 (a balanced 2-set side would need a vertex of
degree 2). Case 3: (A) would make T thin, hence U0; so (B) with S of type U1-U4, ∂_P(S) ≤ 3 (U3 is
impossible since E0(T) ≠ ∅), the same for E1(T) via V − T, so ∂(T) ≤ 6 and g(T) = g(V − T) = 10 by (1.2);
|T| = 2 forces two degree-4 ends and c_F(T) = 3 for every F. Theorem 5.1 then needs PAIRS Prop 5 with the
referee's |S| ≥ 3 (both sides have at least 3 vertices) and L5; the last sentence follows from Cases 1
and 2, which do not use rigidity. The "n < 2(m + 1)" remark is right.

### 1d. Lemma 6.1 and Proposition 6.6: ACCEPT

Lemma 6.1(a), re-derived: Σ_T h = 2|T| − D(T) = 2e_H(T) + e_H(∂T) and e_H(∂T) = ∂(T) − ∂_F(T) with
∂(T) = g(T) − D(T) give g(T) ≤ 2|T| + 2 on both sides; |A| = 2 needs g ≤ 6; g(A) = 10 with |A| ≥ 3 needs
|A| ≥ 18; so |A| ∈ {6, 8, 10}; e(A) ≥ 11 > 9 kills 6; 8 gives K_{4,4} − e; 10 gives 19 ≤ e(A) and the
census caps it at 21. (b): crossing bad sets give four bad corners (submodularity, posimodularity, all
cuts even and at least 2 in a connected F, every cut of at most 2 edges balanced), so n ≥ 32; nested
pairs give M with 2|M| − 2 ≤ e_F(M) ≤ (|M|/2)², so |M| ≥ 8 and n ≥ 24; a disconnected F has exactly two
components and any other bad set splits a component into two bad sets of at least 8 vertices.

Proposition 6.6, re-derived line by line, including the disconnected-F' branch (crossing W and T give a
bad set strictly inside a component; in the nested branch ∂_{F'}(W) = 0 already contradicts
∂_{F'}(M) = 6). The arithmetic is right: |M| ≤ 22 − 16 = 6; t = 1 or t = 3 with ∂_{F'}(M) = 6;
e_{F'}(W, M) = 1 + ∂_{F'}(W)/2 ≤ 2, so all four F'-edges across ∂T (e1, e2, a, b) end in M; x and y are
the right ends in both cases R = T and R = V − T; xy ∈ F' since F'[M] is complete bipartite; the two
subcases (xy ∈ F gives σ = (x → y), xy ∉ F puts the arc y → x on Z at y) are both contradictions.
The §6.2a paragraph: the two Hamilton cycles of K_{5,5} minus {p_i q_i} were checked edge by edge, and
a disconnected 4-factor on at most 22 vertices has a component on 8 or 10 vertices, so c_F(T) = 1.
Identity 6.2, Theorem 6.3 (conditional), Remark 6.4 and the K_{4,4} − e partial proof of Lemma B were
re-derived and are correct.

Own 5 + 5 census (`code/bipcensus.c`: every labeled subgraph of K_{5,5} with 18 to 25 edges, two
independent pair testers, canonical form validated against OEIS A002724: 36 classes for 3 × 3, 317 for
4 × 4): classes for e = 18, ..., 25 are 130, 69, 34, 16, 6, 3, 1, 1, pair-free 125, 62, 24, 8, 0, 0, 0, 0;
the two testers agree on all 726,206 labeled graphs. This is exactly `census55.out`, so "no pair-free
5 + 5 graph with at least 22 edges" now has two methods.

Own identity tests (`code/identities_own.py`, networkx flow 4-factor and random alternating-cycle
walks): Identity 6.2 in 19,924 tests (in the last batch of 6,116, 4,022 had runs and 1,349 a nonzero
change), the H-balance of Remark 6.4, s = out-degree, (1.1) and (1.2) in 28,000 tests each, and
"reversing a directed cycle gives a 4-factor" after every step: 0 failures (a = 7 and a = 8 samples, R20).

### 1e. §7, results table, Appendix A: ACCEPT WITH FIXES (P1-P5)

§7 re-derived: Lemma 7.1 (i) D_Y(Q) = D_Y(P) = 1 + deg y, g(V(Y)) = 2d; (iii) from g_X(S + y) ≥ 10 and
D_Y(q) = [q ∈ N(y)] + [q = u1]. Corollary 7.2 (with P1): u1 ∈ T, equality in (iii), and for n ≤ 21 the
complement {p, q} has ∂_Q(T) = deg p − [pq ∈ E] ≥ 3 (p and y lie in the same class, so deg_Y p = deg_X p).
Lemma 7.3, all four cases (u1 ∈ S with j = 1; u1 ∉ S; u1 ∈ S with j = 2, including g(R) = 2d + 2j −
2D(S_P) ≤ 16 and r = 0 or r ≥ 4; j ≥ 3) are correct. The citation of C1-PAPER Lemma 4.4 (bad ports carry
total deficiency at most 2 when D_U = 1; D(W) = 7) is accurate, so good ports exist. §8: a forced
one-passage cut is an F1 set, which needs n ≥ 36; (HD-OP) for n ≤ 22 follows from H22.
Own test (`code/c1ports_own.py`): Lemma 7.1 (i), (iii) and s = g/2 − j − D(S_Q) on every nonempty proper
S at every port of the C1 census instances (s = 5: 1 instance, 6 ports; s = 6: 8, 42; s = 7: 12 sampled,
59 ports; 1.1 million sets): 0 failures. Thin and forced-excluding sets do not occur at these sizes, so
Corollary 7.2 and Lemma 7.3 are checked by hand only.

Results table: every row matches the body, apart from the P2 wording. Appendix A records: `check_lp`
(above), `classify` counts (reproduced), `check_identities_s3.out` (the counts are assertion passes, so
0 failures), `census55.out` (reproduced), the exp7-exp12 logs (115 sparse necklaces; 362 runs; exp9 135
instances, 1,000 shortest-cycle tests, 13 of 3,996 random-cycle repairs with a new bad set; exp11 204
instances, 1,727 tests; exp12 199 instances, 1,388 atoms; all violation files empty), B6 at N = 20
(121,790 = 121,785 connected + 4 + 1 disconnected 4-regular complements; `timing.out` shows 0 pair-free).
FLAW.md F1 re-checked with own code (`code/flaw_own.py`): n = 40, e = 116, Δ = 6, D(P) = D(Q) = 4, sparse
(own max-closure flows over every edge uv and excluded vertex w: minimum g over proper sets is 10), F a
4-factor, T balanced with c_F(T) = 1 and an atom; Z_random (length 6) and Z_shortest (length 4) are
directed cycles of D⁻ through an E0 H-arc; Z_random repairs T and creates two new bad pairs whose sides
{0..4, 20..24} and V − U_new are disjoint from T; Z_shortest creates none. As the paper says.

## 2. ADDENDUM-B.md

### 2a. Theorem B: ACCEPT

Re-derived by hand, every step:
- §1 setting (n ∈ {20, 22}; T = A without loss; exactly e1 and e2 cross; Lemma B1 in both directions).
- (D1): F[A] = X[A] = K_{4,4} − p1q1. (D2): F̄ has 6 edges, is a union of paths (only p1, q1 have degree
  2), and is (α) or (β) up to names; H[A] ⊆ F̄. (D3) rescue path.
- Lemma B2: types F1/U0/U1 (g = 10: |S| ≥ 18 or an edge with ∂_Q ≥ 3), F2/U3/U4 (t ≥ 4, so 4 + 6 with
  e ≥ 23), U2 (t ≥ 5, so 5 + 6 with e = 27); both graphs contain K_{4,4} by the deletion argument
  (own census agrees: 4 + 6 with 23, 24 edges and 5 + 6 with 27 to 30 edges, 2 and 11 classes, all contain
  K_{4,4}); in(S) = g/2 + j − D(S_P) is s with P and Q exchanged, so (ii) follows.
- Lemma B3 and its mirror: the arcs leaving R are e2 and E1H arcs, e(R) = 4t + 2r − D(R_Q) − s(R),
  (t − 2)(r − 4) ≥ 8 − D(R_Q) − s(R), big or tiny.
- §4.1 (Σ_{y ≠ q1} out(y) ≥ 2; closed R with s(R) ≤ 1 contradicts B2, or |B| = 14 and E1H = ∅ against
  |E1H| = 8 − D(A_P) ≥ 4). §4.2 (∂(A) = 18 − e_H(A) − e_H(B) ≥ 14, |E0H|, |E1H| ≥ 2, both branches; the
  argument uses only "blocked implies an F̄ edge", so a 4-cycle exists, as remarked). §4.3 Steps 1-5 and
  the mirrors, including the tiny case (two E1H edges from distinct vertices into β(y), so one vertex of
  degree 4), the three overlap counts of Step 2, Y0 counting, Step 4 via (D3), and the three branches of
  Step 5. No gap found.

Own SAT model (`code/lemmaB_own.py`, pysat with CaDiCaL, written without reading `lemmaB_sat.py`). A
side fixed (K_{4,4} − p1q1, or (α)/(β) with each of the 22 choices of H[A] ⊆ F̄ with at most 2 edges);
F[B], H[B], E0H, E1H free; F-degrees 4 (3 at p', q' in B); H-degree at most 2 everywhere; exactly
n − 4 H-edges; e_H(B) ≤ 2 for a 5 + 5 side B; for 6 + 6 and 7 + 7 sides, no K_{4,4} in X[B] and
e(S) ≤ 3|S| − 6 for S ⊆ B, |S| ≥ 3, added as lazy cuts. (★) is encoded with a certificate set per
y' ∈ B_Q closed under in-arcs (mode coreach) and, separately, per x' ∈ B_P closed under out-arcs (mode
reach). Results:
- all 90 configurations UNSAT in both encodings, and also without the B-side constraints (confirming the
  addendum's remark that those 46 configurations need no fact about B beyond the degree counts);
- the configuration K_{4,4} − e with B = 7 + 7 did not finish unsplit within about 3 minutes (CaDiCaL,
  Glucose); it was closed by a symmetry split (the model is invariant under permuting y1, y2, y3 and
  B_P − {p'}, and the count forces an E0H edge at some y ≠ q1, so WLOG at y1 with x' ∈ {p', u1}): both
  cases UNSAT in all three modes;
- controls: without (★) all 90 are SAT, each decoded model re-checked by BFS (4-factor, H-degrees, n − 4
  H-edges, and it has a one-crossing cycle); with the count relaxed to "at least k E0H and k E1H edges",
  k = 1, 3, 5 give 90, 63, 3 SAT models, each re-checked by BFS: no one-crossing cycle, so the (★)
  clauses mean what they should. At k = 5 exactly the two n = 20 shapes are UNSAT, matching §5;
- the stronger statement of §4.2 (every pair blocked by an F̄ or F̄_B edge) is UNSAT in all 44 n = 20
  configurations with |A| = 10.

### 2b. Corollary B: ACCEPT

The proof is complete given its inputs: a 4-factor exists (PAIRS Lemma 2); with no bad set it is
connected and 2-cut-free; otherwise it is connected with c_F(T) = 1 (§6.2a), Theorem B gives a
one-crossing cycle, Proposition 6.6 gives a 2-cut-free 4-factor, and H22 gives two edge-disjoint
Hamilton cycles, a pair. With F2, a smallest counterexample on at most 22 vertices is of C1 type with
n ∈ {19, 21}. The inputs and their status: PAIRS Lemmas 1, 2, Example 4 and Prop 5 (with |S| ≥ 3) as
refereed in `wave3/pairs/REVIEW.md`; census F2 (two methods); L5 (one method, referee spot check); the
5 + 5 census (now two methods); H22 (two methods for n ≤ 20, one method at n = 22). The §6 table of the
addendum states these correctly, except that the 5 + 5 census now has a second method (P5).

## 3. Not checked, limits

- L5 above 6 + 7, H22 at n = 22 and F2 were not re-run; they remain the cited records.
- Corollary 7.2's last sentence and Lemma 7.3 have no test instances at small n (they need n near 21);
  they are checked by hand only.
- Theorem 2.1's minimum was searched over a bounded range of π (sufficient here, since equality with the
  brute-force maximum was reached every time, and weak duality holds for every π).
- The SAT check is a second method for Theorem B's case analysis, not a proof certificate; the written
  proof was verified independently by hand.

## 4. Reproduction

`review/code/`: compile C with `/usr/bin/clang -O2 -o <name> <name>.c`; Python is
`~/.cache/erdos585/venv/bin/python`.
- `bipcensus 5 5 18 25`, `bipcensus 4 6 22 24`, `bipcensus 5 6 26 30` (outputs `census*_own.out`).
- `lowslack <file.g6>` (outputs `a8parts/*.out`; a6, a7, R20 in the log).
- `gen_inst.py`, `gen_inst2.py`, `rigidcheck <file.g6> -1 <seed>` (outputs `rc_out/`).
- `identities_own.py`, `c1ports_own.py`, `flaw_own.py` (outputs `ident_*.out`, `c1_s*.out`,
  `flaw_own.out`).
- `lemmaB_own.py {full,full_reach,nobside,nostar,starprime,relax1,relax3,relax5}` and
  `lemmaB_own.py single <mode> <idx> cd15 [y1,pp|y1,u1]` (outputs `lemmaB_own_*.out`, `sat22_*.out`,
  `sat45_split*.out`).
