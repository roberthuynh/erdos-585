# Referee report on wave4/c1type/PAPER.md (Theorem C: the C1 type at n = 19, 21, 23)

Referee lane, Pass 3 wave 4, October 5, 2026. Status: FINAL.

Paper: `wave4/c1type/PAPER.md`, SHA-256 `df13580087f66a2c216ced5377c743133097f1b1990b13513cf3559b20c5f24d`.
- Start of review (19:06): `shasum -a 256 -c FROZEN.sha256` gives `PAPER.md: OK`.
- End of review: see §6.

Method. Every step of PAPER §1-§5 was re-derived by hand before any code was written (log:
`review/LOG.md`, entry 19:58). The case analysis of Theorem C3 was then re-checked with a SAT model
written for this review (`review/code/c1ref.py`, `run_shape.py`; pysat with CaDiCaL 1.9.5, not the
author's CaDiCaL 1.5.3), without reading the author's `c1_sat.py`. Census records were compared with the
files they cite. The author's code was not run. Nothing was written outside `review/` and this file;
`check.sh` was not run.

## 1. Verdicts

| # | Result | FINAL verdict |
|---|---|---|
| 1 | §1 setting: (F1), (F2), (F3)/(1.2), (K) | ACCEPT |
| 2 | Lemma C1 (a)-(c) (m ≤ 22: F connected, bad-pair shapes, one bad pair) | ACCEPT |
| 3 | Proposition C2 (THEORY Prop 6.6 transferred to Y) | ACCEPT |
| 4 | Lemma C3, the 5 + 5 side facts, Lemma B1 transfer | ACCEPT |
| 5 | Theorem C3, §4.1 (A = K_{4,4} − e; n = 19, 21, 23) | ACCEPT |
| 6 | Theorem C3, §4.2 (n = 21, A and B both 5 + 5) | ACCEPT |
| 7 | Theorem C3, §4.3 (n = 23, A of 5 + 5, B of 6 + 6): Lemma C4, Steps 1-5 | ACCEPT (optional wording F5) |
| 8 | Theorem C | ACCEPT (optional wording F6) |
| 9 | Corollary C (W1b for n ≤ 23, B6 for N ≤ 24) | ACCEPT WITH FIXES (F1, provenance of census F2) |
| 10 | §7 records, §8 status table, §6 remark | ACCEPT WITH FIXES (F1-F4; F7 optional) |

**K_{4,4} − e | 7 + 7 at n = 23 (the flagged shape): settled by proof and computation.** The written
proof (§4.1, n = 23) was re-derived line by line and is correct. Two computer checks, both own code and
both with only facts §4.1 uses ((F2), (D1), no K_{4,4} in X[B + w], (1.2) as lazy cuts that were never
needed), are UNSAT throughout:
- method 1: F[B] runs over all 208 classes of bipartite graphs on 7 + 7 vertices with degrees 4 except
  one vertex of degree 3 per class (nauty genbg 2.9.3; list checked by own code), × deg w ∈ {4, 5}:
  416/416 UNSAT, controls without (★) 416/416 SAT;
- method 2 (no genbg): F[B] free, split on symmetry as the ADDENDUM-B referee did (an E0H edge at y1,
  WLOG to p' or to b1) with lex-leader constraints for the residual group: all four (case, deg w) models
  UNSAT; the hardest one (case y1–b1, deg w = 5) was finished by a further complete split on the
  position of u1 (11/11 UNSAT); controls without (★) SAT.

No mathematical error was found. The fixes are about provenance and status words.

## 2. Hand re-derivation (summary; details in review/LOG.md)

- **§1.** C1P Lemma 4.4 (refereed ACCEPT in `G110/C1-REVIEW.md` and `wave4/c1-fable-ref/REVIEW.md`)
  needs only a sparse C1 instance with D(U) = 1, which X is (PAIRS Lemma 1); bad ports carry deficiency
  ≤ 2 < 7 = D(W), so a good port w exists. D_Y(q) = [q ∈ N(w)] + [q = u1] on Q = U, so at most one
  vertex of Q has D_Y = 2 and D_Y(Z) ≤ |Z| + 1 (F2); D_Y(Q) = D_Y(P) = 1 + deg w. (1.1) is THEORY
  Lemma 1.1, which holds in any bipartite Y with Δ ≤ 6 and a 4-factor. (F3): for 3 ≤ |S'| ≤ 17 and
  S' ⊆ V(X), g(S') = 10 would give a 4-core of at least 18 vertices (PAIRS Prop 5 with |S| ≥ 3, census
  L5), so g ≥ 12; with S' = S + w this is (1.2) for 2 ≤ |S| ≤ 16. (F1): the three deletion arguments
  are right. (K): a disconnected F has a component C with c_F(C) = 0 and 8 ≤ |C| ≤ m − 8, which is bad;
  a cut of at most 2 edges of a 4-regular bipartite graph is balanced; H_m covers m = 18, 20, 22.
- **Lemma C1.** (a): the smallest component has 8 or 10 vertices, K_{4,4} or K_{5,5} minus a perfect
  matching, both Hamilton-decomposable. (b): Σ_T h = 2|T| − D_Y(T) = 2e_H(T) + e_H(∂T) with
  e_H(∂T) ≥ ∂(T) − 2 and g(T) = D_Y(T) + ∂(T) gives g(T) ≤ 2|T| + 2; then e(A) ≥ 4t − 1 > t² for
  t = 2, 3, and (F1) gives K_{4,4} − e for t = 4 and 19-21 edges for t = 5. (c): crossing pairs give
  four disjoint bad sets (m ≥ 32); nested ones give M with 4t − 2 ≤ t², so t ≥ 4 and m ≥ 24.
- **Proposition C2.** Re-derived in Y: c_{F'}(T) = 2; W does not cross T (W ∩ T or W ∪ T would be a
  second bad pair of the connected F'); |M| ≤ m − 16 ≤ 6; F'[M] is an edge or K_{3,3} with
  ∂_{F'}(M) = 6; e_{F'}(W, M) = 2, so all four F'-edges across ∂T end in M; both cases xy ∈ F and
  xy ∉ F contradict the choice of a shortest Z.
- **Lemma C3 and the 5 + 5 side.** The arcs leaving a closed S ⊆ B are e2 and E1H arcs;
  e(S) = 4t + 2r − D − s(S); r ≥ 3, and r ≥ 4 unless S_P = {p'}. F̄ has degree 2 exactly at p1, q1, is
  a union of paths, hence (α) or (β) (genbg agrees: 2 classes of 5 + 5 graphs with 19 edges and degrees
  3-4; 14 for 6 + 6, 208 for 7 + 7).
- **§4.1.** (4.1) and Σ_{y ≠ q1} h(y) ≥ 2 from (F2). Good sets: t = 1, 2 impossible, t ≥ 3 forces
  r ≥ 5, S_Q = B_Q impossible. n = 19: none. n = 21: t = 3 gives S_Q = N(w), X[S + w] = K_{4,5};
  t = 4, 5, 6 give 19, 23, 27 edges. n = 23: every case of the table checked, including r = 6, t = 3
  (X[S + w] has 4 + 6 vertices and ≥ 23 − s ≥ 22 edges). Endgame: R(p') ⊆ R_a, common Q-part
  B_Q − z, all E1H tails at z, k1 = 2 = h(z), d = 6, D_Y(B_P) = 0, z = q' with |R(p')_P| = 4 and
  Z_P = N_F(q') ∩ B_P; each x ∈ Z_P would need its two H-edges at q1 (already two parallel edges).
- **§4.2.** k0 + k1 = 20 − d − e_H(A) − e_H(B) ≥ 10; the covering bound; (3) and (4) including the
  tight-case bookkeeping (disjoint unions, in = 2 at three vertices, parallel edges) and the
  (α)/(β) facts about N_F̄(q1), N_F̄(p1).
- **§4.3.** Lemma C4 in every (t, r) case (t = 3, r = 5 uses K_{4,5} ⊆ X[S + w]; t = 4, 5 use K_{4,4}-free
  bounds 15, 18, 18; t = 5, r = 5 and t = 6 use (1.2)). Step 1; Step 2 (closed sets with s ≤ 3 have
  r = 3 with R_P = {p'} and D = 4, or r = 4 and D = 5; S = R1 ∩ R2 ⊆ {u1}; both overlap cases fail);
  Step 3 (|Y0| ≤ 1 + e_H(A)); Step 4 via (D3); Step 5 (only p1 can have two F̄-neighbors).
- **Theorem C and Corollary C.** As written; the global reading of "smallest" (n minimal over all
  W1b counterexamples, then e) is the one PAIRS Lemma 1, Prop 5 and Corollary C use.

## 3. Computer checks (own code, review/code/)

Model (`c1ref.py`). Side A fixed (K_{4,4} − p1q1 with H[A] = ∅, or (α)/(β) with each of the 22
choices of H[A] ⊆ F̄, |H[A]| ≤ 2: all 44 sides, including the 12 with a pair). Variables: F[B] (or one
fixed genbg class), H[B], E0H, E1H, N(w) ∩ Q, the position of u1. Constraints: F[B] degree 4 (3 at p',
q'); each Q-vertex has H-degree + [q ∈ N(w)] + [q = u1] = 2 (F2); each P-vertex H-degree ≤ 2;
|N(w)| = deg w; (★) via one closed-set certificate per x' ∈ B_P (exact: the certificate can be taken to
be R(x')). B-side facts, exactly those the written proof uses ("lean"): none for n = 19; for n = 21
K_{4,4} − e | 6 + 6, no K_{4,4} in X[B + w] and ≤ 21 edges on every 5 + 5 subset of B (no L5); for
n = 21 5 + 5 | 5 + 5, e_H(B) ≤ 2; for n = 23 (both shapes), no K_{4,4} in X[B + w] and (1.2) for S ⊆ B
with |S_P| ≥ 5 and |S_Q| < |B_Q| (lazy cuts).

| Shape | Method | Result | Controls (no (★)) |
|---|---|---|---|
| n = 19, K_{4,4} − e \| 5 + 5 | F[B] enumerated (2 classes) × deg w 4, 5 | 4/4 UNSAT | 4/4 SAT |
| | F[B] free | 2/2 UNSAT | |
| n = 21, K_{4,4} − e \| 6 + 6 | enumerated (14 classes) | 28/28 UNSAT | 28/28 SAT |
| | free (A-side lex) / free + symmetry split | 2/2, 4/4 UNSAT | 4/4 SAT |
| n = 21, 5 + 5 \| 5 + 5 | enumerated, 44 A sides × 2 × 2 | 176/176 UNSAT; also 176/176 with F2 dropped (qfree) | 176/176 SAT |
| | free | 88/88 UNSAT | |
| n = 23, 5 + 5 \| 6 + 6 | enumerated, 44 A sides × 14 × 2 | 1,232/1,232 UNSAT | 1,232/1,232 SAT |
| n = 23, K_{4,4} − e \| 7 + 7 | method 1: enumerated (208 classes) × 2, A-side lex | **416/416 UNSAT** (1,720 core-s solver time) | 416/416 SAT |
| | method 2: free F[B], symmetry split + lex | **4/4 UNSAT**: y1–p' deg 4, 5 (90 s, 1,106 s); y1–b1 deg 4 (1,350 s); y1–b1 deg 5 by 11/11 u1-position subcases (41-249 s each, 974 s) | 4/4 SAT |

Every UNSAT at n = 23 (416 + 1,232 models of the enumeration, and all 14 method-2 models) came at the
first solve, before any (1.2) cut was added: the computer check of Theorem C3 at n = 23 does not use
(F3), hence not L5 (remark only; the written proof does use (1.2)). (Six sampled K_{4,4} − e | 7 + 7
models, classes 0, 50, 207 × deg w 4, 5, are UNSAT with no fact about B at all, `tnok44.out`; a sample,
not claimed.)

Every SAT control was decoded and re-checked by an independent BFS checker (4-factor, degrees,
c_F(A) = 1) and has a one-crossing cycle. Encoding tests: (i) `enc_test.py`: with the counts relaxed,
160 SAT models with (★) were decoded, none has a one-crossing cycle; (ii) `enc_test2.py`: 3,000 random
configurations built directly (170 without a one-crossing cycle): the (★) model with all main variables
fixed is SAT exactly when BFS finds no one-crossing cycle, 0 disagreements, all five shapes; (iii)
`test_symG.py`: the lex clauses agree with direct evaluation of x ≥_lex τ(x) on 1,500 assignments.
Symmetry arguments: method 1 fixes F[B] to a genbg class representative (every labeled F[B] is mapped to
one by a class-preserving permutation fixing p', q', under which the model is invariant) and adds
lex-leader constraints for the interchangeable vertices A_P − p1 and A_Q − q1 of K_{4,4} − p1q1.
Method 2: by (F2) some y ∈ A_Q − q1 has an E0H edge; WLOG y = y1 (S3), and its B_P-end is p' or, WLOG
(S6 on B_P − p'), b1; within each case the residual group (S2 × S3 × S6 or S5 × S6) is broken by
lex-leader constraints of one global variable order.

The genbg class lists were checked against own code (`fb_cover.py`, networkx VF2 with the two classes
as node colors): the 14 (6 + 6) and 208 (7 + 7) representatives are pairwise non-isomorphic, and every
one of 3,000 and 6,000 labeled F[B] drawn by a random walk of degree-preserving interchanges (Ryser: the
walk connects all matrices with these margins) is isomorphic to a representative (14 and 206 classes
hit).

Own pair test (`aside_pairs.py`, networkx cycle enumeration): of the 44 5 + 5 sides, 12 have a pair and
32 are pair-free, and the rule stated in §7 matches on all 44 (controls: K_{4,4} has a pair, K_{4,4} − e
none), as `check_aside.out` says.

Author's records against §7: `c1_sat_19.out` (UNSAT at every level, controls SAT), `sat21_y.out` (66
UNSAT), `sat21_ctrl.out` (66 SAT), `sat21_proof.out` (88 UNSAT for 5 + 5 | 5 + 5; K_{4,4} − e | 6 + 6
SAT at deg w = 5 in the relaxation, as stated), `sat23_y.out` (64 UNSAT, K_{4,4} − e timeouts),
`sat23_allA.out` (88 UNSAT), `sat23_k44.out`, `sat23_k44p.out` (timeouts), `sat23_k44p_ctrl.out`
(SAT): all as §7 says.

## 4. Census and citation checks

- 5 + 5 census (`wave4/theory/census55_e*.{g6,pairfree}`): 130, 69, 34, 16, 6, 3, 1, 1 graphs and 125,
  62, 24, 8, 0, 0, 0, 0 pair-free for e = 18..25; THEORY REVIEW §1d reproduced this with its own
  generator and two pair testers.
- H18, H20, H22 (SCOUT §2.3): no non-HD graph without a 2-edge cut at a = 9, 10, 11; PAIRS REVIEW §3
  reproduced a ≤ 10 with geng and its own HD tester; a = 11 is one method.
- L5 (SCOUT §2.4): one method, spot-checked by the PAIRS referee at 5 + 5 to 6 + 7; used here only for
  n = 23 through (F3).
- C1P Lemma 4.4: ACCEPT in `G110/C1-REVIEW.md` and in `wave4/c1-fable-ref/REVIEW.md`.
- THEORY Lemma 1.1, Prop 6.6, ADD-B Lemmas B1, B3, (D1)-(D3), Corollary B: ACCEPT in
  `wave4/theory/REVIEW.md` (1a, 1d, 2a, 2b); its fixes P1-P3 concern THEORY §6.2 and §7, which this
  paper does not use.
- Census F2: see fix F1.

## 5. Fixes (exact)

- **F1 (required, provenance; PAPER §8 row "Census F2", the input of Corollary C).** The row says
  "two methods" without naming them, and the only replication on record under the name F2 does not
  decide pairs: STATE.md row F2-rep (`census/CENSUS.md` Job 1, geng_q4/genbg_q4) decides 4-regular
  subgraphs (CENSUS.md line 70: "F2(n): bipartite, δ ≥ 4, Δ ≤ 6, e ≥ 3n − 4 ⇒ 4-regular subgraph").
  The pair census F2 itself is one method (geng -b + pairc, `585-fable/CHECKPOINT-02.md` lines 12-13,
  `CHECKPOINT-05.md` lines 28-33); the PAIRS referee said the same (`wave3/pairs/REVIEW.md` §1, Lemma
  1). A genuine second method exists for what Corollary C needs (no smallest counterexample with
  n ≤ 18): by PAIRS Lemma 1 such an X is a sparse E4 instance with a ≤ 9 or a C1 instance with
  s ≤ 8, δ ≥ 4, and SCOUT §2.1 (genbg + ptool) finds two edge-disjoint Hamilton cycles in every E4
  instance with a ≤ 9 and at every port of every C1 instance with s ≤ 8 (one method at the top sizes).
  Read the row as: "Census F2 (no counterexample with n ≤ 18): two methods for the smallest-
  counterexample classes (F2: geng -b + pairc; SCOUT §2.1: genbg + ptool); not STATE.md F2-rep, which
  decides 4-regular subgraphs". The same unsourced "two methods" sits in ADD-B §6 and THEORY REVIEW
  §2b (outside this paper).
- **F2 (status, §8 row "5 + 5 pair-free census").** "one method (genbg + pairc), re-run in THEORY" →
  "two methods (genbg + pairc; THEORY REVIEW's own generator and pair testers)".
- **F3 (status, §8 rows "THEORY Lemma 1.1 and Proposition 6.6; ADD-B Lemmas B1, B3, (D1)-(D3)" and
  "ADD-B Corollary B").** "unreviewed (frozen ...)" → "refereed ACCEPT (wave4/theory/REVIEW.md 1a, 1d,
  2a, 2b)".
- **F4 (record, §0 "Where to check first" item (4), §7 last bullet, §8 last row).** "the one shape
  without a SAT cross-check" / "This shape rests on the written proof alone" are superseded: this review
  settles K_{4,4} − e | 7 + 7 at n = 23 by computation as well (§3).
- **F5 (optional wording, §4.3 Step 2).** "an E1H arc with tail in S would have head β(y1) = β(y2)" →
  "an E1H arc with tail in S would have head β(y1) and head β(y2), which differ".
- **F6 (optional wording, §0 Theorem C and §1 first sentence).** Say "a smallest W1b counterexample
  (n minimal among all counterexamples, then e minimal), and it is of C1 type": PAIRS Lemma 1 and
  Prop 5 need minimality over all counterexamples, not only over C1-type ones.
- **F7 (optional wording, §6 first sentence).** "Lemma C1 fails as stated" for n ≥ 25 → "the proof of
  Lemma C1 does not extend": what §6 lists are steps that break, not counterexamples to the lemma.

## 6. Compute, reproduction, end of review

Compute: about 2.3 core-hours in all, of which about 2.0 for K_{4,4} − e | 7 + 7 at n = 23 (method 1:
1,720 core-s of solver time; method 2: about 5,200 core-s, including a redundant unsplit run of the last
case stopped at 28 minutes once the u1 split had finished). Within the 4 core-hours allowed for that case.

Reproduction (`review/code/`, Python `~/.cache/erdos585/venv/bin/python`): `fb{5,6,7}.g6` from
`genbg -q -d3:3 -D4:4 b b (4b-1):(4b-1)`; `run_shape.py <shape> enum|free [nostar] [qfree]
[levels=...] [degw=...]` with shapes n19k44, n21k44, n21_55, n23_55, n23k44 (method 1:
`run_shape.py n23k44 enum levels=k44w,r12,symA workers=6`; method 2: `run_k44free.sh`, then
`run_k44free_split.sh y1b1 5`); `enc_test.py`, `enc_test2.py`, `test_symG.py`, `fb_cover.py`,
`aside_pairs.py`, `tnok44.py`. Outputs are the `.out` files beside them. Method 1 ran before the symG
code was added to `c1ref.py`; the symA constraints are the same now (only the names of the
auxiliary lex variables changed).

End of review: `shasum -a 256 -c FROZEN.sha256` gives `PAPER.md: OK` (see LOG.md, final entry). PAPER.md
was not edited.
