# Referee report on wave3/pairs/PAPER.md

Referee lane, Pass 3 wave 3, October 5, 2026. Status: FINAL.

Paper: `reports/585-next/wave3/pairs/PAPER.md`, SHA-256
`6fad9b431ca5e4afa6abfa01a38073b636c5ebfae72d3f200acd34beb1483ae0`.
- Start of review: hash matches `FROZEN.sha256`.
- End of review: hash recomputed, still matches. The paper was not edited.

Method. Every lemma was re-derived by hand before I opened the author's code. Every computed claim was
then re-checked with code I wrote for this review (`review/code/`), validated on known graphs, and only
after that compared with the author's tools (`ptool.c`, `mpair.c`, `cuts.c`, `pairc`, the Python
checkers). Log: `review/LOG.md`. No git, no `check.sh`, no Lean, nothing written outside `review/` and
this file (one stray scratch file in `/tmp` was deleted at once, see the log).

## Overall verdict

**ACCEPT WITH FIXES.** No result of the paper is wrong in its main claim, and every lemma it uses later
holds. Three statements need repairs, one of them substantive for the tooling:

1. **Proposition 5 is false as stated for |S| = 2** (an edge has g = 10 and an empty 4-core). Requiring
   |S| ≥ 3 repairs it, and Corollary 6 (n ≥ 36) survives unchanged.
2. **`mpair.c` has a labeling bug**: it never sets `path1[0]`, so its answer is right only when the first
   mark is vertex 0. On the T1 list the final count (6) happens to survive; I re-decided all 76,975 lines
   with my own tester and got the same six. On the T2 list (SCOUT.md §3.2, not in PAPER) every line has
   first mark v ≠ 0, and the reported details are wrong: **82 "exactly two pairings" cases are all false;
   the true number is 6**, the X of the six T1 counterexamples, which the author's data marks as
   realizing all three. T2's headline (≥ 2 pairings always) survives my rerun.
3. Two small wording gaps: the "t ≥ 5" step after Example 4 skips t = 1, and Lemma 7's (b) is vacuous when
   T is itself a (5,1) set, which the §0 summary should say.

| Item | Verdict | One line |
|---|---|---|
| Lemma 1 (smallest W1b counterexample is sparse E4 or C1, δ ≥ 4) | ACCEPT | re-derived |
| Lemma 2 (sparse E4 has a 4-factor) | ACCEPT | re-derived from C1-PAPER Lemma 1.4 (reviewed) |
| Proposition 3 (thin balanced sets are exactly (5,1) sets; ∂_F(T) ≤ 2) | ACCEPT | re-derived |
| Example 4 (R20) | ACCEPT WITH FIX F2 | all claims re-verified by own code; minimality remark misses t = 1 |
| Census L5 | ACCEPT (one-method census, spot-checked) | own generator + own decider agree at 5+5, 5+6, 6+6, 6+7 |
| Proposition 5 | ACCEPT WITH FIX F1 | false for \|S\| = 2; true for \|S\| ≥ 3 |
| Corollary 6 (n ≥ 36) | ACCEPT (given L5) | needs F1's \|T\| ≥ 3, which δ ≥ 4 supplies |
| Lemma 7 and Remark | ACCEPT, wording fix F3 | re-derived; 1,176 random cut tests, 0 failures |
| Example 8 (T1 false at m = 11) | ACCEPT WITH FIX F4 | six certificates re-verified; "exactly 6" reproduced by own rerun; mpair bug |
| H22 (SCOUT §2.3, cited in PAPER §7) | ACCEPT as a one-method census at n = 22, two methods for n ≤ 20 | geng + own HD tester reproduce every count and verdict for n ≤ 20 |
| T2 (SCOUT §3.2, not in PAPER) | ACCEPT WITH FIX F5 | "≥ 2 pairings" holds on all 66,992 X; "82 exactly 2" is false, it is 6 |
| E4 spanning-pair census (Example 4 remark, SCOUT §2.1) | not re-run beyond a ≤ 7 | own generator / geng + own decider agree at a = 6, 7 |

## 1. Lemmas, re-derived by hand

**Setting and (1).** Identity 1.1 (g(S) = 2D^S(S_Q) + 6(|S_P| − |S_Q|), from D^S(S_Q) = 6|S_Q| − e(S)) and
Identity 1.3 re-derived. For an instance g(V) = 8; E4 gives D(P) = D(Q) = 4, C1 gives 1 and 7. (1): the
F-degree sums over T_P and T_Q are 4|T_P| = e_F(T_P, T_Q) + e_F(T_P, Q − T) and the same for T_Q, so
balance gives e_F(T_P, Q − T) = e_F(T_Q, P − T). Correct. C1-PAPER §1 is reviewed (G110/C1-REVIEW.md:
Identities 1.1, 1.3 and Lemmas 1.4, 1.5 ACCEPT), so the paper's "(reviewed)" is accurate.

**Lemma 1: ACCEPT.** Edge deletion keeps every hypothesis while e > 3n − 4, so e = 3n − 4. A set S with
2 ≤ |S| ≤ n − 1 and g(S) ≤ 8 has e(S) ≥ 3|S| − 4, and X[S] is bipartite, Δ ≤ 6, pair-free, on fewer
vertices: a smaller counterexample. g is even, so g(S) ≥ 10. g(V) = 8 = 2d + 6j gives (j, d) = (0, 4) or
(1, 1) (j ≥ 2 gives ≥ 12); this holds for every bipartition, so the class is well defined even before one
notes that X is connected. δ ≥ 4: g(V − v) = 2 + 2 deg v ≥ 10, valid since n ≥ 3 (n = 2 would need 2
edges). The F2 remark (n ≥ 19) matches STATE.md row F2 (pairs, bipartite, n ≤ 18; one program). Rows
F2-19 to F2-21 there decide 4-regular subgraphs, not pairs, so n ≥ 19 is the right bound to cite.

**Lemma 2: ACCEPT.** The flow criterion and slack formula re-derived (cut of the b-matching network:
4|P − A| + 4|C| + e(A, Q − C) ≥ 4|P|; e(A, Q − C) = 6k − D_A + ε). D_A ≤ 4 forces k = 1, ε ≤ 1,
D_A ≥ 3 + ε. Piece Y[A ∪ C]: smaller class C, in-piece deficiency D_C + e(C, P − A) = ε ≤ 1. Piece
Y[(P − A) ∪ (Q − C)]: smaller class P − A, deficiency (4 − D_A) + e(P − A, C) ≤ (1 − ε) + ε = 1. Both
have g ≤ 8, both are nonempty and complementary, so one with ≥ 2 vertices is a proper violator; both
singletons means a = 1. Correct.

**Proposition 3: ACCEPT.** g(T) = 2D^T(T_Q) = 2(D(T_Q) + ∂_Q(T)) ≥ 10 with D(T_Q) ≤ 4 gives ∂_Q(T) ≥ 1,
equality only with D(T_Q) = 4. Then D(Q − T) = 0, V − T is balanced with 2 ≤ |V − T| ≤ n − 2, and the two
expressions for g(V − T) give ∂_P(T) ≥ 5 and g(V − T) = 2(D(P − T) + 1) ≤ 10, so all six equalities
follow (D(T_P) = D(P) − D(P − T) = 0 directly). Conversely the listed equalities give
g(T) = 2(4 + ∂_Q(T)) = 10, so ∂_Q(T) = 1: "thin balanced sets are exactly the (5,1) sets" is right.
The 4-factor statement follows from (1), and two edge-disjoint Hamilton cycles cross every nontrivial cut
at least 4 times. Correct.

**Proposition 5: ACCEPT WITH FIX F1.** The step "if K = ∅ then X[S] is 3-degenerate and
e(S) ≤ 3|S| − 6" needs |S| ≥ 3 (a 3-degenerate graph on m vertices has at most 0 + 1 + 2 + 3(m − 3) = 3m − 6
edges only for m ≥ 3; for m = 2 the bound is 1 = 3m − 5). Counterexample to the statement as written:
any edge S = {u, v} of X has 2 ≤ |S| ≤ n − 1, g(S) = 12 − 2 = 10, and its 4-core is empty. For |S| ≥ 3
the proof is correct: peeling a vertex of degree ≤ 3 never lowers e − 3|·|, so e(K) ≥ 3|K| − 5 when
K ≠ ∅; K is an induced proper subgraph with δ ≥ 4, hence |K| ≥ 8 ≥ 2, and sparsity gives e(K) ≤ 3|K| − 5.

**Corollary 6: ACCEPT (given L5).** Both sides of a (5,1) set have g = 10 (Proposition 3). They have
at least 4 vertices: a balanced side with t = 1 would be an edge pq whose Q-vertex (for T) or P-vertex (for
V − T) carries all 4 units of deficiency, so has degree 2, against δ(X) ≥ 4 (Lemma 1). So the repaired
Proposition 5 applies to both, the two 4-cores are disjoint, and n ≥ 18 + 18 = 36.

**Lemma 7: ACCEPT, wording fix F3.** Re-derived line by line.
- D: arcs P → Q along F, Q → P along H; a directed cycle alternates and has length ≥ 4 (F ∩ H = ∅), so
  F Δ E(Z) is again a 4-factor.
- (a) Z avoids the arcs of e1 and e2, so F' keeps e2 and gains the H-edge q → p of Z:
  e_{F'}(T_Q, P − T) ≥ 2 and ∂_{F'}(T) ≥ 4 by (1). Correct.
- (b) A path p ⇝ q in D⁻ plus the arc q → p (still in D⁻, it is an H-arc) would be a cycle as in (a), so
  q ∉ X. X is out-closed, so the only F-edges leaving X_P are the e_i counted by ε, and every H-edge at
  X_Q stays in X: e_F(X) = 4|X_P| − ε, e_H(X) = 2|X_Q| − D(X_Q), hence g(X) = 2j + 2ε + 2D(X_Q).
  Identity 1.1 with D^X(X_P) = D(X_P) + ε + e_H(X_P, Q − X) gives the second identity. p ≠ p1 (p ∉ T),
  so at most one F-arc at p (to q1, when p = p') is missing: |X| ≥ 4, q ∉ X, so g(X) ≥ 10. With
  e_H(X_P, Q − X) ≥ 1 (the edge qp) the elimination gives 3D(X_Q) ≥ 11 − 2ε + D(X_P) ≥ 7, so D(X_Q) ≥ 3;
  for ε = 0, D(X_Q) = 4, D(X_P) ≤ 1, and 1 ≤ j ≤ (3 − D(X_P))/2 gives j = 1. Correct.
- Remark: for ε = 0, D(X_P) = 0: g(X) = 10, ∂_P(X) = ε + (4 − 0 − 2) = 2, D^X(X_Q) = 8 so ∂_Q(X) = 4,
  and every 4-factor has e(X_Q, P − X) − e(X_P, Q − X) = 4j = 4, forcing all four Q-side edges in and
  both P-side edges out. Correct.
- Gap in the summary, not in the proof: (b) is vacuous when no H-edge joins T_Q to P − T. Since F uses
  exactly one edge of ∂_Q(T), that happens iff ∂_Q(T) = 1, which by Proposition 3 means T is a (5,1) set.
  The §0 row "One-swap repair ..., or deficiency concentration" omits this third case (where T itself
  holds all 4 units of Q-deficiency). See F3.

Empirical check (own code, `review/code/lemma7_test.py`): own flow 4-factor, random alternating swaps,
every 2-edge cut of every sampled 4-factor tested from both sides, every H-edge q → p classified.
R20: 60 cuts (30 thin, i.e. the (5,1) side, where (b) is vacuous), 120 H-edges, all in (b), every
identity and inequality holds. 35 random sparse two-block E4 instances on 20 vertices (own generator,
sparsity by own brute force over 2^20 sets): 510 cuts, 1,056 H-edges, all in (a), every swap gives a
4-factor with cut ≥ 4. No failure. The ε = 0 branch was not reached by these samples; it is pure algebra
and checked by hand above.

## 2. Example 4 (R20): ACCEPT WITH FIX F2

Own checks (`review/code/r20_check.py`, `r20_brute.c`):
- `data/rigid20.g6` is label-identical to the graph described in the text; bipartite with P = 0..9;
  n = 20, e = 56 = 3n − 4, degrees 5^8 6^12, D(P) = D(Q) = 4.
- T: ∂_Q(T) = 1, ∂_P(T) = 5, D(T_Q) = 4, D(T_P) = 0, D(P − T) = 4, D(Q − T) = 0, g(T) = g(V − T) = 10.
- Sparse: brute force over all 2^20 subsets, min g over 2 ≤ |S| ≤ 19 is 10, attained by 58 sets
  (the 56 edges, T and V − T).
- Every 4-factor has a cut of ≤ 2 edges, checked without using Proposition 3: all 155,520 4-factors
  enumerated; 14,400 are disconnected (120 × 120, one 4-factor of each K_{5,5}), and each of the other
  141,120 has a pair of edges whose removal disconnects it. So R20 has no two edge-disjoint Hamilton cycles.
- The pair (two 8-cycles on {0, 1, 2, 3, 10, 11, 12, 13}) checked edge by edge.
- By hand: every Hamilton cycle of R20 crosses the cut exactly twice (four crossings would need two T-paths
  with ≥ 3 endpoints in T_P, which unbalances T), so there are 5 · (4! 4!)² = 1,658,880 of them, the
  count `ptool h` reports.

**F2.** The closing remark "6t − 5 = e(T) ≤ t², so t ≥ 5" also allows t = 1 ((t − 1)(t − 5) ≥ 0). The
conclusion stands because t = 1 needs a vertex of degree 2 and a sparse instance has δ ≥ 4.

## 3. Census L5 and the other censuses

**L5: ACCEPT** as a one-method census (genbg + `pairc f`), with an independent spot check at the
smallest orders. My generator (`review/code/genbip.c`: rows as a non-increasing multiset, canonical form
= minimum over all column permutations of the sorted rows; validated on 2- and 3-regular counts and by
networkx isomorphism tests) and my pair tester (`review/code/rpair.c`: every cycle once, grouped by vertex
set; validated against networkx on 407 graphs) give, for δ ≥ 4, Δ ≤ 6, e = 3n − 5:
4+5: 0, 5+5: 1, 5+6: 2, 6+6: 13, 6+7: 29 graphs, all with a pair. The counts equal the paper's. 7+7 was
not finished (my canonical form is too slow at 5,040 permutations). The class list is complete
(g = 10 forces class difference ≤ 1 under every bipartition, which also covers disconnected graphs), and
the sum 1,471,650 is right. The 8+8 and 8+9 runs: all 12 shard summaries present, 1,237,978 graphs,
0 pair-free (plumbing only; not re-run).

**H22: ACCEPT** as stated, two methods for n ≤ 20, one method at n = 22. geng (a different generation
algorithm from genbg) gives 14, 129, 1,980, 62,611 connected bipartite quartic graphs on 14, 16, 18, 20
vertices; converting to genbg's color-preserving count (a graph without a color-swapping automorphism
counts twice) gives 16, 193, 3,528, 121,785, exactly the paper's numbers (and my generator gives 4 and 16
at a = 6, 7). My HD tester (`review/code/hd.c`, validated on K_{4,4}, K_5, the octahedron, L(K_{3,3}),
and L(Petersen), which is 4-edge-connected and not HD by Kotzig's theorem) finds 1, 2, 15 non-HD graphs at
n = 16, 18, 20 (color-preserving 1, 2, 17 = the paper's), each with a 2-edge cut, and every other graph
HD. At n = 22: the 24 shard summaries add to 5,582,592 graphs, 5,582,356 HD, and the 236 non-HD graphs
(equal to `data/q4bip_a11_nonhd.g6`) are non-HD with a 2-edge cut by my tester. The n = 22 generation
and HD verdicts were not re-run (geng at n = 22 is about 7 CPU-hours). `ptool.c`'s search was read and
looks right.

**E4 spanning pairs (Example 4's "≤ 18 vertices" remark): not re-run beyond a = 7.** My generator gives 10
E4 instances at a = 6 and geng gives 153 unlabeled (267 color-preserving) at a = 7, both equal to the
paper's; all have two edge-disjoint Hamilton cycles by my tester `review/code/sp.c`. The a = 9 run: 100 of
100 shard summaries, 31,662,400 graphs, all with a spanning pair (plumbing only).

## 4. Example 8 (T1) and the `mpair.c` bug

**Certificates: confirmed.** For each of the six lines of `data/t1_none.txt` (own `rpair.c`, mode t,
and `t1_build_x.py`): Y has 11 vertices, 30 = 3·11 − 3 edges, Δ = 6; ab and cd are disjoint edges;
Z = Y − ab − cd is pair-free; Y has pairs but none with ab and cd on different cycles; X = Z + v (12
vertices, 32 edges, Δ = 6) has pairs through v for exactly the two other pairings and no pair avoiding
v. The six are pairwise non-isomorphic (as Y, as marked Y and as Z); each Z has 4-core K_2 ∨ C_5. The
statement of W1-MINIMAL.md §4a is false at m = 11, and the gap in its proof is the one PAPER §6 names
(`FIXED-MATCHING.json` records it on the octahedron).

**The bug.** In `mpair.c`, `compat()` starts the first cycle with `ham1(eb, (1u << ea) | (1u << eb), 2)`,
and `ham1` writes `path1[depth - 1]`, so `path1[0]` is never written and stays 0 (static). When the cycle
closes, the residual graph for C2 is built from `path1[0..ssize-1]`, so it deletes the edges
(0, b) and (last, 0) instead of (a, b) and (last, a). The answer is right only when a = 0; otherwise C2 may
reuse an edge of C1 (false COMPAT) or lose a legitimate edge at vertex 0 (false NONE).
- Demonstration (`review/code/mpair_bugtest_in.txt`): for every one of the six T1 graphs, writing the
  marks as "b a c d", or relabelling v ↦ v + 3 mod 11, makes the frozen `mpair` answer COMPAT. My
  tester answers "no compatible pair" for all 18 lines.
- Fix: one line, `path1[0] = ea;` before the `ham1` call (`review/code/mpair_fixed.c`, diff = that line).
  The fixed binary answers NONE on all 18 lines.
- `verify_t1.py` only re-checked the six NONE answers, so it could not see false COMPATs.

**Effect on T1: none on the final numbers.** 25,206 of the 76,975 lines in `data/t1_Y.txt` have a ≠ 0.
I re-decided every line with `rpair` (16 shards, all exit 0): exactly six have no compatible pair, the
same six; Z is pair-free on every line; by order m = 7..11 there are 5, 50, 608, 6,848, 69,464 lines.
I also checked the Z universe independently through 10 vertices: geng (all graphs, Δ ≤ 6, e = 3n − 5,
no minimum-degree bound) plus `rpair` gives 1, 4, 41, 457 pair-free graphs on 7..10 vertices, the
paper's numbers. At 11 vertices geng -d3 -D6 11 28:28 (400 shards, all exit 0) plus `rpair` gives
5,122, the paper's number; the bound δ ≥ 3 is justified by W1 at n = 10 (Δ ≤ 6, e = 26..28: 87,157
graphs, none pair-free, same run). So the T1 universe (and the T2 universe up to 12 vertices) is
confirmed by a second generation route, and with my rerun T1's "exactly 6, all at m = 11" now has two
independent methods.

**F4** below repairs the method description.

## 5. T2 (SCOUT.md §3.2, not in PAPER): ACCEPT WITH FIX F5

Every T2 line has first mark v (the new vertex, ≥ 7), so every T2 verdict came through the bug. I
re-decided all 66,992 X of `data/t2_X.txt` with `rpair` mode r (one cycle enumeration per X, all three
pairings at v, plus a search for a pair avoiding v): **every X realizes ≥ 2 pairings** (so T2 survives on
this list), no pair avoids v, and **exactly 6 X realize exactly 2**, all on 12 vertices: they are the
X = Z + v of the six T1 counterexamples, missing the pairing {ab | cd}. Every X on ≤ 11 vertices
realizes all three. The author's data say otherwise in 88 places:
- all 82 lines of `data/t2_none.txt` are realized: `review/code/t2_witness.py` (networkx cycles, own
  matching) prints an explicit pair for each, re-verified edge by edge (`t2_witness.out`): 82 false NONE;
- on the six T1-derived X, `data/t2_res.txt` marks all three pairings COMPAT: 6 false COMPAT.
The author's own T1 and T2 outputs contradict each other on these six graphs.

## 6. Fixes (exact)

- **F1 (Proposition 5, required).** Replace "2 ≤ |S| ≤ n − 1" by "3 ≤ |S| ≤ n − 1" in Proposition 5 and
  write in the proof "if K = ∅ then X[S] is 3-degenerate and, as |S| ≥ 3, e(S) ≤ 3|S| − 6". In the §0
  row "Prop 5, Cor 6", read "every set with at least 3 vertices and g = 10". Add to Corollary 6's proof:
  "Both sides have ≥ 4 vertices: a side with one vertex per class would contain a vertex of degree 2
  (D(T_Q) = 4 or D(P − T) = 4 on one vertex), against δ ≥ 4 (Lemma 1)." Same fix in SCOUT.md Lemma 1.4.
- **F2 (Example 4 closing remark, wording).** Replace "so t ≥ 5" by "so t = 1 or t ≥ 5; t = 1 would give a
  vertex of degree 2, impossible since a sparse instance has δ ≥ 4 (g(V − v) = 2 + 2 deg v ≥ 10); the same
  holds for V − T".
- **F3 (Lemma 7 summary, wording).** In §0, Lemma 7 row, and after Lemma 7 add: "(b) is vacuous when no
  H-edge joins T_Q to P − T, that is when ∂_Q(T) = 1, which by Proposition 3 means T is a (5,1) set (then
  T itself holds all 4 units). So a 2-edge cut of a 4-factor is a (5,1) set, or one swap repairs it, or
  an out-closed X holds ≥ 3 units of Q-deficiency."
- **F4 (Example 8 method, required for the record).** Replace the "Checks:" sentence by: "Checks: `mpair.c`
  as frozen has a labeling bug (`path1[0]` is never set, so the residual graph uses vertex 0 in place of
  the mark a) and is reliable only for lines with a = 0, which includes the six NONE lines; the referee
  re-decided all 76,975 lines with an independent tester and found the same six. `verify_t1.py`
  re-checked the six NONE answers." Fix `mpair.c` with `path1[0] = ea;` before the `ham1` call.
- **F5 (SCOUT.md §0 row T2, §3.2, LOG.md; data).** Replace "exactly 2 in 82 (4 on 11 vertices, 78 on 12)"
  by "exactly 2 in 6, all on 12 vertices: the X of the six T1 counterexamples; every X on ≤ 11 vertices
  realizes all three". Regenerate `data/t2_res.txt` and `data/t2_none.txt` with the fixed `mpair` (88
  wrong lines now).
- **F6 (optional).** PAPER §7 and SCOUT should say which census results now have a second method from
  this review: H22 for n ≤ 20, L5 at 5+5 to 6+7, E4 spanning pairs at a ≤ 7, the T1 list in full and the
  Z universe through 10 vertices.

## 7. Comparison with the author's checks

My verdicts were fixed before reading the author's code. Afterwards:
- `ptool.c` sparsity test: the fast path (λ ≤ 8 with the minimal minimizer proper iff a proper violator
  exists through the edge) is correct, and minimal violators contain an edge (|S| = 2 has g ≥ 10, larger
  ones have internal δ ≥ 4). Agrees with my brute force on R20. Its spanning-pair search starts at depth 1
  (no `path1[0]` problem) and agrees with my testers wherever I ran both.
- `brute_sparse.py` (Gray code) is correct. `pairc` (585-fable tools) starts at depth 1 and has no
  `path1[0]` problem; its L5 answers agree with mine at the small orders.
- `mpair.c`: wrong when the first mark is not vertex 0 (§4). The author's T1 count survives; the T2
  details do not.
- Census plumbing: every sharded run (q4a11 24/24, e4a9 100/100, l5s8 12/12) has a summary for every
  shard, and the summaries add to the stated totals. The totals themselves were not regenerated at the
  largest orders.

## 8. What was not checked, and what is left

- Not re-run: H22 at n = 22, L5 at 7+7 and above, E4 spanning pairs at a = 8, 9, the C1 port census.
  These stay one-method results, with plumbing checked.
- Done after the PARTIAL save: Z census at 11 vertices, 5,122 = the paper (§4).
- Not done (optional): full T1/T2 reruns with `mpair_fixed` as a third method.

## 9. Reproduction

All code and outputs are in `review/code/`. Main entry points: `r20_check.py` and `r20_brute.c` (R20),
`rpair.c` and `validate_rpair.py` (pair tester), `genbip.c` (bipartite generator), `hd.c` (HD tester),
`sp.c` (two edge-disjoint Hamilton cycles), `run_q4_20.sh`, `run_t1census.sh`, `run_t2census.sh`,
`run_zcheck.sh`, `run_z11.sh`, `lemma7_test.py`, `t2_witness.py`, `mpair_fixed.c`. Compile with
`/usr/bin/clang -O2 -o <name> <name>.c`; Python is `~/.cache/erdos585/venv/bin/python`.
