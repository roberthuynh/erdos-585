# Referee report on G110/PAPER.md (lane M1-R)

Referee: lane M1-R, October 5, 2026. Independent of the author lane M1. Every step was re-derived by
hand before any code was run; all code is my own (`review/`, no imports from `checks/`).
M1-LOG.md and `checks/` were read only after every verdict below was formed.

Paper SHA-256 at start: `cfce4fcc7d40732c2f2a6c23b9d5fe50823c37f9d37f940b7857d8eda52ab0c9`
(matches FROZEN.sha256). At end: see the last section.

## Summary

No mathematical error found. Every lemma, proposition and theorem in §0.1-§3 is correct as stated,
with the proofs given. The remarks in §4 are correct, including the paper's own correction of the
C1 sub-case count (3n − 2 − ε, false as briefed when ε = 1). One required fix concerns the census
provenance text in §3 and §5, which is out of date; it does not change any statement.

| Section | Verdict |
|---|---|
| §0.1 setting and tools (identities, Lemmas 0.1-0.5, Cor. 0.6) | ACCEPT |
| §1 G-1 (Lemma 1.1, Cor. 1.2, wording note) | ACCEPT |
| §2.1 Lemma 2.1, Props. 2.2, 2.3 | ACCEPT |
| §2.2 Prop. 2.4 | ACCEPT |
| §2.3 Lemma 2.5, Prop. 2.6 | ACCEPT |
| §2.4 Prop. 2.7 | ACCEPT |
| §2.5 Lemma 2.8, Thm. 2.9, Cors. 2.10, 2.11, Prop. 2.12 | ACCEPT |
| §3 size bounds (Thms. 3.1-3.3, Lemma 3.4, Thm. 3.5) | ACCEPT WITH FIXES (fix F1, provenance only) |
| §4 residual and remarks | ACCEPT |
| §5 what is not proved | ACCEPT WITH FIXES (fix F1, same sentence) |
| Appendix A, B | ACCEPT (hashes and cited lines verified) |

## Required fixes

**F1 (census provenance; PAPER.md lines 448-460 and 599-600).** The paper says F1 and F2 "rest on one
program each" (line 448) and that Theorems 3.1-3.3 are "conditional on F1(14) and F2(18), which rest on
one program each and were not re-run here" (lines 599-600). That is stale: `census/CENSUS.md` (Jobs 1-2)
and `STATE.md` rows F2-rep and F1-rep record replications that existed before the freeze. Replace with:

- F2(n) for every n ≤ 18: two methods with different generators and different deciders: plain geng
  2.9.3 + pairc (Fable W1; all graphs for n ≤ 12, bipartite for n = 13..18), and the q4core decider
  (geng_q4 for n ≤ 17; genbg_q4 `-u -d4:4 -D6:6 9 9 50:54` for n = 18). A third run at n = 18
  (`geng_q4 -b -d4 -D6 18 50:54`, 40/40 shards) finished at 00:31:58 with 0 graphs
  (`census/logs/driver_f2_n18.log`); it shares the q4core decider with genbg_q4.
- F2(19): two completed runs, both with the q4core decider: genbg_q4 `-u -d4:4 -D6:6 10 9 53:54`
  (0 graphs) and `geng_q4 -b -d4 -D6 19 53:57 r/400` (400/400 shards, 0 graphs, finished 00:56:04,
  `census/logs/driver_f2_n19.log`). Two generators, one decider; no second decider at n = 19.
- F2(20): not established (`run_f2_n20.sh` started 00:56:07, projected about an hour).
- F1(n) for n ≤ 14: two methods (geng_q4; plain geng 2.9.3 + pysat SAT, 1,798 graphs at n = 14, all
  with a 4-regular subgraph).

No other fix is required. Editorial suggestions are at the end.

## Section reviews

### §0.1 Setting, notation, tools (lines 46-157): ACCEPT

- (0.1), (0.2) (lines 77-85): re-derived from the two degree sums. Correct.
- Lemma 0.1 (lines 87-102): the s-t cut with source side {s} ∪ A ∪ C has capacity
  4|P − A| + e(A, Q − C) + 4|C| = 4s + slack; every finite cut has this form; the Δ ≤ 6 rewriting
  e(A, Q − C) = 6k − D_A + D_C + e(P − A, C) is right. The "Use for a C0 instance" paragraph is right:
  D_C(H_y) = e(y, C) because I-vertices have Γ-degree 6, so ε = ε(S), and Φ(S) does not depend on y.
- Lemma 0.2 (lines 104-122): K is free of rank n − 1 on b_v = e_v − e_{v0}; F2[(Z/4)^r] ≅
  F2[t_1..t_r]/(t_i^4) with t_v = X^{b_v} + 1 (char 2, so t_v^4 = X^{4b_v} + 1 = 0); every factor
  1 + X^g lies in the augmentation ideal, whose (3r + 1)-th power is 0; the X^0 coefficient counts
  zero-sum sublists mod 2 and the empty list contributes 1. The argument uses a list, so repeats
  (parallel edges) are fine. Loopless is needed and assumed. Correct.
- Lemmas 0.3, 0.4 (lines 124-139): degeneracy order, at most 9 edges on the first six vertices, then at
  most 3 per vertex. Correct.
- Lemma 0.5, Cor. 0.6 (lines 141-157): k = 1, ε = 0, D_A = D_P = 3 forced; D_{P−A} = 0 and
  e(P − A, C) = 0 make both pieces C0 instances or single vertices; sizes |C| and s − 1 − |C| sum to
  s − 1 ≥ 5, both below s. The empty-smaller-side case (C = ∅ or P − A = ∅) is exactly the single-vertex
  piece, and both cannot be trivial. Well founded. Correct.

### §1 G-1 (lines 159-216): ACCEPT

- Item 1: p ≤ 5 since y ∉ A; p ≥ 2k + 1 + ε gives k ≤ 2 and the seven types. Correct.
- Item 2: boundary = ε (C to O − A) + (6k − p + ε) (A to I − C, by (0.1)) + p (A to o) = 6k + 2ε.
  Correct.
- Item 3: c = 0 impossible (|A| = k < p); e(A, C) = 6c − ε ≤ (c + k)c; for k = 1, c² − 5c ∈
  {−4, −6, −6, −4} on c = 1..4, so c ≥ 5; for (2,5,0), c ≥ 4. Correct.
- Item 4: Q's O − A side has deficiency 6 − p + ε; k = 1: balanced, t ≥ 1 (y ∈ O − A), Q-degrees
  ≤ t, so t ≤ 5 forces deficiency ≥ t(6 − t) ≥ 5 > 3; k = 2: O − A = {y} would need t ≥ 5 but t = 2,
  otherwise a non-port with 6 neighbors in I − C gives t ≥ 6. |Y| = 2t + 1 or 2t. Correct.
- Cor. 1.2 and the wording note (lines 204-216): the contrapositive is right; the two-K5,5 graph is
  simple bipartite 6-regular with a 10-edge cut of sides 10 and 10 (verified by my code), so the literal
  "side ≤ 9" hypothesis can fail at 20 vertices while the conclusion still holds via |X| + |Y| ≥ 22.
  The note is accurate. At 22 vertices only (2,5,0) with c = 4, t = 6 survives. Correct.

### §2.1 (lines 218-281): ACCEPT

- (M) (line 223): from minimality of m and Cor. 0.6, E3(s) holds for 1 ≤ s ≤ m (C0 below s ≤ m).
  Correct; this is what makes the d0 ≤ 3 case (E3 at size m itself) legitimate.
- Lemma 2.1 (lines 230-250): (1) e(Q_S) = 6t − 4k − Φ ≥ 6t − 4k + 1 against
  Σ_{O−S} deg ≤ 6(t + 1 − k) − (6 − d0) gives 2k ≤ d0 − 1; (2) c = 0 gives λ = Σ deg ≥ 4k; (3) k = 1
  gives E3(t); (4) k = 2 forces d0 = 5 and the chain 6t − 7 ≤ e(Q_S) ≤ 6t − 7, hence Φ = −1, λ = 7,
  ε = 0, D(S_O) = 5, Q_S a C1 instance of size t − 1 ≥ 1. Correct. This holds for every C0 instance,
  not only minimal ones; my exhaustive check confirms it on all C0(m), m ≤ 8.
- Prop. 2.2 (lines 252-264): d0 ≤ 5 by averaging; d0 ≤ 3 gives E3(m); d0 = 4 gives k = 1, c ≥ 1 and an
  E3 piece of size m − c ≤ m − 1. Correct.
- Prop. 2.3 (lines 266-277): k = 1 excluded through an E3(t) piece with t ≤ m − 1 (c ≥ 1 by 2.1(2));
  k = 2 data from 2.1(4); D(S_O) = 5 puts all of P − y in A; c ≥ 4 because a C-vertex has 6 neighbors in
  A. The induction is well founded (attack item 2): E3(t) is handled by C0 at sizes below t via
  Lemma 0.5, whose trivial pieces are single vertices and never both trivial. Correct.

### §2.2 Prop. 2.4 (lines 283-296): ACCEPT

Removing a port y' from S_O changes (k, p, ε) by (−1, −1, +e(S_I, y')), so Φ changes by
−1 + e(S_I, y'). For X_y, S' = X_y − y' is a k = 1 cut of H_{y'}, not negative by Prop. 2.3, so
e(C_y, y') ≥ 2. Correct.

### §2.3 Lemma 2.5, Prop. 2.6 (lines 298-337): ACCEPT

- Lemma 2.5: the three edge blocks partition E(Γ) because ε = 0; the edge-end counts at A and at C
  (all C-neighbors in A) give x = 4(|V(H) ∩ A| − |V(H) ∩ C|), so x ∈ {0, 4}; the gluing equivalence is
  right in both directions (x = 0 splits H; x = 4 gives τ ∈ R_X ∩ R_Q).
- Prop. 2.6(1): X + β has |A| + |C| + 1 = 2c + 3 vertices, 6c + 7 = 3(2c + 3) − 2 edges, β of degree 7,
  A-vertices keep their Γ-degree ≤ 6, loopless, bipartite. Lemma 0.2 applies at exactly 3n − 2 with
  Δ = 7. F must use β (Γ[X] quartic-free), deg_F(β) = 4, and F minus its β-edges realizes the four
  labels. Correct (attack item 5).
- Prop. 2.6(2): Q + α has 2t vertices and 6t edges; deleting any two α-edges leaves 3n − 2 edges and
  Δ ≤ 7, so R_Q meets every 5-subset. Correct.

### §2.4 Prop. 2.7 (lines 339-361): ACCEPT

(1) Q − i is balanced of size t − 1 ≥ 1 with deficiency 7 − r(i) on both sides (y's unit plus the
6 − r(i) Q-neighbors of i; the I side keeps 7 − r(i)). (2) Q + a: deficiency 7 − s(a) on both sides
(a's deficiency is 6 − s(a) whatever its Γ-degree). (3) Q + α_τ is simple (distinct endpoints), balanced
of size t, Δ ≤ 6 (each endpoint had Q-degree ≤ 5), deficiencies 1 + 2 = 3 and 7 − 4 = 3, so E3(t) with
t < m; a quartic F must use α with degree 4, and F minus the α-edges realizes τ. (4) follows. Correct
(attack item 5).

### §2.5 (lines 363-439): ACCEPT

- Lemma 2.8: ∂_B(U) = ε + (6k − p + ε) + p = 6k + 2ε for every U ⊆ V(Γ) (gadget, so D(U_O) = p_U);
  ε = (∂_B − 6k)/2 is submodular, k and p modular, Φ submodular. Correct.
- Theorem 2.9 (attack item 1), step by step:
  1. ε_U + ε_W ≤ 0 with ε ≥ 0; k_U + k_W = 4; X_y ∩ P = P − y gives p_U = 4 (so U ≠ ∅) and p_W = 6.
  2. U ⊆ V(Γ) − y and Φ(U) = 2k_U − 4; the minimum slack of H_y is −1 (Prop. 2.3), so k_U ≥ 2. The
     parenthetical (p_U = 4 ≠ 5, so Φ(U) ≥ 0) is also right.
  3. All six ports are in W and o ∉ W, so 6k_W = ∂_B(W) ≥ 6.
  4. k_W = 1: ε_W = 0 makes Γ[W] a C0 instance of size |W_I| ≥ |C_y| ≥ 4, quartic-free, so
     |W_I| ≥ m by (M); then W_I = I, |W_O| = m + 1 and W = V(Γ).
  5. k_W = 2: ∂_B(Z) = ∂_B(W ∪ {o}) = 12 + 6 − 12 = 6, k_Z = −1, ε_Z = 6; Z has no port, so
     e(Z_O, I − Z) = 0; if Z_O ≠ ∅, Γ[Z] is C0 of size ≤ m − 5 (contradiction); else |Z_I| = 1.
  Degenerate cases: U = ∅ is impossible (p_U = 4); Z = ∅ is impossible when k_W = 2 (k_Z = −1); C0
  instances of size 1 to 4 do not exist, so (M) alone covers every size, as the paper says (lines
  401-403). Correct. The adversarial tests below show each of steps 2, 4 and 5 is needed.
- Cor. 2.10 (attack item 4): Prop. 2.7(1) is applied to the cut X_y at the port y and to X_{y'} at y';
  both apply because i ∈ I_y ∩ I_{y'}. At least 3 + 3 neighbors in the disjoint O_y, O_{y'} and degree 6
  give exactly 3 + 3; Q_y-degree 3 keeps i out of both 4-cores; three petals would need 9 neighbors.
  Correct.
- Cor. 2.11: y' has its 5 neighbors in I_{y'}, at most one of them in I_y. Correct.
- Prop. 2.12 (attack item 3): (1) outside edges of Q_y are T_y; (2) N(R_I) ⊆ R_O; (3) a T_y edge into
  O_{y'} starts at a vertex of I_y ∩ I_{y'}, which sends exactly 3 such edges and none to R_O, so
  7 = 3 sh_y + e(I_y, R_O), sh_y ≤ 2 (7 is not a multiple of 3) and e(I_y, R_O) ≥ 1; (4) R_O has only
  non-ports and shared vertices send nothing to R_O, so 6|R_O| = 6|R_I| + Σ_y (7 − 3 sh_y) =
  6|R_I| + 42 − 6 ov with Σ sh_y = 2 ov ≤ 12. Hence |R_O| − |R_I| = 7 − ov ≥ 1 and R_O ≠ ∅. The
  vertex-count cross-check also gives 7 − ov. Correct.

### §3 Size bounds (lines 441-513): ACCEPT WITH FIXES (F1 only)

Arithmetic re-derived (attack items 3 and 4):

- Thm. 3.1: |X_y| = 2c + 2 with e = 6c = 3n − 6; |Q_y| = 2t − 1 ≥ 11 with e = 6t − 7 = 3n − 4; 4-cores
  by Lemma 0.4; 2m + 1 ≥ N1 + N2 + 2; with (14, 18): 2m + 1 ≥ 34, m ≥ 17, C0 for m ≤ 16. Correct.
- Thm. 3.2: six pairwise disjoint petal cores, each ≥ N2 + 1: 2m + 1 ≥ 6N2 + 6, m ≥ 3N2 + 3, C0 for
  m ≤ 3N2 + 2 (56 at N2 = 18, |V(B)| ≤ 114). Correct.
- Thm. 3.3: add R (≥ 7 − ov vertices) and the ov shared vertices, all outside every core:
  2m + 1 ≥ 6N2 + 13, m ≥ 3N2 + 6, C0 for m ≤ 3N2 + 5 (59 at N2 = 18, |V(B)| ≤ 120). Correct.
- Lemma 3.4: O_y = {y} ∪ U_y with t_y − 2 non-ports saturated into I_y; t_y = 2 contradicts y's 5
  neighbors; t_y = 6 gives K4,4; t_y = 7 gives K5,5 minus a perfect matching (μ injective) or K4,4
  (μ repeats: four rows miss at most 3 columns). Correct; also verified exhaustively by computer.
- Thm. 3.5: m + 1 = |O| ≥ 6 · 7 + |R_O| ≥ 43, so m ≥ 42, C0 for m ≤ 41, G110-quartic for |V(B)| ≤ 84,
  no census. Correct. The fallback without Prop. 2.12 (m ≤ 40) is also right.

Exact N2 dependence (attack item 4): C0 holds for m ≤ 3N2 + 5, that is, every simple bipartite
6-regular B on at most 6N2 + 12 vertices is G110-quartic, given F2(n) for all n ≤ N2.

| N2 | Census status at review time | C0 bound | \|V(B)\| |
|---|---|---|---|
| none | not needed | m ≤ 41 (Thm 3.5) | ≤ 84 |
| 17 | two methods (two deciders) | m ≤ 56 | ≤ 114 |
| 18 | two methods (two deciders); a third run, same q4core decider, also 0 | m ≤ 59 | ≤ 120 |
| 19 | two generators (genbg_q4, geng_q4), one decider (q4core); both 0 | m ≤ 62 | ≤ 126 |
| 20 | not established (run started 00:56) | would give m ≤ 65 | ≤ 132 |

Thm. 3.1 also uses F1(14), which has two methods. F2(N2) improves on the unconditional bound once
N2 ≥ 13 (3 · 13 + 5 = 44 > 41).

### §4 Residual (lines 515-590): ACCEPT

- §4.1 and §4.2 restate proved facts correctly. The tightness claim (lines 537-539) checks: W = V gives
  (k_U, Φ(U)) = (3, 2) and Φ(W) = −4; W = V − i gives (2, 0) and Φ(W) = −2; both sums are −2. The
  receipt profiles (3,3,1) and (3,2,2) are the only ones with three endpoints.
- §4.3 arithmetic: contraction changes e − 3n by 3|Z| − 3 − e(Γ[Z]); +1 per petal; disjoint petals have
  no edges between them, so k petals give k − 3; cluster formula 21 − 3 ov − 3(#clusters) = 3 − 3β1 and
  cluster degree 7|K| − 6 ov_K; petal minus shared vertices has e − 3n = −4. All correct; the remark
  correctly stops at the lifting step.
- §4.4: P2 + β has 2|C'| + 3 vertices and 6|C'| − ε + 7 = 3n − 2 − ε edges, so the briefed "3n − 2"
  is false when ε = 1. The ε = 1 branch is nonempty (I built 12 such instances myself; d0 = 5 is forced
  and consistent). The 8-edge cut and the modified trace identity x − x' = 4(...) are right.
  P1 + α_τ ∈ E4 is right (deficiencies 2 + 2 and 8 − 4). FLAW.md is accurate.

### §5 (lines 592-606): ACCEPT WITH FIXES

The scope statements are correct and appropriately conservative (no pair statement; G110 open for
m ≥ 42, or m ≥ 60 given F2(18); C1 sub-case open). Fix F1 applies to lines 599-600.

### Appendices (lines 608-723): ACCEPT

SHA-256 of all seven check scripts and of `c1sub_eps1_witness.json` match the first and last 8 hex
digits in lines 695-698 and in FLAW.md. Spot-checked citations: scout PAPER.md lines 33-49, 75, 81-84,
86-106; G110-REVIEW.md lines 100-114, 139-181; REPORT.md lines 238-277; QUARTIC-REVIEW.md lines
187-277; FINDINGS.md line 958; CHECKPOINT-01 line 17, CHECKPOINT-02 line 12, CHECKPOINT-05 lines
28-33; tools/README lines 26-38. All say what the paper says they say. I did not re-run the paper's
scripts.

## What I recomputed, and how

All runs: `[temporary path]` under `timeout 240`, own code in `review/`
(a from-scratch pysat CaDiCaL 1.5.3 encoding of "nonempty, every degree in {0,4}", with optional free
vertices for "realizes τ"; every witness re-checked; flows by networkx; exact negative-cut enumeration by
fixing C ⊆ I and branching on A with Φ = 4|C| + Σ_{a∈A}(e(a, I − C) − 4)). nauty genbg/geng 2.9.3 were
used only as generators. Outputs are in `review/out_*.txt`; every script ends with RESULT: PASS.

| Claim | Script | Method | Result |
|---|---|---|---|
| Lemma 0.2 (Olson, multigraph, Δ ≤ 7) | r_olson.py | exhaustive: all bipartite multigraphs with 3n − 2 edges, Δ ≤ 7, n ≤ 6 (78,561 at n = 6); random n = 7..16; 3n − 3 controls | all have a {0,4}-subgraph; controls fail (2,088 of 93,918 at n = 6) |
| (0.1), (0.2), Lemma 2.8, submodularity, Prop. 2.4, Φ independent of y, Lemma 0.1 | r_identities.py | 300 random gadgets, 9,000 random sets, 26,733 transfers, 44,185 y-checks; flow against exact min slack on 75 graphs H_y and 150 random balanced graphs | 0 mismatches |
| Lemmas 0.3, 0.4 | r_degen.py | every bipartite graph with e ≥ 3n − 8, n = 6..12 (831 graphs) | 4-core nonempty in all; 3n − 9 attained |
| Lemma 0.5 | r_small_exhaustive.py | every E3(s), s = 6, 7, 8 (9,617 graphs; 726 without 4-factor), every violation in both orientations (1,500) | all k = 1, ε = 0, D_A = 3, pieces C0 or single vertex |
| Lemma 2.1 (1)-(4) | r_small_exhaustive.py | every C0(m), m = 5..8 (19,092 graphs), every y0 of degree ≤ 5, every cut with Φ ≤ −1 (16,526) | all items hold |
| Lemma 1.1 items 1-4 with Lemma 2.1 | r_g1.py, r_g1_more.py | 67 planted hosts of all seven types, every negative cut (227) enumerated exactly; max flow = 4m + min slack | all hold |
| G-1 at small orders | r_g1.py, r_g1_more.py | every 6-regular bipartite B on 7+7, 8+8, 9+9 (232 graphs, 24,948 pairs (o, y)); 150 sampled 10+10 graphs (18,000 pairs); two-K5,5 example | every B − o − y has a 4-factor; example cut 10/10 with 10 edges |
| Lemma 2.5, Props. 2.3, 2.4, 2.6, 2.7 (counts, gluing, trace) | r_trace.py | 16 planted (2,5,0) hosts; all 128 trace subsets per host by SAT; gluing per τ (560); X + β; Q + α minus two edges (336); Q + α_τ (199) | traces only of size 0 and 4; identity on 478 witnesses; gluing iff holds; all counts as stated |
| Lemma 3.4 | r_lemma34.py | t = 6 shape; all 7^5 maps μ at t = 7; the proof's witnesses | quartic subgraph in every case |
| Thm 2.9 data, Cors. 2.10, 2.11, Prop. 2.12 | r_hub.py | 52 hub-and-petal gadgets, ov = 0..6 (incl. a 6-cycle of sharing), \|R_I\| ∈ {0,1,3,5}; 780 pairs; all quantities recomputed from the graph | all hold |
| Thm 2.9 minimality steps (adversarial) | r_uncross_adv.py | three families with petals overlapping in ≥ 2 vertices (18 hosts; full cut enumeration on two m = 17 hosts) | failure caught exactly at step 2 (k_U = 1, Φ(U) = −2), step 5 (Γ[Z] C0 with Z_O ≠ ∅) or step 4 (Γ[W] C0, W ≠ V); step-1 and step-3 identities hold; every host has a quartic subgraph |
| §4.4 counts, FLAW | r_section4.py | own C1 sub-case instances, 12 with ε = 0 and 12 with ε = 1; slack −1 checked directly and by flow | e(P2 + β) − 3n = −2 − ε; 7 + ε cut edges; 256 P1 + α_τ in E4 |
| §4.3 contraction counts | r_section4.py | 5 hub gadgets (sharing none, one edge, triangle, matching, 6-cycle) | all formulas hold |

## Paper-checked only

No counterexample to C0 is known, so these steps were checked by hand only (their identities and counts
are covered above, and the adversarial tests confirm that each minimality hypothesis in Thm 2.9 is used
where the paper says): the exclusions in Prop. 2.2 (d0 ≤ 4) and Prop. 2.3 (k = 1); "F uses β / α" in
Prop. 2.6; the contradictions in Prop. 2.7(1)-(4); steps 2, 4 and 5 of Thm 2.9; Cor. 2.10 (it rests on
Prop. 2.7(1)); and the final inequalities of Thms 3.1-3.5 (arithmetic, re-derived above). F1 and F2 were
not recomputed here; their status was read from the census logs.

## Comparison with the author lane (read after the verdicts)

M1-LOG.md and `checks/` agree with every verdict above. The author's checks (A.1-A.6) and mine cover the
same kinds of claims (identities, synthetic (2,5,0) hosts, Olson, G-1 hosts, the C1 sub-case, hub
gadgets) but share no code. Mine add: exhaustive Olson for n ≤ 6, exhaustive Lemma 0.5 on E3(6..8),
exhaustive Lemma 2.1 on C0(5..8), exhaustive G-1 on 6-regular bipartite graphs up to 18 vertices,
exhaustive Lemma 3.4, full negative-cut enumeration on every planted host, and adversarial hosts for each
minimality step of Thm 2.9. The author's hub check covers ov ≤ 3; mine reaches ov = 6.

## Editorial suggestions (optional)

- §0 table, row "§3 M1 refinement": state the general form "C0 for m ≤ 3N2 + 5" next to the N2 = 18
  instance, so the dependence is visible without opening §3.3.
- Lemma 3.4, line 498: "If U_y = ∅ then t_y = 2 < 5" could read "If U_y = ∅ then t_y = 2, but y has 5
  neighbors in I_y".
- Informational only: 3,000 random t = 8 petal shapes all contain a quartic subgraph
  (`review/out_lemma34.txt`). An exhaustive t = 8 case would raise Thm 3.5 to m ≥ 48, but this is not
  claimed and not needed.

## Overall verdict

1. **G-1 (§1): ACCEPT.** Lemma 1.1 and Cor. 1.2 are correct; the wording note on "covers every B on at
   most 20 vertices" is accurate (true via |X| + |Y| ≥ 22; the literal "side ≤ 9" hypothesis fails at
   20 vertices).
2. **Structure theorem (Props. 2.2, 2.3, Lemma 2.8, Thm 2.9, Cors. 2.10, 2.11, Prop. 2.12): ACCEPT.**
   The induction is well founded, the minimum slack −1 and both minimality steps are used correctly, and
   the degenerate cases are covered.
3. **Trace lemmas (Lemma 2.5, Props. 2.4, 2.6, 2.7): ACCEPT.** Olson applies at exactly 3n − 2 with
   Δ = 7 on multigraphs; x ∈ {0, 4}; Q + α_τ is a simple E3 instance.
4. **Size bounds: ACCEPT WITH FIX F1 (provenance text only).** Unconditional: C0 for m ≤ 41
   (|V(B)| ≤ 84). Conditional: C0 for m ≤ 3N2 + 5 given F2(N2). F2(18) is established by two methods
   with different deciders, giving m ≤ 59 (|V(B)| ≤ 120); F2(19) has two generators but one decider
   (m ≤ 62, |V(B)| ≤ 126); F2(20) is not established.
5. **Residual statement (§4, §5): ACCEPT.** Correctly stated; the C1 sub-case remark is correctly
   marked false for ε = 1.

Nothing fatal.

## End-of-review checks

- Paper SHA-256 at end (00:59:45): `cfce4fcc7d40732c2f2a6c23b9d5fe50823c37f9d37f940b7857d8eda52ab0c9`,
  unchanged and equal to FROZEN.sha256.
- Census at 00:59: f2_n18 (geng_q4) 40/40 shards, 0 graphs; f2_n19 (geng_q4) 400/400 shards, 0 graphs;
  f2_n20 running.
- Files written by this lane: this REVIEW.md and `review/` (rv_common.py, eleven r_*.py scripts and
  their out_*.txt outputs). Nothing else was modified.
