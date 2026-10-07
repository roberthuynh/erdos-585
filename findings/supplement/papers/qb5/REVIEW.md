# REVIEW: QB(5) reduced to E5 (wave4/qb5/PAPER.md)

Independent adversarial referee, October 5, 2026. Status: FINAL.
Object: `PAPER.md` as frozen in `FROZEN.sha256` (`shasum -a 256 -c FROZEN.sha256`: all 17 entries OK at the
start and at the end of this review). Working files, log and code: `review/` (`review/LOG.md`, `review/code/`,
`review/data/`). Nothing here is a project-oracle PASS: no Lean, no `check.sh`.

Method. Every proof step was re-derived by hand. Cited inputs were checked against their own text
(C1-PAPER.md, P4 PAPER.md, P4 FLAW.md, census CENSUS.md and STATE.md; all four SHA-256 prefixes match
Appendix B). Every certificate and every smallest-size claim was checked with my own code, written from
scratch in `review/code/`. Nothing in `qb5/code/` was run, imported or read; the author's `.g6` data files were
used only as inputs. Graph classes were regenerated with plain nauty genbg 2.9.3 (no prune hook) and compared
by labelg canonical forms. Compute used: about 45 core-minutes.

## 1. Verdicts

| Claim | Verdict | Short reason |
|---|---|---|
| **Theorem 7.1** (a minimal QB(5) counterexample is E5: two 2-blocks, 7 cut edges with no 4-matching, n even, n ≥ 28; n ≥ 40 with the census) | **ACCEPT** | Every step re-derived (Lemma 2.1, Thm 5.1, Thm 6.1, Lemmas 6.2-6.4). n ≥ 28 is on paper. The n ≥ 40 clause rests on a computation (rung b) and inherits the citation fix F6 of Lemma 6.4; I re-checked exactly the subclass it needs by a second method (§4). |
| **Theorem 5.1** (every sparse C2 instance has a good W-vertex; (i) ≤ 5, (ii) ≤ 6, (iii), (iv)) | **ACCEPT** | All four parts re-derived, including every "meet exactly in T" case split, the budget 3a + 6b + 5d ≤ 10 and the p ≥ 2 count in (iv). No minimality used. No counterexample in 1.24 million sparse instances at n = 17 (γ-only there), the complete n = 19 two-block family, and 1,011 of my own random instances at n = 21, 23. |
| Petal-union (lattice) failure first at **n = 19**, proved smallest and certified | **ACCEPT WITH FIXES** (F4) | Lower bound (Lemma 4.2(d): 10 + 9) correct; all 12 certificates verified. But every split petal in them belongs to a degree-6 W-vertex, never a port. For petals of ports, the C1 step's literal form, the first failure is n = 21 (my certificate). |
| E5 gluing failure first at **n = 22**, proved smallest and certified | **ACCEPT WITH FIXES** (F5) | König + Lemma 6.3's first step + K_{4,6} argument correct; all 100 instances verified (sparse, no 4-factor, unique cut, matching number 3 on it). The "60 and 40 instances" are 18 and 33 isomorphism classes. |
| Port-only failure at **n = 15** (and smallest) | **ACCEPT WITH FIXES** (F3) | The three P4 graphs verified (type γ only, four degree-4 ports on u0, degree-6 W-vertices good). Smallest is true (no instance at n = 11, 13 in the complete classes), but the paper gives no argument or computation for it, while §0 says "proved". |
| Lemmas 2.1, 3.1, 3.2, 4.1, 4.2; Theorem 6.1; Lemmas 6.2, 6.3 | ACCEPT | Re-derived; Lemma 3.1 identities and Lemma 3.2 table also asserted on every violation of every graph I ran. |
| Lemma 6.4 | ACCEPT WITH FIX (F6) | n ≥ 28 on paper is correct; the census clause needs its citation fixed. |
| Identities 1.1-1.4, Lemma 1.5 | ACCEPT WITH FIX (F1) | The h-form of Identity 1.2 is misstated (unused). |
| Corollary 7.2 | ACCEPT WITH FIXES (F2) | (a) fails literally at K_2; (b)'s hypothesis is literally false at t = 0. |
| §8.4 remark, Appendix A counts | ACCEPT WITH FIXES (F5, F7) | "mostly" should be "only"; colored-graph counts presented as graph counts. |

No REJECT. I found no mathematical error in any proof.

## 2. Required fixes, with locations

- **F1** (line 53, Identity 1.2). "The same identity holds for h" is false with the coefficient 2. From
  g = 2h + 6κ and modularity of κ: h(A ∪ B) + h(A ∩ B) = h(A) + h(B) − e(A − B, B − A). Fix the coefficient
  or drop the clause; nothing in the paper uses it (every h value is computed from g and κ by Identity 1.1).
- **F2** (lines 376-381, Corollary 7.2). (a): K_2 is a sparse E5 instance (s = 1, both degrees 1, sparsity
  vacuous) with no 4-regular subgraph, so "QB(5) iff every sparse E5 instance has a 4-regular subgraph" fails
  as written; add n ≥ 3 (equivalently s ≥ 2; s = 2, 3, 4 are empty since 6s − 5 > s²). (b): the 2-block graph
  with t = 0 (two isolated vertices) has no 4-regular subgraph, so the hypothesis is false as stated; add
  t ≥ 1 (then t ≥ 4 is forced), which is also what "the j = 2, d = 0 part of QB(6)" means with n ≥ 3.
- **F3** (line 25 and §8.1, lines 394-398; A.1, line 476). The table says each §8 size is "proved
  smallest". For n = 15 (ports only) there is no proof, and A.1 does not report the needed computation (its
  "core check" for u0 graphs is about W-vertices off N(u0), not ports). The fact is true: in the complete
  sparse C2 classes the number of graphs with every port bad is 0, 0, 3 at n = 11, 13, 15 (§4). Add that line
  to A.1 and call this size "computed smallest".
- **F4** (§8.2, lines 400-407, and the §8 intro, line 392). In all 12 certificates the bad W-vertices are
  T_W ∪ {17, 18}, all of degree 6, and the split petals T + 17, T + 18 contain no port. For the 3 u0
  certificates 17, 18 lie in W − N(u0), so the split is relevant to Theorem 5.1(iv); for the 9 u1u2
  certificates it is irrelevant to Theorem 5.1(i)-(ii), which only use ports. The family in §8.2 is all
  n = 19 sparse C2 instances with a W-small 2-block on Z_U (|T| ≥ 10 and |B| ≥ 9 force T = K_{4,6},
  B = K_{3,6}), and in all 64 every port is good. So for petals of ports, the step C1 actually uses, the
  first split is at n = 21: certificate `review/data/cert_portsplit_n21.g6` =
  `T??F~z{~????????J?g?]@BrGI@?]C?]?ON?` (Z_U = {u1, u2}, T = {0, ..., 9}, bad ports 14 and 17 of degree 5,
  α-petals T + 14 and T + 17, union κ = 0). Say "α-petals of W-vertices" in 8.2 and add the port statement
  with n = 21.
- **F5** (§8.3, line 414; A.6, line 482; §8.4, line 420). The 60 instances at n = 22 are 18 isomorphism
  classes and the 40 at n = 24 are 33 (labelg); say so. In §8.4, "(mostly p ∈ A, q ∈ D)" should be "only":
  in all 100 instances every good pair has p ∈ A, q ∈ D, and this is forced, since for p ∈ B, q ∈ D the
  cut violation (A, C) survives in G − p − q (slack 7 − e(A, q) − 8), for p ∈ B, q ∈ C so does (A, C − q)
  (slack 7 − 12), and for p ∈ A, q ∈ C so does (A − p, C − q) (slack 7 − e(p, D) − 8). The claim that k
  ranges over 1 to 5 checks out (both orientations, every instance).
- **F6** (Lemma 6.4, line 364). The cited CENSUS.md line 37 records F1 at n = 18 as "projected"; the
  completion is STATE.md line 31 (cited only in Appendix B, line 499). Cite it in the proof as well, and keep
  "n = 17, 18 by one method".
- **F7** (A.1, line 476). "13, 818 E5 graphs" (and "229,728" at n = 16) count genbg's two-colored outputs;
  as graphs these are 9, 447 and 115,932. Say "two-colored graphs" or give both counts.

Optional: in the Lemma 3.2 table the column "ε, def(w)" holds a description in the γ row; in A.3 the β
template has n = 19 for 16 graphs, so "(n = 19 to 21)" is right but the α templates are all n = 21.

## 3. Proof notes (re-derivation, adversarial points)

- **§1.** Identity 1.1 is C1 Identity 1.1 with h = D^S(S_W). Identity 1.3's v ∉ S form and Identity 1.4 are
  one-line counts. Lemma 1.5: s → P (cap 4), edges (cap 1), Q → t (cap 4); a cut with A, C on the source side
  gives the stated criterion; slack 2k − D_A + ε by expanding e(A, Q − C); k ≤ 0 gives slack ≥ 0.
- **Lemma 2.1.** n²/4 < 3n − 5 iff 2 < n < 10; at n = 10 only K_{5,5}. Edge-minimality gives e = 3n − 5;
  sparsity from n-minimality; δ ≥ 4 from g(V − v) = 4 + 2deg v; g(V) = 10 = 2d + 6j gives (0, 5) or (1, 2).
- **Lemma 3.1.** Re-derived e(Q) = 6|U − C| − D(U) + D(C) − (6k − D_A + ε) and g(Q) = 6 + 2D(U) − 2D(C) +
  2k + 2σ; κ(Q) = k − 1; h(Q) = 8 − 2k + σ − D(C). The deficiency of C in G − w is D(C) + e(w, C), which
  gives ε = D(C) + e(C, W − A).
- **Lemma 3.2.** |Q| = 2 forces A = W − w, k = 1, deg u' − e(w, u') ≤ 3, so deg u' = 4, w ~ u' (γ).
  |Q| ≥ 3 gives k + σ − D(C) ≥ 1; k = 1 impossible; k = 2: σ = −1, D(C) = 0 (α); k = 3: σ ∈ {−1, −2}, giving
  β1a, β1b (D(C) = 1 forces ε = 1, def(w) = 0) and β2. Port restrictions and D(Q_W) = 1 in β1a follow.
  Mutually exclusive by (k, σ, D(C)).
- **Lemmas 4.1, 4.2.** Common neighbors: 3 + 3 − 4 = 2 for u0, 3 + 3 − 5 = 1 for u1. Q ∪ Q' = V gives
  κ(∩) = 3 against g(∩) ≤ 14. Lemma 4.2: D^T(T_U) = 12 = 2 + 10; g(B) = 18, D^B(B_U) = 0; (e) needs |T| ≥ 4,
  true since T_W ≠ ∅; (d) by δ ≥ 4.
- **Theorem 5.1(i).** Closure of 𝒜 under union from Lemma 4.1. Two β1a-only petals: union = V gives
  κ(∩) = 5 against g(∩) ≤ 18; |∩| ≥ 3 forces both g = 14, κ = 2 and h(∪) = 1 < 2. Fact F gives two
  neighbors of u1 in each, disjoint, so at most 2 such ports. 3 + 2 = 5 < 8.
- **(ii).** Checked each case of (1)-(5): (1) κ(T ∪ Q) = 2 contradicts maximality of T; (2) split must be
  (2, 0) with ∩ = T; (3) g(R − T) = 2c(R), |R − T| odd, c = 3 iff R = T + y, def(y) ≤ 2; (4) the case
  T ∩ Q = Z_U (possible: 3 + 2 = 5) is handled, |R'_y − T| = 2 is impossible since x ∈ B_U has no neighbor in
  T, so c' ≥ 5; (5) all four sub-cases of an ℳ1 member against a P2 port close (the (1, 2), g(∪) = 14 case
  uses a port of R ∩ P1). Budget: max of 2a + 3b + d under 3a + 6b + 5d ≤ 10 is 6 (a = 3).
- **(iii).** |W| ≥ 6 needs s ≥ 5, true for every C2 instance (6s − 2 ≤ s(s + 1)). (iii-a): R* misses at most
  one neighbor of u0, at least two W-vertices; Claim A's {u0, x} case gives κ(∪) = 3 against g(∪) ≤ 16;
  Claim B; R** has |R**_W| ≥ (s − 3) + 3. (iii-b): M_i share no W-vertex (κ(∪) = 4 against g ≤ 18), r ≤ 2,
  both cases overflow U.
- **(iv).** β2 excluded at B_W ∩ W' (union would be a larger 2-block); α and β1a reduce to (ii)(1), (ii)(4).
  ℳ vs ℳ' members are nested or meet in T. Counting: |B_W| − |N(u0) ∩ B_W| ≤ |B_U| + p gives p ≥ 2; p = 3 forces
  three T + y and |B_W| ≤ 4; p = 2 forces equality, the uncounted edge u0x0, and each sub-case fails (the
  c = 3, c = 6 case gives R_2 = V − x0 − y and deg x0 + deg y = 7).
- **Theorem 6.1.** e(X) = 6|C| − ε, g(X) = 6k + 2ε; with 2k + ε ≤ 4 and 3k + ε ≥ 6 (|X| ≥ 3): k = 2,
  ε = 0, D_A = 5, σ = −1; |X| ≤ 2 contradicts δ ≥ 4. The 0-or-4 cut remark: e_H(A, D) = 4(|V(H) ∩ A| −
  |V(H) ∩ C|).
- **Lemmas 6.2, 6.3.** Checked Δ ≤ 6, simplicity, vertex counts < n, edge counts 3n' − 5, that the
  4-regular subgraph must use the new vertex or edge, and vertex-disjointness of the glued halves; vc and
  ad are in neither half.
- **Lemma 6.4.** K_{4,6} ⊇ K_{4,4}; on 12 vertices either a repeated miss gives K_{4,4} or K_{5,5} minus a
  perfect matching. QB(6) for ≤ 18 vertices from F1(n ≤ 18) via the usual minimal-counterexample reduction
  (vacuous for 3 ≤ n ≤ 9, δ ≥ 4 by deleting a low-degree vertex).
- **Theorem 7.1.** The only uses of minimality in the C2 case are sparsity and "every W-vertex is bad"
  (Lemma 2.1(d)); Theorem 5.1 then contradicts. Correct.

## 4. Computations (own code, `review/code/`)

| Check | Code and input | Result |
|---|---|---|
| Classes | plain genbg -d4:4 -D6:6: 5 6 28, 6 7 34, 7 8 40, 6 6 31, 7 7 37, 8 8 43 | 2, 29, 2,895 C2 graphs, all sparse (subset DP), labelg-identical to P4's files; E5: 13, 819, 229,913 colored, of which 13, 818, 229,728 sparse (= P4), all with a 4-factor |
| A.1 | `rv c2` (flow per W-vertex, Lemma 1.5 enumeration, Lemma 3.1/3.2 asserts) | bad W-vertices 4, 36, 2,640, all γ; no α/β violation; core check holds; u0/u1u2 1+1, 9+20, 660+2,235; flow and enumeration agree everywhere; every-port-bad graphs 0, 0, 3 |
| P4 Thm 3.1(c) | three n = 15 graphs from FLAW.md line 32 | C2, sparse, Z_U = {u0}, four ports of degree 4 on u0, all bad (γ only), all degree-6 W-vertices good |
| n = 17 (extra) | genbg 8 9 46, 1,237,978 graphs, `rv c2q`, 64 shards | 1,237,962 sparse; no α/β violation; all 870,836 bad W-vertices γ; Thm 5.1 holds in all; 18 with every port bad |
| n = 19 family | `tb19_own.py` (own enumeration of 6×6 cut matrices up to row/column permutations) | 64 classes = author's 64 (labelg); all sparse (14 u0, 50 u1u2); bad W 4-6; types α, β2, γ; 12 with a (2, 0) α-split, 0 with (0, 2); every port good in all 64 |
| §8.2 certificates | `tb19_split.g6`, `rv c2` | all 12 as claimed; graph 1: u0 = 5, Q ∩ Q' = T = {0..9}, Q = T + 18, Q' = T + 17, κ(Q ∪ Q') = 0 |
| §8.3 certificates | `e5_n22.g6`, `e5_n24.g6`, `rv e5pairs`, `e5k` | all 100: sparse, no 4-factor, exactly one violation per orientation, Thm 6.1 structure, cut matching number 3, K_{4,4} present, good pairs 35-40/121 and 40-47/144, all with p ∈ A, q ∈ D; k ∈ {1..5}; 18 and 33 isomorphism classes |
| A.3, A.4 | author's template and j1/j3 data through `rv c2` | 293/290/287 sparse, bad-port deficiency exactly 3/1/2; j3: ≤ 2; j1: good W-vertex off N(u0) in all 1,500; the only rv flags are Lemma 3.2 "other" types in non-sparse graphs, where the lemma does not apply |
| Stress (extra) | `gen_rand.py` (own: random 10- or 12-vertex W-small 2-block on Z_U, random 3-block), n = 21, 23 | 1,011 sparse of 1,080: Thm 5.1 holds, bad-port deficiency ≤ 2; 3 graphs with a (2, 0) split of two bad ports' α-petals (n = 21, 23, 23) |
| n = 21 certificate | `verify_portsplit.py` (Python + networkx, separate from rv.c) | sparse, ports 14 and 17 bad, T + 14, T + 17 α-petals (k = 2, σ = −1, D(C) = 0), union κ = 0 |
| Lemma 6.4 census (second method) | genbg -d6:0 -D6:6 c c+2, e = 6c, all 2-block graphs, own complete decider `q4.c` | c = 6, 7, 8 (|X| = 14, 16, 18): 197, 18,208, 8,452,423 graphs, every one has a 4-regular subgraph. So |X|, |Y| ≥ 20 and n ≥ 40 hold by a method independent of the census's q4core decider. |

## 5. What this review adds

1. The port form of the petal lattice first fails at n = 21, not 19 (F4); n = 19 is right for petals of
   W-vertices, which is what Theorem 5.1(iv) needs.
2. n = 15 is the smallest port-only failure, now backed by complete classes (F3).
3. The n ≥ 40 bound for a minimal counterexample has a second, independent computation for exactly the
   2-blocks it needs.
4. In the E5 instances good pairs lie only in A × D, and provably so (F5).
