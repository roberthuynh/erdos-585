# Referee report on wave4/s6/PAPER.md

Status: FINAL. Every claim below carries a final verdict.
Referee lane, October 5, 2026. PAPER.md checked against FROZEN.sha256 at start and at end: OK
(d47ae403…). Nothing in s6/ was edited except this file. Working files: `review/LOG.md`,
`review/code/`, `review/out/`. None of the author's code in `s6/code/` was run or imported; the
certificates in `s6/data/` were read as data only.

Line numbers refer to PAPER.md as frozen.

## Final verdicts

| # | Claim (lines) | How checked | FINAL verdict |
|---|---|---|---|
| 1 | Identities (1.1), (1.2) (37-43) | by hand | ACCEPT |
| 2 | Lemma 1.1: B − o sparse iff B is E10, independent of o (45-51) | by hand | ACCEPT |
| 3 | Lemma 1.2: cut bounds in Y, Y 5-edge-connected, no thin set (55-72) | by hand | ACCEPT WITH FIXES (citation, line 69) |
| 4 | Lemma 2.1: Y has a 4-factor, every size (76-83) | by hand; observed in all 25,232 sampled (B, o, y) | ACCEPT |
| 5 | Splitting off, frames, Lemma 2.2: frames exist for every π (88-107) | by hand; own frame builder | ACCEPT |
| 6 | Lemma 2.3: S6 at (o, y) iff some frame for π has Φ = 2, for every π (109-114) | by hand | ACCEPT |
| 7 | Moves keep the frame property (116-125) | by hand; own frame check | ACCEPT |
| 8 | Lemma 3.1 (parity) (132-151) | by hand, every step; numerically, 0 failures | ACCEPT |
| 9 | Corollary 3.2 and the girth-6 remark (153-162) | by hand | ACCEPT WITH FIXES (157, 160-162) |
| 10 | Theorem 4.1: Lemma K implies S6 (173-182) | by hand | ACCEPT WITH FIXES (framing, lines 19, 180-182, 405-408) |
| 11 | Remarks (B1)-(B3) (184-191) | by hand | ACCEPT WITH FIXES (185-188) |
| 12 | "The hypothesis is needed": B24, o = 7 (193-196) | by hand; own code | ACCEPT |
| 13 | Example 4.2: one move is not enough, \|B\| = 16 (200-207) | own code | ACCEPT |
| 14 | §4.2 evidence: all 1,532 minima from 4,472 frames escape (21, 209-231) | data files reconciled; independent sample, own code | ACCEPT |
| 15 | Example 4.3: three moves are not enough, PG(2,5) needs exactly 4 (233-240, 394-399) | own code | ACCEPT WITH FIXES (238-240, 396-397) |
| 16 | §4.3: obstruction notes and "Lemma K restated" (244-263) | by hand; data files | ACCEPT WITH FIXES (250-253, 255, 260) |
| 17 | §5 census bullet (267-270) | against va6 PAPER, va6 REVIEW, S6-RESULT.md | ACCEPT WITH FIXES (citations) |
| 18 | §5 banked conditional: 2EC_Y + H22 give S6 for \|B\| ≤ 24 (271-276) | by hand; against pairs SCOUT §2.3 and pairs REVIEW | ACCEPT |
| 19 | §5 "Why the bank is not the target" (277-278) | against pairs SCOUT §2.3, theory PAPER §8 | ACCEPT WITH FIXES (wording) |
| 20 | §6 preamble (F0)-(F3), cut types (282-294) | by hand | ACCEPT WITH FIXES (284, 288-289) |
| 21 | Lemma 6.1 (296-302) | by hand | ACCEPT |
| 22 | Lemmas 6.2, 6.3 (304-316) | by hand | ACCEPT WITH FIXES (state the minimality hypothesis) |
| 23 | Lemma 6.4 (318-319) | by hand | ACCEPT |
| 24 | Theorem 6.5 (321-333) | by hand, every case | ACCEPT WITH FIXES (line 321 wording) |
| 25 | Corollary 6.6 (335-337) | by hand | ACCEPT |
| 26 | §6.1 discussion (339-361) | by hand | ACCEPT WITH FIXES (343, 359) |
| 27 | §7: the one forced-set shape (368-372) | by hand | ACCEPT |

No REJECT. Every theorem and lemma is correct as a mathematical statement. The fixes are wording,
citation and framing. Some sentences outside the theorems are false, each with a counterexample
or a data citation:
- two in Example 4.3 (item 15);
- the "last merge / last step" gloss (items 9, 11, 16);
- one percentage (item 16).

None of them changes a theorem or a refutation.

## Details

### 1-3. Setting, Lemma 1.1, Lemma 1.2 (lines 25-72)
- (1.1): the degree sum over S_P is 6|S_P| − a = e(S) + ∂_P(S), with e(S) = 3|S| − g/2, so
  ∂_P = g/2 − 3j − a; the same over S_Q. (1.2): 6|S| = 2e_B(S) + ∂_B(S) and e_Y(S) = e_B(S), so
  g(S) = ∂_B(S). The edges from S to {o, y} number a + b, so ∂_Y = g − a − b. Correct.
- Lemma 1.1: the sets S ⊆ V(B) − o with 2 ≤ |S| ≤ |B| − 2 are exactly the o-free sides of the
  bipartitions with both sides of size ≥ 2, and g_Γ(S) = ∂_B(S). Correct, and o-independent.
- Lemma 1.2: (i) the complement contains o and y. (ii) ∂_B(S + o) = g + 6 − 2a, with S + o of size ≥ 2
  and complement (V(Y) − S) + y of size ≥ 2. (iii) ∂_B(S + o + y) = g + 10 − 2a − 2b (y has b + 1
  neighbors in S + o). The ∂_Y bound and "≥ 5" follow, and single vertices have degree ≥ 5. All
  correct. No-thin-set remark (69-72): for j = 0, ∂_P − ∂_Q = b − a and ∂_P + ∂_Q ≥ 4 + |a − b|, so
  min ≥ 2. Correct.
- Fix (line 69): "(va6 PAPER Ex. 4)" covers B24 only. R20 is `wave3/pairs/PAPER.md` Example 4.

### 4-7. Lemma 2.1, frames, Lemmas 2.2, 2.3, moves (lines 76-125)
- Lemma 2.1: the cut capacity for source-side A ∪ C is 4|P − A| + e(A, Q − C) + 4|C|, so a 4-factor
  exists iff s'(S) = 4j + ∂_P(S) ≥ 0, and s' = g/2 + j − a by (1.1). Endpoint cases: s' = 0. Otherwise
  s' ≥ 2 + j by 1.2(ii), and for j ≤ −3, ∂_Q ≥ 0 gives s' ≥ b − a − 2j ≥ 1. Correct. My samples
  found a 4-factor in every one of 25,232 random (B, o, y) on E10 hosts.
- Splitting off (88-93): Y⁺ is 6-regular bipartite. The 1-factorization correspondence is correct.
- Lemma 2.2: H + Λ is 2-regular bipartite. Λ is a matching, so a 2-cycle is a Λ edge parallel to
  an H edge. Even cycles 2-color, and König splits F. Correct.
- Lemma 2.3: both directions are correct for every π, and E10 is not used.
- Moves: the legality rule is exact (a Λ edge can sit only in N_4 or N_5). A Λ re-pairing keeps N_k
  a perfect matching and gives a frame for π ∘ (p p′). Correct. My code checks every sampled frame
  after the random walk and after descent (`check_frame`), and every check passed.

### 8. Lemma 3.1 (lines 132-151): ACCEPT
- (a) σ = τ_N^{-1}τ_{N′}: the cycles of N ∪ N′ (2-cycles included) are the cycles of σ, so
  sign σ = (−1)^{m − c}, and σ = (β^{-1}τ_N)^{-1}(β^{-1}τ_{N′}).
- (b) Multiply (a) for the two pairs.
- (c) τ_i^{-1}τ′_i is the identity off Z ∩ P and one ℓ-cycle on Z ∩ P, so each sign is multiplied by
  (−1)^{ℓ−1}. The three parity cases follow.
- (d) A Λ re-pairing composes τ_{N_k} with a transposition of Q. The identity is (b) times (a) for
  (N_4, N_5).
- All correct. Numerical check (`code/parity_check.py`, `out/parity_check.txt`): 27,000 instances
  of (a), 1,800 of (b), 1,027 of (c), and 1,800 + 1,027 + 3,600 + 5,400 of (d) (the identity,
  Kempe, re-pairing and Λ re-pairing cases). 0 failures.

### 9. Corollary 3.2 (lines 153-162): ACCEPT WITH FIXES
- (i) With ℓ odd, every sign is unchanged, so every c(N_i ∪ N_j) changes by an even amount. A net
  change of −1 in c(C′) needs ℓ even, that is |Z| ≡ 0 (mod 4). Correct.
- (ii) As stated ("contains a swap ...") it is correct: only a legal swap with i ≤ 3 < k and ℓ even
  changes the parity of Φ.
- Fix (line 157): the gloss "the leftover of B must supply the last merge" does not follow. The
  parity-changing swap need not be the last move or a merge. Concrete cases
  (`code/last_step.py`, `out/last_step.txt`): three random E10 frames (|B| = 20, 24) with Φ = 5
  descend by single non-raising moves along Φ = 5 → 4 → 2. In each, the last move is not a swap of a
  cycle color with a leftover color on a chain ≡ 0 (mod 4). The three last moves are:
  - a (3, 5) swap on a 6-chain;
  - a (1, 3) swap on a 14-chain;
  - a (0, 2) swap on a 10-chain.

  The same overstatement is at line 188 ((B3)) and at line 250. Minima with Φ = 5 also occur: 60 of
  the minima in my samples have Φ = 5.
- (iii) Correct.
- Fix (lines 160-162): "no Kempe 4-cycles" should read "no Λ-free Kempe 4-cycles". Chains of colors
  4 and 5 can be short through Λ edges, even 2-cycles. The ≥ 8 conclusion holds for the swaps that
  change C or C′, which must be Λ-free. Also, "NOTES §A" points to an unfrozen file that another lane
  is editing. Define "merging move" in the paper instead.

### 10. Theorem 4.1 (lines 166-182): ACCEPT WITH FIXES (framing only)
- The proof is complete and correct. Lemma 2.2 gives a frame. Each application of Lemma K lowers Φ
  by ≥ 1 and never raises it, and Λ re-pairings change π, which is harmless because Lemma K is
  quantified over every π. Φ ≥ 2 is an integer, so a Φ = 2 frame is reached, and Lemma 2.3 (⇐) gives
  the two Hamilton cycles. "Hence ... S6 for all sizes" follows by Lemma 1.1.
- The "Lemma K restated" claim (259-260) is also correct. If K fails at f, the set of frames reachable
  from f by non-raising moves is nonempty, closed and at level Φ(f) ≥ 3. Conversely, at a frame of
  least Φ in a closed set, K fails.
- Fix (lines 19, 180-182, 405-408): the reduction goes to a stronger statement. For a fixed
  (B, o, y), S6 says that some frame has Φ = 2. Lemma K says that a Φ = 2 frame is reachable from
  every frame by non-increasing moves. Lemma K plus Lemmas 2.2 and 2.3 gives S6, and S6 is not known
  to give Lemma K. Example 4.3 and my second depth-4 example below show that the frame graph has deep
  local minima. Theorem 4.1 is a correct reformulation of S6 as a reachability statement on the
  frame graph, with Lemmas 1.2-2.3 as routine inputs. It does not make S6 easier, and "S6 reduced to
  Lemma K, every other step proved" should say so.
- Optional (line 173): write "for (B, o, y) and every bijection π". The proof uses Lemma K at the π
  current after Λ re-pairings.

### 11. Remarks (B1)-(B3) (lines 184-191): ACCEPT WITH FIXES
- Fix (lines 185-187): "a frame is a 1-factorization of B cut open at o and y ... the two leftover
  classes of B". Under the correspondence of lines 90-93, a 1-factorization of B puts the five Λ edges
  in five different classes, while a frame puts all five in N_4 ∪ N_5. So no frame is the image of a
  1-factorization of B. Say "a 1-factorization of Y⁺", and "the leftover H + Λ" for the last two
  classes.
- Line 188: the "last merge" fix of item 9.
- The Meredith-type graph is cited from theory PAPER §8, which takes it from
  `reports/585-plan/report.html` and does not re-check it. This is not load-bearing.

### 12. B24 with o = 7 (lines 193-196): ACCEPT
Own construction (`code/b24_check.py`, `out/b24_check.txt`) equals `va6/data/b24.json`, and the
minimum essential cut is 2. For o = 7, all six ports y = 18..23 give Y a 4-factor. Copy 1 has one
Y-edge leaving each color class (0 and 1 for y = 18). So every 4-factor has ∂_F(T) ≤ 2 (pairs
PAPER (1)), no frame has Φ = 2, and K fails at a frame of least Φ. Correct.

### 13. Example 4.2 (lines 200-207): ACCEPT
Own code (`code/cert.py ../data/ml1_counterexample.json brute`, `out/cert_ml1.txt`):
- B is simple, bipartite and 6-regular on 16 vertices. Brute force over all 2^15 sets gives a
  minimum essential cut of 10.
- Y⁺ is rebuilt from B, o = 0, y = 11 and the Λ flags. The frame is valid, with c(C) = 2, c(C′) = 1
  and Φ = 3.
- There are exactly 17 legal Kempe swaps (paper: 17), and none lowers Φ: they give Φ = 3 (14 swaps),
  4 (2) and 5 (1). Both re-pairings give 3. ML-1 is false.
- An escape exists at depth 2.
- The author's `verify_min.py` and `verify_depth.py` import nothing from `frames.py`, which bears out
  the "shares no code" claim.

### 14. §4.2 evidence (lines 21, 209-231): ACCEPT (rung (b), now two methods in kind)
- Every row of the table reconciles with `data/escape_*.txt` and `data/escapeB_*.txt`, and the
  totals are 4,472 frames and 1,532 minima. Rows with two files: |B| = 24 is M12 + escapeB_M12,
  |B| = 40 is M20 + escapeB_M20, and PG(2,5) is pg25 + pg25_b.
- Own independent run (own random hosts by edge switches, E10 checked by flows, own frames, 300-step
  random walk, random descent, own BFS without Λ re-pairings, cap 20,000):
  - First sample (`out/sample_*.txt`): 2,932 frames gave 1,020 minima, and all escape. Depths:
    |B| = 16 {2: 87, 3: 1}, 20 {2: 94, 3: 1}, 24 {2: 111, 3: 2}, 30 {2: 140, 3: 1}, 40 {2: 50, 3: 1},
    50 {2: 52}, 62 {2: 70, 3: 1}; PG(2,5) {2: 164, 3: 8, 4: 1}; H19 {2: 123, 3: 1}; H23 {2: 112}.
  - Larger search (`out/big_*.txt`): 22,300 frames gave 8,968 minima, with 0 unresolved and 0
    non-E10 hosts rejected. That includes 7,500 frames on PG(2,5), where every escape is at depth
    2 or 3.
- So the claim is reproduced in kind by code that shares nothing with the author's. Depth 2 is the
  rule, depth 3 is rare and depth 4 is very rare.
- Notes:
  - (a) "Strict local minimum" is a misnomer: every such frame has Φ-neutral neighbors (the escapes
    use them). "Local minimum (no single Φ-lowering move)" is accurate.
  - (b) The random-host files `escape_M*.txt` do not record the E10 test, though line 210 says it
    was run.

### 15. Example 4.3 (lines 233-240, Appendix 394-399): ACCEPT WITH FIXES
Own code (`code/cert.py`, `code/pg_e10.py`, `code/variants.py`; `out/cert_pg25.txt`,
`out/pg25_e10.txt`, `out/variants_pg25.txt`):
- The host satisfies the projective-plane axioms of order 5 (any two points have exactly one common
  line, and dually), so by uniqueness of the plane of order 5 it is PG(2,5). Girth 6. Minimum
  essential cut 10, from flows over all 16,275 pairs of disjoint edges (this routine is validated
  against brute force and on planted 2-, 6- and 8-cuts, `out/test_e10.txt`).
- The frame is valid, with Φ = 3. BFS over all move types, Λ re-pairings included, finds no
  Φ-lowering sequence of ≤ 3 non-raising moves, and finds one of 4 moves. Without Λ re-pairings the
  answer is also 4. K3 is false, as claimed.
- The counts 9, 47, 211 are reproduced exactly when frames are counted labeled (no identification
  of color relabellings), with the re-pairing moves taken as the two fixed permutations. Counted up
  to relabellings that keep the pairing, they are 6, 21, 81. The depth is 4 under every convention.
- Fix (lines 238-239, 396-397): "211 ... at depths 1, 2, 3, none with a Φ-lowering move; an escape
  at depth 4" contradicts itself, and the depth-3 part is false. The 211 depth-3 frames admit 17
  Φ-lowering moves, which are the depth-4 escapes. Correct statement: the start frame and the 9 and
  47 frames at depths 1 and 2 have no Φ-lowering move, and some of the 211 depth-3 frames have one.
  State the counting convention.
- Fix (lines 239-240): "any proof of Lemma K has to allow sequences of unbounded or at least
  growing length, and girth 6 is where the long sequences appear first" is not supported. K3 false
  shows only that 4 moves are sometimes needed. The girth clause is contradicted by this
  counterexample from my search:
  - Host: the Haar graph H(Z_23, {3,5,9,13,17,20}), 46 vertices, built by my code. Girth 4 (5 + 17 =
    9 + 13 mod 23), minimum essential cut 10.
  - Frame: o = 17, y = 45, Φ = 3 with c(C) = 1 and c(C′) = 2.
  - It needs exactly 4 moves, with Λ re-pairings (levels 6, 20, 67 up to relabelling) and without
    them (`out/deep_h23_105_0_365.json`, `out/deep_h23_check.txt`).
  - Delete the girth clause and say "at least 4 moves".
- Note: `data/pg25_e10_check.txt` holds only the E10 line and a vacuous "no sequence of <= 0
  moves" line. The 9/47/211 run cited in Appendix A is not saved in `data/`.

### 16. §4.3 (lines 244-263): ACCEPT WITH FIXES
- Fix (lines 250-253): "from odd Φ the last step is a swap of a cycle color with a leftover color
  along a Λ-free chain of length ≡ 0 (mod 4)" is true for Φ = 3 under non-increasing sequences (the
  parity-changing move must land on Φ = 2). It is false from Φ = 5: see the three 5 → 4 → 2
  sequences in item 9 (`out/last_step.txt`). Say "some step", or restrict to Φ = 3.
- Fix (line 255): `data/escape2_M*.txt` gives 7/43 (16%), 3/46, 5/69 and 5/79 still stuck, so
  "5 to 15%" should read "6 to 16%". The lexicographic counts, 53 to 72 of 225 (`data/lex_M*.txt`:
  53, 68, 72), are correct. Neither was re-run independently.
- Fix (line 260): "E10 is necessary" should read "Lemma K can fail without E10 (B24)".
- The rest of §4.3 is a description of the open problem and needs no verdict. The "Lemma K
  restated" equivalence is item 10.

### 17-19. §5 bank (lines 265-278)
- Census bullet: ACCEPT WITH FIXES.
  - S6 for |B| = 16, 18 is in va6 PAPER §4 and was reproduced by the va6 referee. |B| = 12, 14 come
    from va6 REVIEW only. Cite both.
  - "Every B on 16, 18 or 20 vertices is E10" is va6 REVIEW, and Lemma 6.1 (non-E10 needs ≥ 22
    vertices) proves it.
  - The slice 0/600 and the 80 random graphs at 22 and 24 vertices were re-run by the va6 referee
    with independent code, so "one method each" understates those rows.
  - The 28/30 numbers match `va6/S6-RESULT.md` and SCOUT §7 (7,909 + 6,368 = 14,277 graphs;
    1,328,494 + 1,145,933 = 2,474,427 decisions).
- Conditional: ACCEPT. A 4-factor of Y with no edge cut of ≤ 2 edges is connected and has no 2-edge
  cut. |Y| = |B| − 2 ≤ 22, and |Y| ≥ 10. H22 (pairs SCOUT §2.3: connected bipartite 4-regular, no
  2-edge cut, n ≤ 22) then gives a Hamilton decomposition. H22 is a census: one method at 22
  vertices, two below (pairs REVIEW). 2EC_Y is an assumption, so this is a conditional with an open
  hypothesis, as the paper says.
- "Why the bank is not the target": ACCEPT WITH FIXES (line 277). The 350-vertex graph shows that
  "no 2-edge cut ⇒ HD" fails at 350 vertices. Between 24 and 348 vertices it is untested, not known
  to fail. Say "is not known to give ... beyond 22 vertices, and fails at 350".

### 20-26. §6, part (ii) (lines 280-361)
- Preamble: ACCEPT WITH FIXES.
  - (F0)-(F3) are correct.
  - Corollary B of `585-fable/PROOF-R1.md` (line 157 there) states the B6 ⟺ VA6 equivalence.
  - Cut types: |∂_I − ∂_O| = 6||T_I| − |T_O|| ≤ 8 forces the listed types. Connectivity excludes
    c = 0.
  - Line 284: N ≥ 22 uses VA6 at 12 and 14 vertices too (va6 REVIEW, trivial).
  - Line 288-289: "exactly when" should read "S6 gives B6 once such cuts are ruled out".
- Lemma 6.1: ACCEPT. δ = 0: k² − 6k + c/2 ≥ 0 gives k ≥ 3 + √(9 − c/2) > 5.2, the other root is
  < 0.77, and k ≥ 1. δ = 1: k² − 5k + (c − 6)/2 ≥ 0 gives k ≥ (5 + √(37 − 2c))/2 ≥ 4.79, and the
  other root is ≤ 0.21. The K_{6,5} example is right.
- Lemma 6.2: ACCEPT WITH FIXES. B[T] + z is simple, bipartite (z on the O side), 6-regular, and
  has |T| + 1 ≤ N − 1 vertices. VA6 at z gives a pair in B[T] ⊆ B − o. Fix: state the hypothesis
  "VA6 holds for all simple bipartite 6-regular graphs on fewer than |B| vertices", as va6 PAPER
  Lemma 1 does. The proof applies VA6 to the smaller graph B[T] + z, so it needs this hypothesis;
  the §6 preamble supplies it only through (F0). The same fix applies to Lemma 6.3.
- Lemma 6.3: ACCEPT WITH FIXES (hypothesis as above). The completion is simple (q_i distinct and
  not adjacent to p) and 6-regular. VA6 at p leaves B[T] − p. The k = 1 and k = 2 comparisons with
  va6 Lemma 1 are accurate.
- Lemma 6.4: ACCEPT. The count is c − d(v) + (6 − d(v)).
- Theorem 6.5: ACCEPT WITH FIXES. Every case was re-derived.
  - c = 2: va6 Cor. 2(a), with the va6 referee's parity fix, gives |T| ≥ 22.
  - c = 4: the paper's disjunction is equivalent to "not va6 Lemma 1 case 3 and not case 4", since
    2|T| ≥ N implies 3|T| ≥ N. Lemma 6.3 excludes more.
  - c ∈ {6, 8}: if d(v) ≥ 3, then (T − v, T̄ + v) has size ≤ c. It is essential (|T| ≥ 11 by
    Lemma 6.1) and o-free, with |T − v| < |T|, against the lexicographic choice. If d(v) = 6 and
    c = 6, the new cut is empty, against (F2). So d ≤ 2 on T. For (6,0), Lemma 6.2 forces a
    repeated end.
  - Fix (line 321): "a smallest counterexample to VA6 that is not E10" can be read as "smallest
    among non-E10 counterexamples", under which (F0) fails and so do the cited cases. Write "let
    (B, o) be a counterexample to VA6 with |B| minimum, and suppose B is not E10". That is how
    Corollary 6.6 uses it.
- Corollary 6.6: ACCEPT. A smallest counterexample is either E10, and then S6 gives a pair (F3), or
  it has a cut as in Theorem 6.5, which (R) excludes. "At least 22 vertices" follows from Lemma 6.1
  (24 if the cut is balanced).
- §6.1: ACCEPT WITH FIXES as discussion.
  - Line 343: "only if at most three cross edges survive" should read "if": (C) confines a pair
    when at most three survive, and is merely silent otherwise.
  - Line 359: "which S6 does not imply" should read "which S6 is not known to imply".
  - The VA6_f count (k − d(p) forbidden edges) is right.

### 27. §7 (lines 368-372): ACCEPT
- With s = g/2 − j − b (theory PAPER Lemma 1.1, accepted by its referee), s = 0 and ∂_P ≥ 1 give
  b − a − 2j ≥ 1, and 1.2(ii) gives j ≥ 2. So b = 5, a = 0, j = 2, g = 14, ∂_P = 1 and ∂_Q = 8. Only
  (ii) and (1.1) are used.
- ∂_B(S + y) = 14 + 6 − 10 = 10. Its I-part carries ∂_Q = 8 cut edges, and its O-part carries
  ∂_P + a + [oy] = 2. So it is a 10-edge cut of type (8,2) containing oy. Correct.

## Computations (rung (b), own code, under 10 CPU-minutes in all)
- `code/s6rev.py` holds the library, written from the paper's definitions: E10 by brute force (Gray
  code) and by flows between disjoint edge pairs, frames, legal Kempe swaps, re-pairings,
  Λ re-pairings, BFS escape, random hosts by edge switches, 4-factor by max flow and Kuhn
  matchings.
- `code/test_e10.py` validates the two E10 routines: they agree on 6 random 16-vertex hosts and
  find planted cuts of 6 (22 vertices), 2 (B24) and 8 (24 vertices).
- `code/cert.py` checks the certificates (items 13, 15), and `code/variants.py` gives the level
  counts under five conventions.
- `code/parity_check.py` (item 8), `code/b24_check.py` (item 12), `code/sample.py` with
  `run_sample.sh` and `run_big.sh` (item 14), `code/deep_check.py` (the H23 depth-4 frame) and
  `code/last_step.py` (items 9 and 16).
- Every command ran under `timeout 240`. Outputs are in `review/out/`.

## Summary for the coordinator

No REJECT. The mathematics is correct throughout: Lemmas 1.1-3.1, Theorem 4.1, Lemmas 6.1-6.4,
Theorem 6.5 and Corollary 6.6. Both refutations reproduce with independent code: ML-1 fails at
|B| = 16, and K3 fails at PG(2,5), which needs exactly 4 moves. The escape evidence reproduces in
kind: 9,988 minima from 25,232 frames, all escaping.

Fixes needed:
1. Framing of Theorem 4.1 (lines 19, 180-182, 405-408). Lemma K is a strengthening of S6
   (reachability of a Φ = 2 frame from every frame), not an easier statement. The reduction is a
   correct reformulation.
2. Example 4.3 and Appendix (lines 238-240, 396-397). The 211 depth-3 frames do have Φ-lowering
   moves (17 of them), so "none with a Φ-lowering move" holds only at depths 0-2. State that 9/47/211
   counts labeled frames. Delete "girth 6 is where the long sequences appear first": in
   H(Z_23, {3,5,9,13,17,20}), girth 4, a frame with Φ = 3 needs exactly 4 moves, with or without
   Λ re-pairings.
3. "The last merge" and "the last step" (lines 157, 188, 250-253) hold only for Φ = 3. In general
   some step, not necessarily the last, is the parity-changing swap. Three explicit 5 → 4 → 2
   sequences end with other moves (`review/out/last_step.txt`).
4. Line 255: "5 to 15%" should read "6 to 16%" per the paper's own data. Line 260: "E10 is
   necessary" should read "K can fail without E10".
5. (B2), lines 185-187: a frame is a 1-factorization of Y⁺, never the image of one of B. Lines
   160-162: "Λ-free Kempe 4-cycles"; define "merging move" in the paper rather than citing NOTES §A.
6. §6: state "VA6 below |B|" in Lemmas 6.2 and 6.3. Reword line 321 ("|B| minimum among all
   counterexamples, B not E10"), line 343 ("if", not "only if") and line 359 ("not known to imply").
7. Citations and wording: line 69 (R20 is pairs PAPER Ex. 4), lines 267-270 and 284 (12 and 14
   vertices from va6 REVIEW), line 277 (Meredith shows failure only at 350 vertices), and lines
   288-289 ("exactly when").
