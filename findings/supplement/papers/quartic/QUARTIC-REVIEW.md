# Review: quartic-subgraph lane, theory claims (sections 5, 5.1, 6)

Status: **FINAL** (2026-10-04, 06:13 to 06:41)

**Overall verdict: ACCEPT WITH FIXES.** No mathematical defect found in Lemmas 1, 2, 4, Corollary 3,
Theorem 5 or the section 5.1 reductions. Theorem 5's 1 / 12 / 58 types were reproduced exactly by
independent code. Fixes are a citation (Lemma 1), one clause (Lemma 4), and a full statement of the
open sub-case (section 5.1). Corollary 3 is correct but follows at once from Petersen's 2-factor
theorem, so it should not be presented as new. P_2 remains open at exactly the stated sub-case.

Reviewed file: `lanes/quartic-subgraph/REPORT.md` (line numbers are from that file as of 06:12).
Review scripts and outputs: `reviews/quartic-review/`. The census (sections 3, 4) is out of scope.
Nothing in the lane folder was edited; its `geng_plain` binary and two data files were only read
or executed with output redirected here.

| item | claim | verdict |
|---|---|---|
| 1 | Lemma 1 (Tutte form), Lemma 2, Corollary 3 | ACCEPT WITH FIX (citation) |
| 2 | Lemma 4 (minimal counterexample) | ACCEPT WITH FIX (wording) |
| 3 | Theorem 5 (barrier types 1 / 12 / 58) | ACCEPT |
| 4 | Section 5.1 (bipartite reductions) | ACCEPT WITH FIX (state the sub-case in full) |
| 5 | Section 6 (F3, F4 spot checks) | ACCEPT |
| 6 | Literature for Corollary 3 | not found stated; immediate from Petersen 1891 (one-edge trick) |

## Item 1. Lemma 1 (and Lemmas 2, Corollary 3)

Algebra, confirmed by hand (short, as asked):
- Lemma 1 (REPORT.md lines 140-148): sum_T deg_{G-S} = sum_T deg - e(S,T) and f(T) = sum_T deg - 4|T|
  give delta = f(S) + 4|T| - e(S,T) - q. Parity: f(C) + e(C,T) ≡ sum_C deg + e(C,T) =
  2e(C) + e(C,S) + 2e(C,T) ≡ e(C,S). f(V) = 2e - 4n is even. Complement step: with min degree >= 4,
  0 <= f(v) = deg(v) - 4 <= deg(v), and F is an f-factor iff E(G) - E(F) is a spanning subgraph
  with every degree deg(v) - f(v) = 4. All correct.
- Lemma 2 (lines 157-174): (*), (**), 2(*) + (**), and the substitution of D_S all re-derived; the
  identity holds. w(C) >= 0 for odd C and the singleton value 12 - a - 3[a odd] >= 4 are correct.
  |S| > |T| from (**) is correct (e(S,R) - q >= 0).
- Corollary 3 (lines 178-184): D <= 2 forces every degree >= 4, 3 delta >= -2D >= -4, delta even,
  so delta >= 0. Correct. The sharpness example was rebuilt and checked by code
  (`quartic-review/spot_checks.py`): n = 13, e = 37, max degree 6, no spanning 4-factor (gadget
  matching), barrier S = {s0..s6}, T = {t1..t6} with delta = -2 (exactly the c = 2 type of
  Theorem 5), and K5,5 minus a perfect matching on {t1..t5, s1..s5} is a 4-regular subgraph.

Numerical check of Tutte's criterion in the stated form, with a decider that shares nothing with
the lane (`quartic-review/barrier_test.py`: Tutte's gadget, vertex v becomes deg(v) ports plus
deg(v) - 4 inner vertices, then networkx maximum matching): min over all 3^n pairs (S,T) of delta
>= 0 agreed with "has a spanning 4-factor" on all 60 graphs with D = 8 at n = 8, on 120 graphs with
D = 8 at n = 9 (113 with, 7 without), and on all 32 graphs with D = 6 at n = 8; the "no 4-factor
implies a barrier" direction also agreed on every 4-factor-free graph of items 3 below
(8 + 27 + 4 graphs). Every delta was even and every barrier had |S| > |T|.

Citation (read by the review in the original PDFs; quotes checked against the page text):
- W. T. Tutte, "A short proof of the factor theorem for finite graphs", Canad. J. Math. 6 (1954)
  347-352, doi:10.4153/CJM-1954-033-3. p. 348: "We denote by q(S, T) the number of components C of
  G_{S∪T} such that (3) v(C) + Σ_{a∈C} f(a) ≡ 1 (mod 2)", v(C) = number of edges from C to T;
  "THEOREM C. G is without an f-factor if and only if there is a subset S of V and a subset T of
  V − S such that (6) Σ_{a∈S} f(a) < q(S, T) + Σ_{c∈T} (f(c) − d_S(c))", d_S = degree in G − S.
  This is exactly "delta(S,T) < 0 for some disjoint S, T" with the lane's q.
- Parity: W. T. Tutte, "The factors of graphs", Canad. J. Math. 4 (1952) 314-328, Theorem I
  (p. 315; stated for his "recalcitrance" r(G,S), which translates to delta ≡ f(V) mod 2).
- Caveat: Tutte assumes f(a) is a positive integer (1954, p. 347), but f = deg - 4 is 0 at
  degree-4 vertices. A statement with nonnegative f, in the lane's form, is Z. Qu and D. B. West,
  "Another proof of the generalized Tutte-Berge formula for f-bounded subgraphs" (preprint, 2023,
  dwest.web.illinois.edu/pubs/btutgen.pdf), Theorem 1.1 (multigraphs, "nonnegative weight
  function f", "bad" components with f(Q) + ‖Q,T‖ odd, condition f(T) <= f(S) + d_{G-S}(T) - q(S,T))
  and Lemma 2.2 (Parity Lemma).
- Shorter route that avoids both the complement step and the f >= 0 issue: the k-factor criterion
  of Belck (1950) and Tutte, as stated in Kostochka, Raspaud, Toft, West, Zirlin, "Cut-edges and
  regular factors in regular graphs of odd degree", Graphs Combin. (2021),
  doi:10.1007/s00373-020-02242-0, Theorem 1.4: "A multigraph G has a ℓ-factor if and only if
  q(S,T) − d_{G−S}(T) ≤ ℓ(|S| − |T|) for all disjoint subsets S, T ⊂ V(G), where q(S,T) is the
  number of components Q of G−S−T such that ‖V(Q),T‖ + ℓ|V(Q)| is odd." With ℓ = 4 and the names
  S and T swapped this is word for word the lane's delta(S,T) = f(S) + 4|T| - e(S,T) - q with q
  counting components with e(C,S) odd.
- Not used: Akiyama-Kano (the theorem number could not be checked) and Lovász-Plummer,
  Bondy-Murty, Schrijver (not read).

Verdict: **ACCEPT WITH FIX** (citation only). Fix for line 141 and line 150: replace "Tutte 1952,
standard form" and "I did not re-read Tutte's 1952 paper" with Tutte 1954 Theorem C (p. 348)
plus Tutte 1952 Theorem I for parity, and either cite a nonnegative-f statement (Qu-West
Theorem 1.1) or, more simply, the 4-factor criterion (Kostochka et al. 2021, Theorem 1.4, from
Belck 1950) with S and T swapped. The mathematics of Lemmas 1, 2 and Corollary 3 is correct.

## Item 2. Lemma 4

Verdict: **ACCEPT WITH FIX** (wording of one clause; the mathematics is right).

Checked (REPORT.md lines 188-192):
- n >= 7: for c <= 4 the hypothesis needs n(n-1)/2 >= 3n - 4, which fails for n <= 5; for n = 6,
  e >= 14 means K6 or K6 minus an edge, both contain K5. Correct.
- min degree >= 4: deleting a vertex of degree <= 3 gives a smaller counterexample (n - 1 >= 6 >= 2,
  e - deg >= 3(n-1) - c). e = 3n - c: deleting an edge gives one with the same n and fewer edges.
  Both correct, so D = 2c.
- Sparsity: G[U] (proper, |U| >= 2) has max degree <= 6, no 4-regular subgraph and fewer vertices,
  so by minimality e(G[U]) <= 3|U| - c - 1; with 2e(U) = 6|U| - D_U - e(U, V-U) this is exactly
  D_U + e(U, V-U) >= 2c + 2. Correct.
- w bounds: for a component C with a = e(C,S), b = e(C,T), D_C + a + b is even and >= 2c + 2, and
  w = (D_C + a + b) + (D_C + b) - 3[a odd]. Even C: w >= 2c + 2. Odd C: D_C + b is odd, so
  w >= 2c + 2 + 1 - 3 = 2c. The stated ">= 2c - 1" is true but not sharp (w is even when a is odd,
  so the two bounds are equivalent). Not a defect.

Fix: line 191 says "every component C with |C| >= 2 of **any** G - S - T". For S = T = empty and G
connected, C = V is not a proper subset and the bound fails. It should read "of G - S - T for any
barrier (S,T)" (a barrier has |S| > |T| >= 0 by Lemma 2, so S is nonempty and every component is
proper). Theorem 5 only uses it for barriers, so nothing downstream changes.

## Item 3. Theorem 5

Verdict: **ACCEPT** (counts, properties and coverage reproduced independently).

Independent enumerator `quartic-review/types_indep.py`, written from scratch (it does not import or
copy `obstruction_types.py`). It does not search over the budget identity; it loops over the
components, D_T, e(T), e(S), takes D_S from the total D_S + D_T + sum D_C = 2c, computes s - t from
the difference of the S and T degree counts (6(s-t) = D_S - D_T + 2e(S) - 2e(T) + sum a - sum b,
must be an integer) and delta from Tutte's formula with e(S,T) eliminated
(delta = 2(s-t) - D_S + D_T + 2e(T) + sum b - q), and keeps delta <= -2. q is computed from the
textbook condition f(C) + e(C,T) odd (as D_C + b odd), not from e(C,S). The Lemma 2 identity is
asserted on every accepted tuple, and is used only to argue the loop bounds are not binding.

Results (`quartic-review/out_types_indep.txt`, `compare_lane.py`):
- c = 2: 1 type; c = 3: 12 types; c = 4: 58 types. Same counts as the lane.
- As sets of tuples (delta, s-t, e(S), e(T), D_T, D_S, multiset of (kind, D_C, e(C,S), e(C,T))),
  the review's lists are **equal** to the lane's `out/obstruction_types.txt` for c = 2, 3, 4.
- Doubling every search bound (`--loose=2`) gives the same 1 / 12 / 58; no accepted tuple
  touches a bound.

Stated properties for c = 4 (lines 205-210), checked on the review's own list (`props_c4.py`):
no violations. 1 <= s-t <= 3 (17 / 27 / 14 types); e(S) <= 5 (max 5); e(T) + D_T <= 2 (max 2);
e(S,T) >= 6|T| - 5, i.e. D_T + 2e(T) + sum e(C,T) <= 5 (max 5); D_S >= 5 (min 5); at most two
components (9 types with none, 29 with one singleton, 11 with two singletons, 9 with one piece);
a piece never occurs together with another component; each piece has w <= 10, e(C,S) >= 7 and
e(C,T) + D_C <= 3. delta = -2 in 53 types and -4 in 5.

Coverage:
- delta: not restricted by the review's enumerator (computed, then delta <= -2 kept). The identity
  3 delta + 2D = (sum of nonnegative terms) gives delta >= -16/3, so delta in {-2, -4} for c = 3, 4,
  and delta = -2 for c = 2. Both values occur.
- Singletons: every (a, b) with 4 <= a + b <= 6 is in the catalog. w = 12 - a - 3[a odd] is 12, 8,
  10, 6, 8, 4, 6 for a = 0..6, so with budget <= 10 every a in 1..6 can and does occur in the c = 4
  list (counts 3, 3, 15, 3, 22, 5); a = 0 is excluded by w = 12 > 10.
- Pieces (|C| >= 2), odd and even e(C,S): all (D_C, a, b) with D_C <= 2c, parity and sparsity are
  in the catalog. Odd pieces need w >= 2c = 8, even pieces w >= 2c + 2 = 10. The c = 4 list has odd
  pieces with e(C,S) in {7, 9, 11} and one even piece with e(C,S) = 10.
- Number of components: every component has w >= 4 (singleton) or w >= 2c (piece) and the total
  is <= 4c - 6, so at most 2 components for c = 4, 1 for c = 3, 0 for c = 2. The lane's cap of 3
  components is not binding.

Real-graph test of the sparsity-on list (`barrier_test.py`): the only use Theorem 5 makes of
Lemma 4 is the inequality D_C + e(C,S) + e(C,T) >= 2c + 2 for pieces of the barrier, so every
barrier of any graph with min degree >= 4, max degree <= 6, D = 2c whose pieces satisfy that
inequality must have a listed type. Results, with all 3^n pairs (S,T) scanned:
- D = 8, n = 9 (all 1157 graphs): 8 without a spanning 4-factor, 21 barriers (matches the lane's
  count), all 21 satisfy the piece inequality, all 21 in the 58.
- D = 8, n = 10 (all 35724 graphs): 27 without a spanning 4-factor, 96 barriers, all satisfy the
  piece inequality, all 96 in the 58. (The lane checked 4 of these 27 graphs.)
- D = 6, n = 8, 9, 10 (32 + 525 + 14314 graphs): 4 without (all at n = 10), 4 barriers, all in the 12.
- D = 4, n = 10 (3230 graphs): all have a spanning 4-factor; the n = 13 graph of Corollary 3 has the
  c = 2 type.

Constraints the enumeration relies on, and whether each is justified:
1. A barrier exists, delta <= -2 and even: Tutte's f-factor theorem with f = deg - 4 (Lemma 1),
   applicable because min degree >= 4. Justified (item 1).
2. q counts components with e(C,S) odd (equivalently D_C + e(C,T) odd): parity in Lemma 1. Justified.
3. D = 2c exactly: Lemma 4 (e = 3n - c). Justified.
4. Singletons: D_x = 6 - a - b and 4 <= a + b <= 6: all neighbors of x are in S u T; min degree
   >= 4 (Lemma 4) and max degree <= 6. Justified.
5. Pieces: D_C + a + b even (degree sum of C) and D_C + a + b >= 2c + 2 (Lemma 4 applied to U = C,
   proper because S is nonempty). Justified (with the item 2 wording fix).
6. D_C, D_T, D_S, e(S), e(T) >= 0 and D_S + D_T + sum D_C = 2c. Definitions.
7. s - t from (**) and D_S from (*) in the lane's code, equivalently the two degree counts in the
   review's code. Identities, justified.
8. Loop bounds in the lane's `obstruction_types.py`: delta in {-2,...,-8} with budget >= 0, at most
   3 components, piece e(C,S), e(C,T) <= 3 x budget, D_C <= 2c. None cuts off a solution: the
   budget (3 delta + 4c) is 2, 6, 0 or 10, 4 in the cases that occur; a piece has w >= a - 3 and
   w >= 2b - 3, so a <= budget + 3 <= 3 x budget when budget >= 2; and at budget 0 (c = 3,
   delta = -4) no piece passes sparsity (w <= 0 forces D_C + a + b <= 3 < 8). The lane's docstring
   does not state this; it is a documentation gap, not an error. (With sparsity off, as in the
   lane's cross-check, the budget-0 case could miss a piece with a = 1 and w = 0; that run used
   c = 4 only, where budget 0 does not occur.)
Not used (so the 58 is an upper bound on realizable types, which is all the theorem claims):
realizability in terms of |T| (for example D_S <= 2|S|), sparsity of sets other than the pieces,
and any constraint linking different barriers.

## Item 4. Section 5.1

Verdict: **ACCEPT WITH FIX** (all four reductions and the conclusion are correct; the open
sub-case and the piece classes should be stated in full, see the fix list at the end of this item).

**Bipartite criterion** (REPORT.md lines 232-233). Proof from max-flow min-cut: network s -> p
(capacity 4, p in P), p -> q (capacity 1 per edge pq), q -> t (capacity 4, q in Q). By integrality a
flow of value 4m is exactly a spanning subgraph with every degree 4. A cut with source side
{s} u A u (Q - C), A in P, C in Q, has capacity 4|P - A| + e(A, C) + 4|Q - C|, and every s-t cut
has this form. So max flow = 4m iff 4(m - |A|) + e(A,C) + 4(m - |C|) >= 4m for all A, C, which is
e(A,C) >= 4(|A| + |C| - m). Correct; it is also the bipartite case of Tutte's f-factor theorem.
Checked numerically (`quartic-review/bip_check.py`, `bip_check_big.py`): "min over (A,C) of the
slack >= 0" agreed with a networkx max-flow decider on 175 of 175 random balanced bipartite
graphs with m = 4..7 (126 without a 4-factor).

**Slack formula Φ** (lines 233-235). e(A,C) = (6|A| - D_A) - e(A,C') and
e(A,C') = 6|C'| - D_C' - e(A',C'), and 4(|A| + |C| - m) = 4(|A| - |C'|), so
Φ = 2|A| - 2|C'| - D_A + D_C' + e(A',C'). Φ >= 4(|C'| - |A|) because e(A,C) >= 0. A violation
therefore has k >= 1 and Φ = 2k - D_A + ε < 0, i.e. D_A >= 2k + 1 + ε. All correct; the formula
matched the definition on every (A, C') of the 175 random graphs.

**Pieces.** In B[A u C'] the C' side has deficiency D_C' + e(A',C') = ε and |A| = |C'| + k; in
B[A' u C] the A' side has deficiency D_A' + e(A',C') and |C| = |A'| + k. Correct.

**Reductions** (lines 238-248), re-derived by hand. Write P, Q for the sides of the balanced graph
and, in the C0 and C1 steps, P = Y - y0, Q = X, x1 = the degree-5 vertex of X when D_X = 1.
- E_3(m) <= C0(m'): D_A <= D_P <= 3 forces k = 1, ε = 0, D_A = 3, hence D_A' = 0 and
  e(A',C') = 0. Both pieces have X-side deficiency 0 and |Y| = |X| + 1: C0 instances of sizes |C'|
  and m - |A|, both < m. Both X-sides empty would need m = 1, which no E_3 graph has. Correct.
- E_4(m) <= C1(m'): k = 1 and ε <= 1; A' side deficiency D_A' + e(A',C') <= (4 - 3 - ε) + ε = 1.
  Correct.
- C0(m) <= E_3 and C1(m'): B - y0 is balanced with deficiency d0 on each side (d0 <= 5 because the
  average Y-degree is 6m/(m+1) < 6). d0 <= 3 gives E_3. Otherwise k = 1 or 2. For k = 1 the piece
  B[(X - C') u (Y - A)] is balanced (both sides m - |C'|) with deficiency 6 - D_A + ε <= 3 (using
  D_C'(B - y0) = e(y0, C')). For k = 2: D_A >= 5 + ε and D_A <= d0 <= 5 force d0 = 5, D_A = 5,
  ε = 0, and B[(X - C') u (Y - A)] has smaller side Y - A (it contains y0) with deficiency
  6 - 5 + 0 = 1 and |X - C'| = |Y - A| + 1: a C1 instance of size m - |C'| - 1 < m. Correct.
  Note: the E_3 piece can have the same size m (C' empty, or B - y0 itself); this is harmless
  because E_3(m) reduces to C0 at sizes < m, so the induction on m is well founded.
- C1(m) <= E_4 and C1(m'): D_X = 0 is the C0 step. For D_X = 1, D_Y = 7 and B - y0 has deficiency
  d = 1 + d0 on each side; d0 <= 3 gives E_4. Otherwise k = 1 gives the balanced piece
  B[(X - C') u (Y - A)] with deficiency 7 - D_A + ε - [x1 in C'] <= 4 (E_4). k = 2 gives
  D_A in {5 + ε, ..., 1 + d0} with ε <= 1, and the piece B[(X - C') u (Y - A)] has smaller side
  Y - A with deficiency 7 - D_A + ε - [x1 in C'], which is <= 1 (C1, size m - |C'| - 1) except when
  D_A = 5 + ε and x1 is not in C', where it is exactly 2. Correct, and this is exactly the stated
  exception.
These deficiency formulas were also checked mechanically (`bip_check.py`, `bip_check_big.py`): on
random C0 and C1 instances with m = 5..8, for every pair (A, C') of B - y0 with k in {1, 2}
(127,754 pairs, violations or not), the piece sizes and deficiencies equal the predicted
(6 + D_X) - D_A + ε - [x1 in C'] and ε. No mismatch.

**"P_2 holds if C1 holds"** (line 250): follows. By Theorem 5 (c = 2) a minimal counterexample is
B + one edge inside S with B bipartite, T-side all degree 6 and |S| = |T| + 1, i.e. B is a C0
instance with X = T; C0 is a subclass of C1; and the induction above proves C1(m) from C1 at
smaller sizes in every case but the sub-case. The bipartite census numbers (lines 252-260) were
not re-run (computational, outside the items); the inference from them ("C0 and C1 hold for
|X| <= 6", via the bipartite 4-core having e' - 3n' >= -4) is logically sound.

**Is the open sub-case stated precisely?** Nearly. Line 246-248 gives the right three conditions
but leaves the setting implicit and says "or" where both pieces occur. Fix: state it as
"B in C1(m) with D_X = 1 (x1 the degree-5 vertex of X), y0 in Y of minimum degree d0, and a
violation (A in Y - y0, C' in X) of B - y0 with k = |A| - |C'| = 2, D_A = 5 + ε (ε in {0, 1}, so
d0 >= 4 + ε) and x1 not in C'. Then B[(X - C') u (Y - A)] is a C_2 instance (X-side Y - A, which
contains y0, deficiency exactly 2, size m - |C'| - 1) **and** B[A u C'] has |A| = |C'| + 2 with
C'-side deficiency ε <= 1." Neither piece is covered by the classes C0, C1, E_3, E_4.

Fixes for section 5.1: (1) state the sub-case as above; (2) "(all sizes m' below are < m)" should
say that the E_3 and E_4 pieces may have size m, and the induction is well founded because
E_3(m), E_4(m) reduce to sizes < m.

**Optional: attempt to close the sub-case (time-boxed, not closed).** Partial progress,
with the identities checked on 20,112 pairs (A, C') with k = 2 of random C1 instances, m = 5..7
(`quartic-review/subcase_check.py`, 0 mismatches). In the sub-case, write P1 = B[(X - C') u (Y - A)]
(the C_2 piece, Y - A side deficiency 2) and P2 = B[A u C'].
- Exactly 7 edges join A and X - C': e(A, X - C') = 12 - D_A + ε = 7.
- If some a in A has e(a, X - C') >= 4, then P1 + a = B[(X - C') u (Y - A) u {a}] is balanced
  (size m - |C'|) with deficiency 2 + 6 - e(a, X - C') <= 4: an E_4 instance of size <= m, which
  has a 4-regular subgraph by the induction (E_4(m) reduces to C1 at sizes < m). This disposes of
  C' = empty (then |A| = 2 and the two vertices of A send 7 edges to X, so one sends >= 4).
- If some x in X - C' other than x1 has e(x, A) >= 4, or e(x1, A) >= 3, then
  P1 - x = B[(X - C' - x) u (Y - A)] is balanced (size m - |C'| - 1) with deficiency
  2 + e(x, Y - A) <= 4: E_4 at a smaller size. (Adding x to P2 instead gives a C1 instance only
  when e(x, A) >= 5 + ε, which is weaker.)
- What remains: the 7 edges between A and X - C' are spread so that every vertex of A sends at
  most 3 of them, every vertex of X - C' other than x1 receives at most 3, and x1 at most 2
  (so C' is nonempty, at least three vertices of A and at least three of X - C' meet these edges).
  Other small modifications checked (P2 minus one or two vertices of A, P2 plus two vertices of
  X - C', P1 plus two vertices of A) do not reduce to C0, C1, E_3 or E_4 in general. Closing this
  needs a new idea, for example a different choice of y0, or a stronger induction class that
  contains "|Y| = |X| + 2, D_X <= 1" (P2) and C_2 (P1).
- Structural fact that any closing argument can use: in a bad instance every violation of
  B - y0 must itself be of the sub-case type (a k = 1 violation gives an E_4 piece, a k = 2
  violation outside the sub-case gives a C1 piece), and the sub-case has Φ = 2k - D_A + ε = -1.
  So B - y0 has a subgraph with all degrees <= 4 that misses a 4-factor by exactly one edge
  (max-flow value 4m - 1), and the 7 edges between A and X - C' all lie in every such maximum
  flow. The same holds for every y in Y of minimum degree, and d0 >= 4 (d0 <= 3 gives E_4).

## Item 5. Section 6

Verdict: **ACCEPT** (both spot checks pass with explicit barriers verified by the review's code,
`quartic-review/spot_checks.py`; delta in the textbook form, no spanning 4-factor by gadget matching).
- K2 ∨ C5 (hubs 0, 1; pentagon 2..6; n = 7, e = 16, D = 10): S = pentagon, T = {0, 1}, R empty:
  delta = -2, |S| - |T| = 3, e(S) = 5, e(T) = 1, D_T = 0. This is family F3
  (-2, 3, 5, e(T) + D_T = 1, R empty). The barrier described in section 4 (lines 125-126:
  T = one hub, the other hub a single odd component) is also valid: delta = -2, s - t = 4,
  component (D = 0, e(C,S) = 5, e(C,T) = 1). Both exist; the table and the text name different
  barriers of the same graph, which is fine but could be said.
- `K?r@daMZq}Fw` (graph6 and the JSON edge list agree): T = {4, 5, 6, 7}, S = the other 8 vertices,
  R empty: delta = -2, |S| - |T| = 4, e(S) = 7, e(T) = 0, D_T = 0. Family F4. It is the only
  independent 4-set of degree-6 vertices.
- `K?`CRbt^d{Vo` (bonus): T = {8, 9, 10, 11}: the same parameters, family F4.
- Also confirmed: K2 ∨ C5 has no 4-regular subgraph at all (exhaustive over vertex subsets).
- Bonus (`quartic-review/families_all.py`, output `out_families_all.txt`): over barriers with R
  empty, the lane's 17 known graphs (`out/excess1_all17.g6`) and the two n = 12 graphs realize
  exactly the families the table assigns: n = 7 and the three n = 9 graphs F3; the two n = 8, the
  eleven n = 10 and the two n = 12 graphs F4. The probe counts in the table (t = 5, F3 at n = 11,
  13) were not re-run.

## Item 6. Literature

Verdict: **not found as a stated result in a short search, but it is an immediate special case
of Petersen's 2-factor theorem (1891)**. Corollary 3 is correct; it should not be presented as new.

Short derivation (review's check of the literature lane's argument): D = 6n - 2e is even and at
most 2. If D = 0, G is 6-regular. If D = 2, either two vertices u, v have degree 5 (add an edge
uv, parallel if uv is already an edge) or one vertex v has degree 4 (add a loop at v). The result
G' is a 6-regular multigraph. Petersen's theorem in the multigraph form (loops allowed, a loop
adds 2 to the degree) gives a 2-factor; removing it leaves a 4-regular multigraph, so G' splits
into three edge-disjoint 2-factors. The added edge or loop lies in exactly one of them, and the
other two are edge-disjoint 2-factors of G, whose union is a spanning 4-regular subgraph of G.
(The same trick fails at D = 4: two added elements can lie in two different 2-factors, which is
consistent with the n = 13 sharpness example.)

References checked:
- Petersen's theorem with loops and multiple edges, read by the review: J. van den Heuvel and
  B. Toft, "2-Factors in Graphs", arXiv:2510.11486v2 (7 May 2026): "we do allow multiple edges and
  loops" (p. 1); "a loop adds 2 to the degree of its vertex" (p. 2); "Theorem 1.2 (Petersen, 1891
  [18]). Let G be a 2r-regular graph, for some positive integer r. Then G has a 2-factor."
- Candidates the literature lane found that do not imply it (statements from abstracts or
  secondary sources, not read in full by the review): Katerinis, Discrete Math. 113 (1993)
  (k-regular, (k-1)-edge-connected, even order, delete k - m edges: m-factor; needs connectivity
  and simplicity of G + uv). Thomassen, J. Graph Theory 5 (1981), and Kano and Saito,
  Discrete Math. 47 (1983), are background leads whose original full statements have not
  been checked here. Withdraw the unverified assertions about which regular-factor cases
  those statements exclude; Alon, Friedland and Kalai, JCTB 37 (1984), Theorem 3.1 does apply at
  maximum degree 6: 3n - 1 edges force a nonempty 4-divisible subgraph and hence a nonempty
  quartic. That conclusion alone is not the spanning-factor conclusion under discussion.
  Results on regular
  host-graph leads (Bäbler, Belck, Gallai, Bollobás-Saito-Wormald, Niessen-Randerath) lack exact bibliographic identities in this paragraph; no theorem-scope or novelty clearance follows from that list.
- Recommendation: say in REPORT.md lines 176-179 that Corollary 3 also follows from Petersen's
  theorem by the one-edge (or loop) trick, and keep the Lemma 2 proof as the route that extends to
  the barrier analysis.

## Reproduction

All from `reviews/quartic-review/` (system python3 with networkx; no lane file is modified):
- `python3 types_indep.py 2 3 4 > out_types_indep.txt`; `python3 types_indep.py 4 --loose=2`;
  `python3 compare_lane.py`; `python3 props_c4.py` (item 3).
- `./run_small.sh` (items 1, 3: n = 8, 9 at D = 8; n = 8, 9, 10 at D = 6; n = 10 at D = 4;
  output `out_barrier_tests.txt`, about 80 s) and `./run_n10.sh` (n = 10 at D = 8, 35,724 graphs,
  output `res_n10_e26_chunks.txt`, a few minutes on two processes).
- `python3 bip_check.py 7`; `python3 bip_check_big.py`; `python3 subcase_check.py` (item 4).
- `python3 spot_checks.py > out_spot_checks.txt`; `python3 families_all.py` (items 1, 5).
- Literature PDFs were fetched to the session scratchpad and read with pdftotext; they are not
  stored in the repo.
