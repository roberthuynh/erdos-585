# BM review: bipartite Müyesser (lane bipartite-hamilton)

Reviewer: independent skeptical review, 2026-10-04. Status: FINAL.

Read: the lane's REPORT.md (all 699 lines) and every file in its checks/ folder. Sources fetched
independently with `curl -sL -A "openmath-review/1.0"`, then `pdftotext -layout`:
arXiv:2609.35766v1 (Müyesser, 13 pages, read in full) and arXiv:2605.15043v1 (Bradač-Janzer:
Definition 1.2, Theorem 1.3, Corollary 1.4, Definition 3.1, Lemma 3.3, the nearly-regular
definition, reference [19]). Reran combinatorics.py, controls.py and sampling.py from a scratch
copy (outputs match the report). Two new scratch scripts: `arith.py` (Section 6 inequalities at the
smallest admissible d) and `multi_check.py` (multi-edges in sampling.py). Scratch folder:
`[local scratch folder]`.

## Verdicts

1. Section 5.4 (Lemma B4.7): ACCEPT WITH FIX (one clarifying sentence, F3; no gap).
   Section 5.5 (Lemma Ch): ACCEPT.
   Section 6.3 (Part 2, Steps 1-9): ACCEPT (Step 5 counts, Step 6 entry and exit bound, Step 7 use
   of Lemma 5.1 on item graphs all verified; one harmless union-bound constant, F5).
2. δ^2 in place of δ^3 (U3), hence c = 5: ACCEPT. c = 6 also holds with nothing else changed.
3. Divisibility: the bipartite step (cherries): ACCEPT. [Omitted from this copy.]
4. Lemma B2.2: ACCEPT. Lemma R2: ACCEPT (its side hypothesis is necessary: otherwise the imbalance
   is exactly k).
5. Section 4 quotes: ACCEPT (every quote checked against the PDF text; every use within hypotheses).
6. Corollary BM-2: ACCEPT WITH FIX (constants for the c = 6 fallback are not stated, F2).

**Overall.** Theorem BM at c = 5: ACCEPT. I found no gap in the written proof. Theorem BM at c = 6:
ACCEPT (weaker statement, same proof with k := c1 δ^3 qn/L^2). Theorem BM-γ at c' = 10 and
Corollary BM-2: ACCEPT, with F2 for the fallback constants. Rung (a), single independent review.
Residual trust sits in cited results that neither the lane nor I re-derived: Haxell's theorem (as
stated in Asadpour-Feige-Saberi), the Alon-Hoory-Linial Moore bound, Tropp's matrix Bernstein,
the hypergeometric Chernoff bounds, and BJ Lemma 3.3 (from [19], Draganić-Methuku-Munhá
Correia-Sudakov). All are standard.

## Defects and fixes

- **F1 (wording).** [Omitted from this copy.]
- **F2 (constants; Section 0 item 3, Section 8, Section 11).** The constants 33 C_BM and
  2^11 C_γ assume c = 5 and c' = 10. Under the c = 6 fallback, (a) needs
  d >= 65 C_BM δ^-6 (log n)^3, since (δ/2)^-6 = 64 δ^-6, and (b) needs
  d >= 2^13 C_γ γ^-12 (log n)^3, where C_γ itself becomes 32^6 C_BM. State both versions wherever
  the fallback is mentioned.
- **F3 (Lemma B4.7, template wiring).** A merged connection (v_(1,k) to a row-3 point when k is
  odd; a row-2 point to v_(4,1), or to v_(4,k) when k is even) matches Definition 4.3's "edge plus
  path" only if it has length at least 2. Add one sentence. Lemma 3.1's paths always have an
  interior vertex, since its proof builds them as a_i x ... y b_i with x, y in K. In any case,
  contracting a degree-2 non-terminal vertex preserves the router property (R0 read backwards).
- **F4 (checks; Section 0 item 5 and Section 9).** (i) "40/40 proper 2-colorings" holds by
  construction: `connect()` in router_embed2.py picks each path's parity from the coloring. Only
  "balanced" and "router" are tests. (ii) `two_block()` in sampling.py sums random permutation
  matrices with `np.add.at`, which creates repeated edges. Each test matrix has 2017 to 2839
  entries >= 2, with multiplicity up to 5 (multi_check.py). Those are multigraphs, outside Lemma
  B2.2 (its Step 4 uses W_ij^2 = W_ij). Fix: say so, or reject permutations that hit an existing
  edge. Not load-bearing.
- **F5 (trivial; Section 6.2 (P2)).** The union bound gives about 2n^-2, not n^-2: 2n^-4 per
  (vertex, set), with up to n^2 such pairs. The total failure probability is still below 1.
- **F6 (recommendation; U3).** The δ^2 argument applies verbatim to Müyesser's non-bipartite
  Theorem 1.3, giving d >= C δ^-5 (log n)^3 there too, and ε^-10 γ^-10 in his Corollary 1.4.
  The report should say so in U3, so readers see the full reach of the claim. Before any outside
  mention, a third reader should check it: it is a claim about someone else's preprint.
- **F7 (trivial; Section 1 typo list).** Two more harmless typos in Müyesser: p. 12,
  "Let P := V(G) \ V(S) ∪ C1 ∪ ... ∪ Ct" means V(G) \ (V(S) ∪ C1 ∪ ... ∪ Ct); and Lemma 3.1's
  "|P_i| <= Cγ log(2|R|)" should read Cγ^-1 log(2|R|), since the proof uses ℓ = C0 γ^-1 log(2|R|).

## 1. Sections 5.4, 5.5 and 6.3, line by line

**Lemma B4.7 against Müyesser's Lemma 4.7 (p. 9-10).** Same skeleton: split R into C, U, V;
concentration; Lemma 2.1 for cut-density of J; Lemma 4.6 for cycles in H[C]; Lemma 4.5 for
comparators; one application of Lemma 3.1 for every connection. The one structural change is
side-by-side sampling. That makes H[U ∪ V] = H[U, V] exactly. (In the non-bipartite original,
Lemma 3.1 is applied to J = H[U, V] even though H[U ∪ V] has more edges. That is harmless there:
apply the lemma to H minus the edges inside U and inside V.) Checked:
- s' >= σδ^2 qN/(2L) and s' <= qN/100, because σδ^2 qN/L >= σ K_R L = 4·10^5 L. Hence
  D0 in [0.99qd, qd], D_C in [σδ^2 qd/(2L), σδ^2 qd/L], and D_C >= 2·10^5 L.
- E1 is B2.2 with a = 2 (needs D0 >= 192 δ^-2 L). E2: the tail 2exp(-δ^2 D0/(3·10^4)) needs
  D0 >= 9·10^4 δ^-2 L. E3 needs D_C >= 900L. All hold. U and V are uniform m0-subsets of P and Q,
  independent, so B2.2 applies. The g(R) averaging step is the right way to get a statement about
  R alone.
- δ(J) - λ2(J) >= 0.49 δ D0, so ρ|V(J)| >= 0.49 δ D0 >= (δ/3)(1.01 D0) >= γΔ(J) with γ = δ/3.
- H[C] = H[C_P, C_Q] has degrees in [0.9 D_C, 1.1 D_C]. Lemma 4.6 with D = 0.9 D_C >= 100 gives
  at least σδ^2|R|/(200L^2) >= k disjoint even cycles of length at most 3L (needs c_R <= σ/200;
  c_R = σ/400).
- Pair list: I traced k = 2, k odd and k even, including the boundary columns. Every vertex of
  A ∪ B and of every used cycle is an end of exactly one pair, and no end lies in U ∪ V.
- Lemma 3.1 with β = 1/4 and γ = δ/3. A ∪ B ends: d(x, U ∪ V) >= qd/2 - 1.1 D_C >= qd/3 >=
  1.01qd/4 >= Δ(J)/4. Cycle ends: d(x, U ∪ V) >= 0.99 D0 >= Δ(J)/4. Reservoir vertices:
  d(v, T) <= 1.1 D_C + c_R δ^2 qd/L <= δ^2 qd/(250 C_L L), below the required
  δ^2 qd/(74 C_L L). (The lane uses log(2|U ∪ V|) <= 2L where <= L already holds.)
- Paths have interiors in U ∪ V and pairwise distinct ends, so they share no vertices or edges.
  Lemma 4.5 allows any pairing lengths. R1 handles the A and B ends and R0 the column connections.
  R0 and R1 are correct. The lane's proof of Proposition 4.4 is correct: right-multiplying by
  (i i+1) when i and i+1 are in different cycles merges them, the merges persist, and the
  transpositions chosen in one phase are disjoint.

**Lemma Ch (5.5).** Correct. After j < r cherries, with U_j the 3j used vertices, there are at
least θ|F_Q \ U_j| - 2jd edges between F_Q \ U_j and F_P \ U_j. Since
j(θ - 1 + 2d) < 3rd <= (θ - 1)|F_Q| (using θ <= d), that number exceeds |F_Q \ U_j|, so some
center has two free neighbors.

**Section 6.3 against Müyesser's Part 2 (p. 12).**
- Step 1. d(x, R) = d(x, R_Q) >= 0.9qd. d(v, A ∪ B) <= (1 + η)D + 12qD <= 2D <=
  4c1 δ^2 qd/L^2 <= c_R δ^2 qd/L. k <= c_R δ^2 |R|/L^2. All three hypotheses of B4.7 hold.
- Step 2. V(S) ∩ P ⊆ A ∪ R_P, so N - qN - k <= M <= N - k. R2 applies, since A ⊆ P and B ⊆ Q.
- Step 3. T' - τ >= (qN - 2qk)/((1 - 2q)k) - 1 >= qN/(2k), and T' - τ <= Nh/(mk) + 1 <= 7qN/k,
  and τ >= N/(2k). Correct.
- Step 4. θ = qd/5, and (θ - 1)|F_Q| >= q^2 Nd/40 >= 3rd uses c1 <= c0/480
  (10^-8 <= 2.08·10^-8). Correct.
- **Step 5 counts: correct.** |P \ V(S)| = |Q \ V(S)| = M = τk + r. On the P side, M - τm vertices
  lie outside the used odd layers, and the 2r cherry ends among them become r super-vertices, so
  |W_P| = M - τm - r = τh. On the Q side, removing the used even layers and the r centers gives
  |W_Q| = τh. Super-vertices occur only on the P side; W_Q is all ordinary.
- **Step 6 bound: correct, with contracted vertices counted through each end.** Distinct items
  have distinct entries and distinct exits, since x_j and x'_j leave the ordinary items. So for each
  sign, #{z : v ~ z^±} <= d(v, Π). Π lies inside (R \ V(S)) ∪ Z_P ∪ Z_Q ∪ (spare layers), so
  d(v, Π) <= 1.1qd + 2D + 7.07qd <= 9qd. X_i is a uniform h-subset of τh items, so the mean is
  at most 9qd/τ <= 18qdk/N <= 36qD. The tail is e^(-12qD) <= n^-1200, and 72qD < αD/20. Both
  counts are needed (the X side of Lemma 5.1 uses exits towards R0, the Y side uses entries towards
  L0), and both are bounded. A super-vertex in X_i meets the exit condition in pair
  (L_i, L_(i+1)) and the entry condition in pair (L_(i-1), L_i), each through the correct end.
- **Step 7, Lemma 5.1 on item graphs: correct.** In each of the 2τ + 1 auxiliary graphs, the base
  graph is exactly H0 = G[base, base], because base items are ordinary. H0 has degrees (1 ± η)D
  by (P2a), and λ2 <= (1 - δ/2)D by (P1): the needed pairs (B0, C1), (C_i, C_(i+1)) and
  (C_(2τ), A0) are all in the list. Lemma 2.1 gives cut-density 0.245 δD/m >= αD/m, with
  α = δ/10 and η = α/10. Perturbation items have at least (1 - η)D base neighbors through the
  right end. Base vertices have at most 72qD (by (*)) or 12qD (by (P2d)) perturbation neighbors.
  Lemma 5.1 is a statement about an abstract bipartite H containing H0, so applying it to item
  graphs is legitimate. I re-derived Lemma 5.1's proof; it is correct.
- Steps 8-9. The matchings compose into k disjoint B-to-A item sequences. Expanding w_j into
  x_j y_j x'_j gives G-paths with sides alternating correctly. Their internal vertices are exactly
  V(G) \ V(S), and Proposition 4.2 closes the cycle. Correct.
- Arithmetic stress test (arith.py). At the smallest admissible d, with δ in {0.5, 0.1, 0.01},
  C_L in {10^3, 10^6}, n in {10^60, 10^120}, and M at both extremes, every inequality in Sections
  6.0 to 6.3 holds.

Müyesser's own Part 2 is looser at the same points: "d_G(v, P) = O(qd)" and d_G(v, X_i) <= 10qD
are asserted without the accounting, and super-vertices do not arise. The lane's version is more
careful than the source.

## 2. δ^2 versus δ^3 (U3)

**ACCEPT: c = 5 holds.** Müyesser's Lemma 4.7 assumes δ^3 twice (p. 9:
"dH(v, A ∪ B) <= c δ^3 qd/log n" and "k <= cδ^3 |R|(log n)^-2"). His proof never uses the third
power:
- Cycles (p. 10): "Since k <= cδ^3 qn log^-2 n and |C| = Θ(δ^2 qn/log n), choosing c sufficiently
  small ensures that there are at least k such cycles." The count is c1|C|/log n =
  Θ(δ^2 qn/L^2), so k <= cδ^2|R|/L^2 suffices.
- Degrees (p. 10): "dH(v, T) <= 2DC + cδ^3 qd/log n ... at most c2 δ^2 qd/log n ... precisely the
  condition required in Lemma 3.1 with ... γ = Θ(δ)." Lemma 3.1 needs βγ^2 Δ/(C log) =
  Θ(δ^2 qd/L), so a bound cδ^2 qd/L on d(v, A ∪ B) suffices.
- qd >= Kδ^-4 L^2: the proof only needs D_C = Θ(δ^2 qd/L) >= CL and D0 >= Cδ^-2 L, that is
  qd >= Cδ^-2 L^2.
- Lemma 3.1's proof has no further δ dependence. I re-read Claim 1: |I| <= 5γ^2|R|/(C log),
  |U| <= 10 C0 γ|R|/C, |W| <= 6|U|/γ, and a final contradiction 140C0/C < 1.

In the main proof, the binding constraint is the layer subsampling bound D >= Cδ^-2 L, with
D = Θ(kd/n) = Θ(δ^e q d/L^2), where e is the power of δ in k. Since q = Θ(δ) (forced by Lemma
5.1's slack α = δ/10), this gives d >= Cδ^-(e+3) L^3: e = 3 gives 6 and e = 2 gives 5. Every other
constraint is weaker: the (P2a) tails need the same D bound; qD >= CL; qd >= K_R δ^-2 L^2; and
Step 4 needs only c1 << c0. Fallback: with k := c1 δ^3 qn/L^2, every Section 6 inequality still
holds (Steps 1 and 4 get easier) and d >= Cδ^-6 L^3 results. So c = 6 holds with nothing else
changed. Minor wording point: "Müyesser's Lemma 4.7 exactly as stated" cannot be applied to a
bipartite host, since it assumes an (n, d, λ)-graph. It means "Lemma B4.7 with δ^3 in place of
δ^2". See F6 for the non-bipartite consequence.

## 3. Divisibility

[Omitted from this copy.]

**The bipartite step.**
- Verified in item 1 (Steps 3 to 8). Contracting a P-Q-P cherry removes one vertex
  from each side, so the balance from Lemma R2 is kept.

## 4. Lemma B2.2 and Lemma R2

**Lemma B2.2: ACCEPT.** I re-derived every step.
- Step 1. From B1 = 0, 1^T B = 0, W^T W = (d^2/N)11^T + B^T B and ||W|| <= d, we get
  s2(W) = ||B||. Also λ2(G) = s2(W), since spec(A_G) = {±s_i(W)}.
- Step 2. Each row and column of B has squared norm d - d^2/N.
- Step 3. Lemma 2.4 applies to F = B^T with r = s = N.
- Step 4. ||B[U, {j}]||^2 = d(j, U)(1 - 2d/N) + m d^2/N^2 <= d(j, U) + D.
- Step 5. V is independent of U and uniform on Q, so Lemma 2.4 applies with q = p. This is why
  the bipartite version is cleaner: Müyesser's V is uniform on [n] \ U, with proportion p/(1 - p).
- Step 6. (1 + √3)/√32 = 0.483 < 1/2.
- Step 7. (2N^2 + 3N) n^-(a+4) <= n^-a.

Dropping p <= δ/100 is justified: that hypothesis only fed (1 - p)^(-1/2) <= 1 + p in Müyesser's
(10).

Sharpness: a D-threshold of order δ^-2 cannot be removed. In a two-block host with
s2 = (1 - δ)d, the sampled s2 is about (1 - δ)D plus fluctuations of order √D, and those must
stay below δD/2. The log n factor is the union-bound cost. The lane's numerics show the failure
at small D (D = 12, δ = 0.1 gives 1.01 > 0.95), on multigraphs (F4).

**Lemma R2: ACCEPT.** Every edge of the Hamilton cycle E(P_φ) ∪ M_φ joins P to Q, so the cycle
alternates sides. The hypothesis is necessary: with A, B ⊆ P, each of the k paths of P_φ has one
extra P vertex, so the imbalance is exactly k. I reproduced the controls.py result (10/10 runs,
imbalance exactly k). The use in Step 2 is within hypotheses.

## 5. Section 4 spot-checks (against the PDF text)

All correct:
- Lemma 2.1 (p. 3). The lane's Laplacian and Weyl proof is right.
- Lemma 2.2's hypotheses (p. 3): p <= δ/100; D >= Ca δ^-2 log n with Ca = 30000(a + 4);
  "ordered pairs of disjoint m-subsets of V(G)".
- Theorem 2.3 and Lemma 2.4 (p. 3-4): c = max ||f_j||_2, not squared; bound r(s + 1)e^-t.
- Lemma 3.1 (p. 5). The lane omits |R| >= 3 and the path-length conclusion; neither is used. The
  use in B4.7 is within hypotheses (β = 1/4, γ = δ/3, multiplicity 1).
- Definition 4.1, Proposition 4.2, Definition 4.3 and Proposition 4.4 (p. 7).
- Lemma 4.5 (p. 8): pairing {c_(2j+1) c_(2j+4) : 1 <= j <= r - 3} ∪ {c_(2r-3) c_(2r-1)} with
  g = 2r. The M0 typo reading is confirmed by the paper's own next sentences: M1 "pairs c1 with
  c2", and "M0 ∪ P has a path connecting c0 and c1". I reran the g <= 600 and k <= 9 checks.
- Lemma 4.6 (p. 9). Used with D = 0.9 D_C >= 100 and Δ <= 2D.
- Lemma 4.7's hypotheses (p. 9): q <= δ/100; qn ∈ 2N; qd >= Kδ^-4 (log n)^2; δ^3 twice.
- Lemma 5.1 (p. 10-11). Proof re-derived.
- The main-proof quotes (p. 11-12), including the "log log n" typo.
- BJ: Definition 1.2 (|S| <= 2n/3, average degree); Theorem 1.3 ((γ^-1 log n)^(10^8));
  Corollary 1.4 ("λ2(G) = (1 - δ)d", (3δ^-1 log n)^(10^8)); Lemma 3.3 (λ2(N(G)) <= 1 - γ^2/32
  for (d ± d')-nearly regular, d' <= d/4); N(G) = D^(1/2) A D^(1/2) with D_ii = 1/d_G(i);
  [19] = Draganić-Methuku-Munhá Correia-Sudakov.

## 6. Corollary BM-2

- λ2(G - E(H1)) <= λ2(G) + 2: correct. The all-ones vector 1 is the top eigenvector of both A(G)
  and A(G'), so λ2(G') is the maximum Rayleigh quotient over x ⊥ 1. Also -x^T A(H1) x <= 2||x||^2,
  since the smallest eigenvalue of an even cycle is -2. (Weyl's inequality gives the same in one
  line.) This step does not use bipartiteness; bipartiteness keeps G' inside Theorem BM's class.
- δ/2 arithmetic: correct. (1 - δ)d + 2 <= (1 - δ/2)(d - 2) iff d >= (8 - 2δ)/δ. Also
  d - 2 >= 32 C_BM δ^-5 L^3 = C_BM (δ/2)^-5 L^3, given C_BM δ^-5 L^3 >= 2.
- (b): correct. e_G'(S, V \ S) >= (γd - 2)|S| >= (γ/2)(d - 2)|S| when γd >= 4, and
  d - 2 >= 2^10 C_γ γ^-10 L^3 = C_γ (γ/2)^-10 L^3. BJ (p. 4) make the same remark about removing
  Hamilton cycles from far-from-bipartite expanders.
- Fix: F2 (fallback constants).
