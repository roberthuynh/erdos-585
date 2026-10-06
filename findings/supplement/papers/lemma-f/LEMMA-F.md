# Lemma F: statement, proof and review (verbatim excerpts)

Excerpt 1: the spectral report, section 4.5 (lines 322-342 of the source).

### 4.5 Lemma F: the Tutte / Gale-Ryser step works when pieces are near-regular (rung (a))
**Lemma F (bipartite, balanced).** Let H be bipartite with parts P, Q, |P| = |Q| = N/2, all degrees
in [(1-η)k, k], and e_H(Z, V(H) \ Z) >= γk|Z| for every Z with 1 <= |Z| <= N/2, where 0 < γ <= 1,
η <= γ^2/8 and k >= 16/γ^2. Put θ = (η + 2/k)/γ and k' = floor((1 - η - θ)k). Then H has a
spanning k'-regular subgraph F, k' >= (1 - 3γ/8)k - 1, and e_F(Z, V(F) \ Z) >= (γ/2)k'|Z| for every
|Z| <= N/2.

*Proof.* By max-flow min-cut (source to P with capacity k', unit edges, Q to sink with capacity
k'), H has a k'-factor iff k'|X| <= k'|Y| + e(X, Q \ Y) for all X ⊆ P and Y ⊆ Q. The condition is
self-complementary: for X' = Q \ Y and Y' = P \ X it reads k'|X'| <= k'|Y'| + e(X', P \ Y'), the
same condition with the sides swapped. So suppose (X, Y) violates it with Z = X ∪ Y of size at
most N/2 (otherwise use the complementary pair, whose union V(H) \ Z is smaller than N/2).
Violation gives k'(|X| - |Y|) > e(X, Q \ Y) >= 0, so |X| > |Y| and |Y| < |Z|/2. Degree counts give
e(X, Y) + e(X, Q \ Y) >= (1-η)k|X| and e(X, Y) + e(Y, P \ X) <= k|Y|. Hence
e(Y, P \ X) < (k - k')|Y| - ((1-η)k - k')|X| <= ((η+θ)k + 1)|Y| - θk|X|.
Non-negativity gives |X| - |Y| < ((ηk + 1)/(θk))|Y|, so e(X, Q \ Y) < k'(|X| - |Y|) <
((ηk + 1)/θ)|Y|; and, using |X| > |Y|, e(Y, P \ X) < (ηk + 1)|Y|. Adding,
e(Z, V \ Z) < (ηk + 1)(1 + 1/θ)|Y| < (η + 1/k)(1 + 1/θ)k|Z|/2 <= (η + 1/k + γ)k|Z|/2 < γk|Z|,
using (η + 1/k)/θ <= γ and η + 1/k <= 3γ^2/16 < γ. This contradicts expansion. For the bounds:
θ <= γ/4 because 2/k <= γ^2/8, so η + θ <= 3γ/8. Each vertex loses at most k - k' <= (3γ/8)k + 1
edges, so e_F(Z, V \ Z) >= (γ - 3γ/8 - 1/k)k|Z| >= (γ/2)k'|Z|. ∎

Excerpt 2: its independent review, item 2 and correction D6 (lines 19-20, 61-68 and 150-152 of the source).

2. Lemma F: **ACCEPT**. Every inequality checks, including the self-complementary flow condition.
   Two wording fixes about what it shows (D5, D6).

### Item 2: Lemma F
Checked each step: the max-flow condition k'|X| <= k'|Y| + e(X, Q \ Y) (uses |P| = |Q|); the
complement map (X, Y) -> (Q \ Y, P \ X) turns the condition into itself with sides swapped, so a
violator with |Z| <= N/2 exists; |X| > |Y|; the bound e(Y, P \ X) < ((η+θ)k + 1)|Y| − θk|X|
(using k − k' <= (η+θ)k + 1 and (1 − η)k − k' >= θk); |X| − |Y| < ((ηk+1)/(θk))|Y|; the sum
e(Z, V \ Z) < (η + 1/k + γ)k|Z|/2 < γk|Z| (using (η + 1/k)/θ <= γ and η + 1/k <= 3γ²/16); the
bounds θ <= γ/4 and η + θ <= 3γ/8; and the final expansion (5γ/8 − 1/k)k >= (γ/2)k', which needs
only k >= 8/γ. If Y is empty there is no violator, which the chain also shows. All correct.

**D6 (item 2, Section 0 item 2).** Lemma F's expansion is for |Z| <= N/2. In the BJ sense used by
Corollary 1.4 and Propositions A and C (sets up to 2N/3), the output is a (γ/4)-expander, not
(γ/2). *Fix:* say which sense, or state the BJ-sense constant.
