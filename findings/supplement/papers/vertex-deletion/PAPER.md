# V110: balanced deletion at the local BM scale

Current publication status: Proposition V110 and its corollaries are conditional reductions using the unverified main BM/BM-2 input. The dated text and review record below do not establish that input. They do not certify an unconditional Hamiltonicity theorem or a project `check.sh` PASS.

Date: 2026-10-04. Author status: complete and frozen after independent mathematical review; source wording and reference corrections applied.

This is a complete paper derivation from the existing local Lemma F and BM-2. Both are paper inputs, and BM is an unpublished adaptation with a positive manual review. Neither F, BM, nor this derivation has a project `check.sh` PASS. No Lean was written or run. The appropriate scope is a subclass bound, intended rung (b), with a written proof of the implication. It is not a degree-six theorem, a general growth improvement, or a historical novelty claim.

## Decision

V110 closes with one candidate and no repair. At the local BM degree scale, one can delete any prescribed vertex and still find a faithful pair. More generally, arbitrary deletion of at most `floor(gamma^2 r / 32)` vertices from each side, with equal numbers deleted, leaves two edge-disjoint Hamilton cycles on the entire remainder. The proof uses only deletion, an actual spanning factor, and the local BM-2 theorem.

Recommend retaining this as an exact resilience corollary and stopping this scout. It fills the prescribed-vertex inference on this growing-degree expander class. It provides no extraction theorem for arbitrary avoiders, and it does not transfer Fable R1's degree-six equivalence to a class of expanders.

## 1. Notation and paper inputs

All graphs here are finite, undirected, and simple. `N` always denotes the **original total number of vertices**, not the size of a bipartition side. Logarithms are natural. Write `Pair(G)` for two simple cycles with disjoint edge sets and exactly the same nonempty full vertex support, possibly a proper subset of `V(G)`.

A regular graph of degree `r` is a **BJ gamma-expander** when

    e_G(S, V(G) \ S) >= gamma r |S|  for 1 <= |S| <= 2N/3.

A **half-order cut bound** instead restricts to `|S| <= N/2`. We keep these conventions separate.

We import the following existing local statements, without re-proving either.

**F.** A balanced bipartite graph H of order h with degrees in `[(1-eta)k,k]` and

    e_H(S,V(H)\S) >= alpha k |S|  for 1 <= |S| <= h/2,

where `0 < alpha <= 1`, `0 <= eta <= alpha^2/8`, and `k >= 16/alpha^2`, has a spanning d-regular factor F, where

    theta = (eta + 2/k)/alpha,
    d = floor((1-eta-theta)k),
    d >= (1-3alpha/8)k - 1,
    e_F(S,V(F)\S) >= (alpha/2)d|S|  for 1 <= |S| <= h/2.

Source: [spectral report, Section 4.5](../lemma-f/LEMMA-F.md), with [independent review, Item 2 and correction D6](../lemma-f/LEMMA-F.md). In particular, its last cut bound has BJ parameter `alpha/4`, not `alpha/2`.

**BM-2.** There is an absolute `C_BM`, which we may enlarge to satisfy `C_BM >= 1`. Set

    C_gamma = 32^5 C_BM.

For any `0 < beta <= 1`, a bipartite d-regular BJ beta-expander F on `h >= 4` vertices has two edge-disjoint Hamilton cycles whenever

    d >= 2^11 C_gamma beta^-10 (log h)^3.

Here `C_gamma` is the fixed absolute constant in the local theorem, not a function of the expansion parameter. Source: [BM report, Section 2 and Section 8(b)](../bipartite-hamilton/REPORT.md), with [independent BM review, Section 6](../bipartite-hamilton/BM-REVIEW.md). This is the reviewed exponent-five spectral route, hence exponent ten in cut expansion. We make no claim to have re-audited BM's proof.

## 2. Quantified proposition

**Proposition V110 (paper consequence of F and BM-2).** Put

    C_V = 2^42 C_gamma = 2^67 C_BM.

Let G be a simple bipartite r-regular BJ gamma-expander on `N >= 4` vertices, where `0 < gamma <= 1`. Suppose

    r >= C_V gamma^-10 (log(2N))^3.                         (V1)

Its bipartition has equal sides A and B. For **every** pair of deletion sets `D_A subset A` and `D_B subset B` and integer `t >= 0` with

    |D_A| = |D_B| = t <= floor(gamma^2 r / 32),             (V2)

the induced remainder

    H = G[V(G) \ (D_A union D_B)]

contains two edge-disjoint Hamilton cycles. Thus these cycles give a faithful pair in G whose common full support is exactly

    V(G) \ (D_A union D_B).

All constants above are sufficient and deliberately unoptimized. The absolute BM constant remains the paper input; this is an explicit constant multiplier, not a claim to a numerically evaluated BM constant.

### Proof

**1. Balance and nonempty remainder.** Since `r > 0`, counting edges from the two bipartition sides gives `r|A| = r|B|`. Hence `|A|=|B|=N/2`. Simplicity implies `r <= N/2`.

Let `h=N-2t`. Condition (V1), `C_BM >= 1`, `gamma <= 1`, and `log(2N)>1` imply

    r >= 64 gamma^-2 >= 64.                               (V3)

Also (V2) gives `t <= r/32`. Each remaining side therefore has size at least

    N/2 - t >= r - r/32 = 31r/32 >= 62.

In particular `h >= 4`, and H is balanced. This explicitly rules out an empty or undersized support.

**2. Degree loss and half-order expansion.** Each surviving vertex has at most t neighbors in the deleted opposite side. This uses simplicity and the equal sidewise deletion bound, not the total deletion size `2t`. Therefore

    r-t <= d_H(v) <= r  for every v in V(H).               (V4)

For every nonempty `Z subset V(H)` with `|Z| <= h/2`, we have `|Z| <= N/2 <= 2N/3`. Write `D=D_A union D_B`. The exact cut identity is

    e_H(Z,V(H)\Z) = e_G(Z,V(G)\Z) - e_G(Z,D).

The first term is at least `gamma r|Z|`, and the second is at most `t|Z|`. Hence

    e_H(Z,V(H)\Z)
      >= (gamma r-t)|Z|
      >= (gamma-gamma^2/32)r|Z|
      >= (gamma/2)r|Z|.                                  (V5)

The bound uses the original degree r as its denominator. We do not silently treat H as regular or replace its degree by its average.

**3. Apply the existing factor lemma.** Set

    k=r,  eta=t/r,  alpha=gamma/2.

H has equal sides, (V4) gives its required degree interval, and (V5) gives its half-order cut bound. Conditions (V2) and (V3) give exactly

    eta <= gamma^2/32 = alpha^2/8,
    k = r >= 64/gamma^2 = 16/alpha^2.

Thus F supplies an actual spanning d-regular factor of H with

    d = floor(r-t-2(t+2)/gamma),
    d >= (1-3gamma/16)r - 1
      >= 13r/16 - 1
      >= r/2,                                            (V6)

where the last inequality follows already from `r >= 64`. Its retained half-order expansion is

    e_F(Z,V(F)\Z) >= (gamma/4)d|Z|  for 1 <= |Z| <= h/2.  (V7)

The factor is a subgraph, not a regular completion with added edges. In particular `E(F) subset E(H) subset E(G)`.

**4. Convert the expansion convention.** Let `1 <= |Z| <= 2h/3`. If `|Z| <= h/2`, (V7) is stronger than the required `(gamma/8)d|Z|` bound. Otherwise let `W=V(F)\Z`. Then

    1 <= |W| < h/2,  |W| >= |Z|/2,
    e_F(Z,W) = e_F(W,Z)
              >= (gamma/4)d|W|
              >= (gamma/8)d|Z|.

Consequently F is a BJ `(gamma/8)`-expander. This factor of two is essential when passing from half-order to the two-thirds convention.

**5. Apply BM-2 and check its constants.** By (V1) and (V6),

    d >= r/2
      >= 2^41 C_gamma gamma^-10 (log(2N))^3
       = 2^11 C_gamma (gamma/8)^-10 (log(2N))^3
      >= 2^11 C_gamma (gamma/8)^-10 (log h)^3,

since `4 <= h <= N < 2N`. We have `0 < gamma/8 <= 1` and the required bipartite regular host. BM-2 therefore gives two edge-disjoint Hamilton cycles in F.

Each cycle visits every vertex of F exactly once, so both full supports equal `V(F)=V(H)`. Their edge sets are disjoint subsets of the original edge set of G. Thus they form the asserted faithful pair with no projection, completion, or lifting step. This proves the proposition. ∎

## 3. Prescribed vertices and arbitrary forbidden sets

**Corollary V110.1.** Under (V1), for every prescribed vertex v and every vertex u in the opposite bipartition side, G contains a pair with common support exactly `V(G)\{v,u}`. In particular `Pair(G-v)` holds.

Indeed, (V3) ensures `gamma^2 r/32 >= 2`, so the proposition applies with `t=1`. Deleting u balances the sides. The conclusion is a pair contained in `G-v`; it is not a spanning pair on `G-v`, whose sides are unequal.

The same argument gives a slightly more general way to state the budget. Let `b=floor(gamma^2 r/32)` and let W be any prescribed forbidden set with

    max(|W intersect A|, |W intersect B|) <= b.

Set `t=max(|W intersect A|,|W intersect B|)` and enlarge the smaller sidewise deletion set to size t. This is possible because `b <= r/32 <= N/64`. Applying V110 gives a pair in `G-W` on a support of size `N-2t`. When W is balanced, the pair spans all of `G-W`. This is the same deletion argument, not a second candidate.

## 4. What the combination establishes

The expansion ledger is

| Stage | Degree control | Cut-set sizes | Expansion parameter and denominator |
|---|---|---|---|
| Original G | r-regular | through `2N/3` | `gamma r` |
| Balanced remainder H | degrees `[r-t,r]` | through `h/2` | at least `(gamma/2)r` |
| Spanning factor F | d-regular, `d >= r/2` | through `h/2` | `(gamma/4)d` |
| Same F, converted convention | d-regular | through `2h/3` | `(gamma/8)d` |
| BM-2 output | two cycles | full common support `V(H)` | edges contained in F |

[Fable R1, Corollary B](../r1-substitution/PROOF-R1.md) supplies the motivation to seek a pair avoiding a prescribed vertex. V110 meets that demand on its own growing-degree expander class. It does not use substitution, and it proves no statement about expansion surviving R1 substitution. Therefore it supplies no restricted-class version of `B6 <=> VA6`.

The proof makes no biclique assumption or extraction step. Accordingly, if a K4,4-free graph satisfies the stated hypotheses, the same implication applies to it. We do not construct such a host here or claim that arbitrary pair-free graphs contain one. No claim about nonvacuity of a particular biclique-free family is needed for the implication.

At degree six, even the factor input `r >= 64/gamma^2` fails for every `0 < gamma <= 1`. Moreover (V1) grows with the order. The statement neither proves B6 nor changes the saved general upper bound. The unpaid avoidance-conditioned extraction in E110 remains unpaid by this scout.

## 5. Primary-source scope and novelty check

Primary sources below were opened directly on 2026-10-04. A bounded search also used the phrases “Hamiltonicity bipartite regular expander vertex deletion resilience balanced deletion spectral gap” and “Hamiltonicity mildly pseudorandom regular graphs resilience vertex deletion Müyesser”. Search results alone were not used for mathematical claims.

Bradač and Janzer already discuss the need for equal bipartition sizes alongside strong near-regularity. Their Lemma 3.11 controls expansion and degrees after uniform vertex deletion; Lemma 3.12 requires a balanced alpha-uniform deletion set and concludes bipartite mixing for the remainder. Their Theorem 6.4 supplies a robust spanning-path theorem with degree error at most `d^(1-c)` and a large polynomial inverse-expansion degree requirement. These are direct precedents for the resilience framework. They do not state V110's local exponent-ten, log-cubed bound. [Bradač–Janzer, arXiv:2605.15043v1, Introduction and Sections 3 and 6](https://arxiv.org/html/2605.15043v1).

Müyesser's Theorem 1.3 is stated for a two-sided absolute spectral gap, with threshold `C delta^-6 (log n)^3`. The text after Corollary 1.4 points to a bipartite one-sided analogue but leaves it unwritten. Thus neither the local bipartite BM proof nor its exponent-five spectral improvement should be attributed verbatim to that source. [Müyesser, arXiv:2609.35766v1, Section 1](https://arxiv.org/html/2609.35766v1#S1).

The justified assessment is therefore: **an elementary resilience consequence of the existing local F and BM-2 interfaces, in an already established resilience framework**. The exact inference was missing from the saved separate lanes and is written out here with constants. We do not assert historical priority, a new Hamiltonicity theorem, or that the bounded literature search excludes an earlier identical formulation.

## 6. Verification, remaining review, and stop record

- Read AGENTS.md and the final synthesis before choosing this route.
- Checked the exact local F statement, its accepted proof review, and correction D6; imported F rather than re-proving it.
- Checked the BM-2 expansion statement, its edge-deletion proof, and the accepted review scope.
- Read Fable R1's degree-six corollary and the orientation review's scope warning.
- Checked primary-source statements directly, as recorded in Section 5.
- Completed all deletion, degree, balance, rounding, support, and constant calculations in Sections 2–3. No empirical test is used as proof.
- No Lean, no `check.sh`, no graph census, no Git mutation, and no public action.
- Independent V110 review accepted every mathematical step without repair. Its source-precision correction and the root-requested R1 reference correction are applied in this frozen version. See the [independent review](V110-REVIEW.md). Root owns the combined task-tracker report and the final project status.

One candidate completed; zero repairs used. This scout is stopped. Nothing in this note authorizes another research pass.
