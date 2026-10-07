# Independent mathematical review of V110

2026-10-04. **Mathematical verdict: ACCEPT as a paper consequence of the stated
local Lemma F and BM-2.** No mathematical repair is required. The requested
source-description precision correction at author line 179 is applied and the
final snapshot is confirmed below. This is not a project oracle PASS, a new growth bound, or a
historical-novelty finding.

Reviewed [PAPER.md](PAPER.md),
initial frozen SHA-256
`a9e21869cee8f6b97bce595fb3ae693a5269972476889c91eb589573df998674`.
The final accepted SHA-256 is
`1b7d32fc494e0027ed89591702bfe387da6e3258d065ac432d86be23a67af717`.
I read the final file and independently recomputed its hash; the mathematical
statement and derivation are unchanged. Line references apply to both 196-line
versions. I independently checked every
displayed inequality and the graph/support transfers in Sections 1–4. I read the
final synthesis and orientation/BM-REVIEW.md, inspected the exact F and BM-2 source
statements and their recorded reviews, and checked the two primary-source scope
paragraphs. I did not re-audit the full BM proof.

## 1. Exact accepted claim and dependencies

Let `C_BM >= 1`, `C_gamma = 32^5 C_BM`, and `C_V = 2^42 C_gamma`.
For a finite simple bipartite r-regular BJ gamma-expander of total order `N >= 4`,
with `0 < gamma <= 1` and

    r >= C_V gamma^-10 (log(2N))^3,

every deletion of equal numbers `t` from the two sides, where

    0 <= t <= floor(gamma^2 r / 32),

leaves two spanning edge-disjoint Hamilton cycles on the exact remaining support.
The quantifier is over arbitrary deletion sets of that size, without a random or
uniform-distribution hypothesis. This follows from the local paper interfaces:

- [Spectral Lemma F, lines 323–342](../lemma-f/LEMMA-F.md),
  with its [accepted review, lines 61–68](../lemma-f/LEMMA-F.md).
- [BM-2, lines 125–129 and 595–610](../bipartite-hamilton/REPORT.md),
  with its [accepted expansion-case review](../bipartite-hamilton/BM-REVIEW.md).

Neither input nor the new consequence has a project `check.sh` PASS. Acceptance
here verifies the consequence from those precise written inputs. It does not
remove their unformalized-proof dependency.

## 2. Inequality and hypothesis audit

1. **Constants, positivity and logarithms, lines 38–56 and 74–78: correct.**
   Enlarging the absolute existence constant to at least one is legitimate.
   `32^5 = 2^25`, so `C_V = 2^67 C_BM`. Since `N >= 4`,
   `log(2N) >= log 8 > 1`; since `0 < gamma <= 1`,
   `gamma^-10 >= gamma^-2`. Thus (V1) implies
   `r >= 64 gamma^-2 >= 64 > 0`. Natural logarithms are specified, and the
   original total order is used consistently.

2. **Balance, simplicity and retained order, lines 74–84: correct.**
   Double-counting edges gives `r|A| = r|B|`. Positive r implies equal side
   sizes `m=N/2`, so N is even. Simplicity gives `r <= m`.
   The floor budget gives `t <= gamma^2 r/32 <= r/32`. Each remaining side
   therefore has `m-t >= r-r/32 = 31r/32 >= 62` vertices. Hence the remainder
   is balanced, its total order `h=N-2t` is even, and `h >= 124 >= 4`.
   Also `t <= N/64`, so `31N/32 <= h <= N`. There is no empty-support case.

3. **Pointwise loss and cut identity, lines 86–101: correct.**
   Each surviving vertex loses at most t neighbors, because its neighbors lie
   only on the opposite side and the graph is simple. Thus all H-degrees lie
   in `[r-t,r]`. For `Z subset V(H)`, the cut identity in line 92 is exact:
   the removed cut edges are precisely `E_G(Z,D)`.
   Summing the same pointwise loss gives `e_G(Z,D) <= t|Z|`, not `2t|Z|`.
   Every tested `|Z| <= h/2` also satisfies the original BJ size condition.
   Finally `gamma-gamma^2/32 >= 31gamma/32 >= gamma/2`. This proves (V5)
   with original degree r as denominator; no regularity of H is assumed.

4. **All Lemma F inputs, lines 103–110: correct.**
   For `k=r`, `eta=t/r`, and `alpha=gamma/2`, r is positive,
   `0 <= eta <= gamma^2/32 = alpha^2/8`, and `0 < alpha <= 1/2 <= 1`.
   Also `k >= 64/gamma^2 = 16/alpha^2`. H has the equal sides, pointwise
   degree interval and half-order cut bound required by F.

5. **Floor substitution and retained degree, lines 112–121: correct.**
   From F, `theta=(eta+2/r)/alpha=2(t+2)/(gamma r)`. Hence its integer degree is
   exactly `d=floor(r-t-2(t+2)/gamma)`, as stated. The F lower bound becomes
   `d >= (1-3gamma/16)r-1 >= 13r/16-1`.
   Subtracting `r/2` leaves `5r/16-1 >= 19 > 0` at `r >= 64`, so `d >= r/2`
   safely absorbs the rounding loss. In particular d is a positive integer
   and at least 32. F's cut coefficient `alpha/2` is exactly `gamma/4`.
   It is an actual spanning subgraph of H, with no added edge.

6. **Half-order to BJ conversion, lines 125–132: correct.**
   For `h/2 < |Z| <= 2h/3`, the complement W has
   `1 <= |W| < h/2` and `|W|=h-|Z| >= |Z|/2`. The two cut edge counts agree.
   Thus `(gamma/4)d|W| >= (gamma/8)d|Z|`. Smaller sets already satisfy the
   stronger `gamma/4` bound. This is the essential extra factor of two;
   the final BJ parameter is `beta=gamma/8`, with `0 < beta <= 1/8`.

7. **BM-2 degree and order comparison, lines 134–141: correct.**
   Its right-hand coefficient is

       2^11 C_gamma (gamma/8)^-10
       = 2^11 * 2^30 C_gamma gamma^-10
       = 2^41 C_gamma gamma^-10.

   The inequality `d >= r/2` and the assumed `2^42` multiplier pay that
   coefficient exactly. Since `4 <= h <= N < 2N`, both logs are positive
   and `log(h)^3 <= log(2N)^3`. F is simple, bipartite, regular and of order
   at least four. Every BM-2 input is present.

8. **Cycles and full support, lines 141–143: correct.**
   BM-2 yields two distinct edge-disjoint Hamilton cycles of the same F.
   F spans H, so both supports are exactly `V(H)`. Since
   `E(F) subset E(H) subset E(G)`, they satisfy the original Pair predicate
   without a projection or a lift. Balanced deletion also keeps the even
   support size needed by bipartite cycles.

9. **Prescribed vertex and padding, lines 145–155: correct.**
   The derived lower bound gives `gamma^2 r/32 >= 2`, hence its floor is
   at least two and t=1 is allowed. For any prescribed v, every opposite-side
   u is distinct and permits a pair with support `V(G) minus {v,u}`.
   This pair lies in `G-v`; it need not span `G-v`, and the author correctly
   says so. For the general forbidden set W, choosing the larger side count
   as t and padding the other side is possible because
   `t <= b <= r/32 <= N/64 < N/2`. The exact support size is `N-2t`; it
   equals all of `V(G-W)` precisely when W already has equal side counts.

## 3. Scope audit

The prescribed-vertex demand is genuinely met on the stated growing-degree
expander class: deletion sets are arbitrary, and the pair is in the original
graph with the named vertex absent. The argument does not rely on an assumed
choice of favorable deleted vertices or on a random-deletion result.

The author correctly excludes degree six. Even the preliminary bound
`r >= 64/gamma^2` fails there for every allowed gamma, and the main threshold
grows with order. The argument supplies no expanding piece inside an arbitrary
avoider and no preservation of expansion under Fable R1 substitution. Therefore
it gives neither B6, an expander-restricted B6/VA6 equivalence, nor a new general
bound for Erdős 585. No biclique-free host is constructed; line 171 correctly
states only the conditional applicability to such a host if one satisfies the
hypotheses. Those limits must remain in the final report.

## 4. Primary-source precision and final status

The [Bradač–Janzer source](https://arxiv.org/html/2605.15043v1#S3), opened directly
on 2026-10-04, supports the precedent description with one clarification:
Lemma 3.12 requires a balanced alpha-uniform deletion set and concludes
bipartite mixing. I requested that both qualifications be named at line 179.
Lemma 3.11's degree/expansion comparison and
[Theorem 6.4's stronger quantitative hypotheses](https://arxiv.org/html/2605.15043v1#S6)
are consistent with the author's limited precedent claim. These sources are
context, not inputs to the elementary deletion estimate above.

[Müyesser's Theorem 1.3 and following discussion](https://arxiv.org/html/2609.35766v1#S1),
also opened directly, use the absolute-spectrum exponent-six statement and
leave the one-sided bipartite analog unwritten. The author correctly treats
exponent five and BM-2 as local written-proof inputs. No priority claim is
supported or made.

Final snapshot accepted: the source wording at line 179 is corrected, the R1
reference at line 169 now uses the exact worktree path requested by root, and
the status lines record paper acceptance. The mathematical statement and proof
are unchanged. No correction remains outstanding in this review.

No Lean, `check.sh`, graph search, source-lane edit, Git mutation or public action
was performed. Root owns the combined report and result status. Reviewer stopped.
