# G110: the distinct-port quartic question remains open in this pass

October 4, 2026. Bounded final scout. Status: conditional paper reductions and a
small independently counted positive control; no project oracle result.

## Outcome

This pass does not prove or refute G110. It narrows the balanced deletion rule
to four cut types. Under the hypothesis that a G110 gadget has no nonempty
4-regular subgraph, **every port-deleted graph has maximum 4-factor flow exactly
one below full value**. The remaining descent does not preserve the six distinct
ports. The saved broader C0/C1 induction therefore still encounters its stated
unclosed C1 case.

The single repair was a group-algebra parity argument at the exact Olson
boundary. Its coefficient has a useful interpretation as the number of cubic
factors after deleting a port, modulo two. Universal cancellation is false:
an explicit valid 15-vertex G110 gadget has **84,577** such factors. Two exact
counts agree. The same gadget has an explicit 4-factor after the deletion, so
this is a counterexample to the proposed parity repair, not to G110.

Pair(Gamma) remains a separate, stronger assertion. No step below turns two
2-factors into two connected cycles with a common support.

## 1. Exact class and the zero-sum threshold

Let Gamma=(I,O) be simple and bipartite, |I|=m, |O|=m+1. Every I-vertex has
degree 6. A set P of exactly six O-vertices has degree 5; all other O-vertices
have degree 6. Thus n=2m+1 and e=6m=3n-3. Simplicity gives m>=5. Adding a new
I-vertex adjacent to P produces a simple bipartite 6-regular graph B; conversely
Gamma=B-o has this form. This is the distinct-port case used in Fable R1.

Here is the exact zero-sum fact needed, with a direct proof of this special
case. A bipartite n-vertex graph with at least 3n-2 edges has a nonempty edge
set whose degrees are all divisible by 4. Orient edge vectors as e_i-e_o in
(Z/4)^V. They lie in the coordinate-sum-zero group K, isomorphic to
(Z/4)^(n-1). Over F2, the group algebra of K is the truncated ring
F2[t_1,...,t_(n-1)]/(t_1^4,...,t_(n-1)^4), via t_v=X_v-1. Every factor
1-X^g has positive degree, so a product of 3(n-1)+1 such factors is zero.
Its identity coefficient counts zero-sum subsets modulo two, including the
empty subset. Thus there is a nonempty one. If maximum degree is at most 7,
its nonisolated vertices all have degree 4.

This is the p=2, exponent-4 group-algebra argument in Olson's theorem, whose
proof is reproduced in Alon's [Tools from Higher Algebra, Theorem 6.2,
printed pp. 20-21](https://web.math.princeton.edu/~nalon/PDFS/tools1.pdf).
Olson's original publisher abstract was available, but its full text returned
403; this report does not claim to have inspected Olson's original pages.
The argument above supplies the specific threshold independently of that gap.

G110 has 3n-3 edges, one below this threshold. One cannot substitute equality
for the strict nilpotency inequality. If Gamma has no quartic subgraph, every
nonempty induced subgraph Gamma[U] satisfies e(U)<=3|U|-3, since otherwise the
same threshold applies to Gamma[U]. Such a Gamma is connected: a component with
p ports has 6(|O_C|-|I_C|)=p, so p is 0 or 6. A component with no ports is
6-regular and already exceeds its zero-sum threshold; hence only the one
component containing all six ports can exist.

## 2. Main rule: delete a port and inspect the balanced factor cut

Fix y in P and put H=Gamma-y. Its shores I and O-y both have size m, with
five deficiency units on each shore. Here deficiency means sum(6-degree)
in the graph named. On O-y, those units remain on five distinct vertices.

For A subset O-y and C subset I, set

- k=|A|-|C|,
- p=|A intersect P|,
- epsilon=e_Gamma(C,O-A).

The integral flow network with capacity 4 at shore vertices and capacity 1
on graph edges has a spanning 4-factor precisely when every cut slack is
nonnegative. The slack indexed by A,C is

    Phi(A,C)=e_H(A,I-C)-4(|A|-|C|)=2k-p+epsilon.                 (1)

Indeed e_Gamma(A,I-C)=6|A|-p-(6|C|-epsilon). The usual source-sink cut
capacity is 4m+Phi. If Phi<0 then k>=1 because its other expression is a
nonnegative edge count minus 4k. Since p<=5, a negative cut has k=1 or 2.

Without assuming no quartic subgraph, the possible pairs are:

- k=1 and p>=3+epsilon, with p<=5;
- k=2, p=5, epsilon=0.

Now assume Gamma has no quartic subgraph. For a negative k=1 cut, take the
actual induced complementary piece

    Q=Gamma[(I-C) union (O-A)].

Its shores have the same positive size t=m-|C|. Counting its edges from O-A,
its deficiency on each shore is

    d=6-p+epsilon.                                            (2)

If p>=4+epsilon, then d<=2 and e(Q)=6t-d>=3|V(Q)|-2. The zero-sum fact of
section 1 gives a quartic subgraph of Q, a contradiction. Therefore every
negative k=1 cut has p=3+epsilon and Phi=-1. The k=2 case also has Phi=-1.
We obtain precisely four aggregate types:

| k | p | epsilon | e_Gamma(A,I-C) | complementary Q |
|---|---|---|---|---|
| 1 | 3 | 0 | 3 | balanced, deficiency 3 per shore |
| 1 | 4 | 1 | 3 | balanced, deficiency 3 per shore |
| 1 | 5 | 2 | 3 | balanced, deficiency 3 per shore |
| 2 | 5 | 0 | 7 | imbalance 1, smaller-shore deficiency 1 |

All negative cuts have slack -1, and at least one exists because a 4-factor
of H would itself be a quartic subgraph of Gamma. The maximum integral flow
therefore equals 4m-1. This conclusion holds **for every y in P**, with a cut
that can depend on y. It says that H has an edge set with all degrees at most
4 and exactly 4m-1 edges. It does not assert a full 4-factor or specify the two
unsaturated vertices.

In the last row, A contains P-y and epsilon=0 says no C-vertex has a neighbor
in O-A. Thus Gamma[A union C] has smaller shore C saturated at degree 6,
imbalance 2, and exactly seven edges from A to I-C. The complementary Q has
smaller shore O-A, whose only deficient vertex is the original port y; its
larger-shore deficiencies are the seven removed edge incidences at I-C.

## 3. Exact unpaid descent

The conclusion needed is an actual nonempty quartic subgraph in Gamma. The
proposed rule would have to infer this from at least one of the four cut
pieces above, or derive a contradiction by comparing the cuts for different
ports. It does neither in the current proof.

The first three rows supply a balanced E3 piece, in the notation of the saved
quartic report, section 5.1 (not included).
If it has no spanning 4-factor, its reviewed factor-cut argument splits off
smaller C0 pieces: imbalance one, smaller shore saturated at degree 6,
maximum degree at most 6. Their six deficiency units on the other shore need
not be distinct. The seven-edge boundary in the final row likewise gives a
C1 piece, not a smaller G110 gadget. Several removed incidences can meet the
same vertex. The original distinct-port hypothesis supplies no bound of one
on these incidences. Induction on G110 alone is therefore not closed.

The broader saved mutual induction on C0,C1,E3,E4 is independently reviewed,
but remains unclosed at this exact C1 case. For a C1 graph with smaller shore
X, unique degree-5 vertex x1 in X, and larger shore Y, delete a minimum-degree
y0 in Y. In the balanced graph, a failed cut A subset Y-y0, C' subset X has

    |A|-|C'|=2,  D_A=5+epsilon,  epsilon in {0,1},  x1 notin C'.

Here epsilon=D_(C')+e(A',C') is measured in that balanced graph. It creates
both a C2 piece and an imbalance-two piece whose smaller shore has deficiency
at most one. Exactly seven edges join A to X-C'. The reviewed remaining
subcase has at most three of these edges at each A-vertex, at most three at
each X-C' vertex other than x1, and at most two at x1. Neither output is in
the induction classes. This is a conditional reduction through the larger
class, not a claim that every G110 instance realizes that subcase or that
all its additional provenance has been discarded without cost.

The 58 Tutte parameter types in the wildcard work are necessary aggregate
types for a different minimal-counterexample domain. They do not eliminate
these pieces. Neither the existence of a 4-core nor the existence of two
arbitrary 2-factors closes the obligation.

## 4. Single repair: the exact-boundary parity coefficient

Let r=n-1. At e=3r, the group-algebra product in section 1 has degree at
least 3r and hence equals

    c * product_(v != y) t_v^3,  with c in F2.

To compute c only the linear part of each edge factor matters. For a root
y in O the coefficient is

    c = [product_(v != y) t_v^3] product_(io in E(Gamma)) (t_i+t_o),
    with t_y=0.                                               (3)

The oriented group coordinates give t_i-t_o as their linear part, which is
t_i+t_o in F2. For every i in I, degree 6 and exponent 3 mean exactly three
incident factors choose their O endpoint. Every nonroot O endpoint is chosen
three times; a root edge cannot choose the root. Those chosen edges are
exactly a spanning cubic factor of Gamma-y. Thus

    c = number of spanning 3-factors of Gamma-y modulo 2.       (4)

The coefficient of the group identity in product t_v^3 is 1, because
(X_v-1)^3=1+X_v+X_v^2+X_v^3 in characteristic two. Consequently c=0 would
force a nonempty zero-sum edge set and therefore prove G110 for that instance.
If Gamma were quartic-free, (4) would instead have to be odd for every port y.

Universal evenness is false. The control packet below contains B with shores
0,...,7 and row neighborhoods

    0: 0 3 4 5 6 7
    1: 0 1 2 4 5 6
    2: 1 2 3 4 6 7
    3: 0 2 3 4 5 7
    4: 0 1 3 4 5 6
    5: 0 1 2 3 5 7
    6: 1 2 3 5 6 7
    7: 0 1 2 4 6 7.

Every row and column has degree 6. Delete left vertex 0 to obtain Gamma.
The six ports are right 0,3,4,5,6,7. Delete right port 0. A row-by-row exact
integer dynamic program counts **84,577** spanning cubic factors. A separate
meet-in-the-middle enumeration of the first three and last four rows obtains
**84,577** again. Both count edge sets, without counting orderings of their
perfect-matching decompositions. The following row neighborhoods are an
explicit spanning 4-factor of this same balanced deletion:

    1: 1 2 4 5
    2: 1 2 3 6
    3: 2 3 4 7
    4: 1 4 5 6
    5: 1 3 5 7
    6: 3 5 6 7
    7: 2 4 6 7.

The certificate checker verifies edge containment and every row and column
degree. This host is a positive control, not a quartic-free graph. An odd
coefficient is therefore not sufficient to certify absence either.

Artifacts: [initial exact count](parity_probe.py), [independent count and
witness validator](verify_parity_control.py), [full certificate](parity-control-certificate.json).
The fixed probe examined three small controls and stopped on the first odd
count. No census or next search was launched.

## 5. Primary factor theorem checked, and stopping state

Katerinis, [A note on regular factors in vertex-deleted subgraphs of regular
bipartite graphs](https://ajc.maths.uq.edu.au/pdf/93/ajc_v93_p211.pdf),
Australasian Journal of Combinatorics 93(1), 2025, pp. 211-215, Theorem 3,
requires ell<=k/2 and edge connectivity at least 2ell-1. It gives an ell-factor
after deleting any opposite-shore vertex pair. For k=6 it reaches ell<=3;
ell=4 violates the degree restriction and would also require connectivity 7,
which a nonempty 6-regular graph cannot have. It does not establish G110.

The exact G110 quartic assertion remains unresolved in this pass. The main
rule has the four-type, one-edge-deficit conclusion but no closed descent.
The single parity repair has a certified finite falsifier to universal
cancellation. Pair(Gamma), B6 and the global growth goal remain untouched.

No Lean, check.sh, Git action, public action, source-lane edit, subagent or
large search was performed. The parent owns independent review integration,
Task-tracker publication and the final stop. No continuation pass is proposed.
