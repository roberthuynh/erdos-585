# G110 independent review

Status: complete, October 4, 2026. **ACCEPT the stated limited conclusions.**

Scope: inspect the G110 distinct-port six-gadget argument and its sole parity
repair, independently replay the small factor-count control, and replay the
root's fixed-matching certificate. No new route, census, Lean, or oracle run.

The open target is existence of a nonempty 4-regular subgraph in a simple
bipartite gadget with shores I, O, `|O| = |I| + 1`, all I-degrees 6, six
distinct degree-5 O-ports, and all other O-degrees 6. Pair existence and a
Hamilton decomposition are separate obligations. A parity counterexample
below would refute a proposed universal cancellation inference, not G110.

## Verdict

The balanced-deletion cut calculation and its four-type conclusion are
correct. If a G110 gadget has no nonempty quartic subgraph, every port-deleted
balanced graph has maximum 4-factor flow exactly `4m - 1`. This is a
conditional reduction, not a contradiction or closed induction.

The group-algebra identity is correct. The proposed universal-evenness repair
is false: two fresh reviewer-written exact counters give **84,577** cubic
factors in the saved balanced graph. The supplied quartic witness is valid,
so the control refutes the parity inference and does not refute G110.

The fixed-matching certificate is also valid in its narrow scope: one actual
pair through the deleted center induces a different matching from the fixed
admissible one. It neither refutes W1 nor rules out another compatible pair.

No mathematical correction to the frozen paper is required. The original
Olson full text was inaccessible to this review as well; that source-access
limit is reported accurately in the paper, and its required special case has
a complete direct proof.

## Inputs and independent replay

Reviewed `scout-gadget/PAPER.md`, the two author counter implementations,
`parity-probe.json`, and `parity-control-certificate.json`. The author scripts
were read but not run in place, because they write their source directory.

Frozen paper SHA-256:
`097e48d7e123eb75defa23c666e04057dae4c776845e86a6dff8861c85425d50`.

Control SHA-256:
`7c2205092aeabb080ba5a2f3f7d990ba5ea2087d145ef12b581e3842aab2c2ba`.

Fixed-matching input SHA-256:
`aaf4a9e2c0c2b4a64a4e7c9865f669bee17c893d1d98996ac3ff9273e14bbf5f`.

Reviewer code and results are in `reviews/G110/`:

- `count_direct.c`: exhaustive choice of three incident edges at each row,
  with no memoization and only the pruning that a column cannot exceed
  degree three. At a leaf, every column must have degree three. Each cubic
  edge set is visited once, through its unique row subsets.
- `replay.py`: a separate exact integer coefficient calculation, multiplying
  one column's elementary symmetric polynomial at a time. States are row
  degree vectors, truncated above degree three. The coefficient of
  `(3,...,3)` counts each cubic edge set once. It does not count its
  decompositions into perfect matchings.
- `replay-results.json`: both counts, witness validation, controls, and hashes.

Both fresh counters return 84,577. The direct enumerator visits 614,386
recursion nodes. Both also return the analytically known controls 1 for
K3,3, 24 for K4,4, and 0 for the 3-by-3 graph with one isolated row.

The replay independently verifies that B is simple and bipartite on two
separately labeled shores of size 8, with 48 edges and every degree 6.
Deleting left vertex 0 gives Gamma with 15 vertices and 42 edges. Its six
distinct degree-5 ports are right vertices `0,3,4,5,6,7`; other O-degrees and
all I-degrees are 6. The count deletes right port 0. The supplied 28-edge
quartic witness is a subset of that balanced graph, with degree exactly 4 at
each of its 14 vertices.

Commands run by this reviewer, all bounded by `timeout 240`:

```text
clang -O2 -Wall -Wextra reviews/G110/count_direct.c -o reviews/G110/count_direct
python3 reviews/G110/replay.py
```

The paths in that command summary are relative to `paper110`; they document
the performed checks rather than asking Robert to run them. Compilation
returned no warning or error; the replay completed with every assertion true.

## Group-algebra argument and source check

The publisher identifies the original source as John E. Olson,
[A combinatorial problem on finite Abelian groups, I](https://www.sciencedirect.com/science/article/pii/0022314X69900213),
Journal of Number Theory 1 (1969), 8-10. Its original full text returned 403
in this review. I do not label the original pages inspected.

I inspected Alon's author-hosted
[Tools from Higher Algebra, Theorem 6.2](https://web.math.princeton.edu/~nalon/PDFS/tools1.pdf),
printed pages 20-21, PDF pages indexed 21-22. It explicitly reproduces
Olson's group-ring proof and gives threshold `1 + sum(p^e_i - 1)`. This is a
reproduced proof, not direct inspection of Olson's original article.

The paper's particular exponent-4 statement can be checked directly. For a
nonempty bipartite vertex set V, orient each edge vector from I to O. The
coordinate-sum-zero subgroup of `(Z/4)^V` has a basis
`b_v = e_v - e_y`, one for each `v != y`, hence is `(Z/4)^(n-1)`. In
characteristic two its group algebra is
`F2[t_v : v != y]/(t_v^4)`, where `t_v = X^(b_v) - 1`.

Each edge factor `1 - X^(e_i-e_o)` lies in the augmentation ideal. A product
of `3(n-1)+1 = 3n-2` such factors is zero, since every surviving monomial
has each exponent at most 3. Its identity coefficient is the parity of all
zero-sum edge subsets, including the empty subset. If no nonempty zero-sum
subset existed, that coefficient would be 1, a contradiction. In a graph
of maximum degree at most 7, a nonempty zero-sum edge subset has degree 4
at every nonisolated vertex. This proves precisely the needed bipartite
quartic threshold. All applications in the paper have positive order.

At the G110 equality `e = 3n - 3`, write `r = n - 1`. The product has
degree at least `3r`, so it lies in the one-dimensional top-degree space,
spanned by `product t_v^3`. Only linear terms contribute to that coefficient.
For a nonroot edge, `X^(e_i-e_o) = X_i X_o^(-1)`, whose linear part after
subtracting 1 is `t_i - t_o = t_i + t_o` over F2. For a root edge the term
is `t_i`; setting `t_y = 0` is therefore correct.

Every I-vertex has degree 6 and must receive exponent 3. Thus exactly three
of its incident factors choose their O endpoint. Every nonroot O-vertex is
chosen three times, and no root edge can choose y. The chosen-O edges are
therefore exactly the spanning cubic factors of `Gamma - y`, with a
bijection between terms and cubic edge sets. This verifies equations (3)
and (4) without any factor-decomposition multiplicity.

Finally `t_v^3 = 1 + X_v + X_v^2 + X_v^3`; independence of the basis means
the identity coefficient of their product is 1. Consequently `c = 0`
forces a nonempty quartic subgraph. The converse is not proved and is false
for the supplied positive control: it has `c = 1` and a quartic witness.
If Gamma were quartic-free, c would have to equal 1 for every allowed root.
The control only disproves an assertion of universal cancellation in the
whole G110 class. It does not rule out a different argument that uses
quartic-freeness in an additional way.

## Four cut types and the conditional flow conclusion

I re-derived the cut identities independently of the saved quartic report.
Fix a port y and set `H = Gamma - y`. It has m vertices on each shore and
deficiency 5 on each shore. For `A subset O - y` and `C subset I`, define
`k = |A| - |C|`, `p = |A intersect P|`, and
`epsilon = e_Gamma(C, O - A)` exactly as in the paper. In particular epsilon
includes edges to y; it is not just a deficiency measured in H.

For the network directed from the O shore to the I shore, a source-side
set consisting of the source, A, and C has cut capacity

```text
4(m - |A|) + e_H(A, I - C) + 4|C| = 4m + Phi.
```

Degree counting gives `e_H(A,I-C) = 6k - p + epsilon`, and hence
`Phi = 2k - p + epsilon`. These account for every network cut. A negative
cut has k positive, since `e_H(A,I-C) >= 0`. Because `p <= 5`, it must
have `k = 1` or 2, with the cases listed in the paper.

Assume now that Gamma contains no nonempty quartic subgraph. For a negative
k=1 cut, the induced complementary piece
`Q = Gamma[(I-C) union (O-A)]` is balanced on t+t vertices, where
`t = m - |C| >= 1`. The inequality t>=1 follows from
`|A| = |C| + 1 <= m`. Its edge count is
`6t - (6 - p + epsilon)`. If `p >= 4 + epsilon`, this is at least
`6t - 2 = 3|V(Q)| - 2`, contradicting the just-proved zero-sum threshold.
Therefore `p = 3 + epsilon`, and the three possibilities are
`(p,epsilon) = (3,0),(4,1),(5,2)`. All have Phi=-1 and complementary
per-shore deficiency 3.

For k=2, negativity forces p=5 and epsilon=0 directly. Phi=-1 again. All
five surviving ports lie in A, the cut from A to I-C has seven edges, and
the complementary piece has smaller-shore deficiency 1 at y. These are
exactly the fourth row and its stated boundary data.

Since a spanning 4-factor of H would be a quartic subgraph of Gamma, at
least one negative cut exists. Every negative cut has Phi=-1 and no cut
has smaller slack, so minimum cut and maximum integral flow equal
`4m - 1`. This holds separately for every y. There is no assertion that
the minimizing cut is the same for different y, and no comparison between
those cuts has been proved.

The sparse-induced-subgraph and connectivity observations in section 1
also check. Under quartic-freeness, a nonempty induced U cannot reach the
zero-sum threshold, so `e(U) <= 3|U| - 3`. For each component, its number
of original ports satisfies `p_C = 6(|O_C| - |I_C|)`, so is 0 or 6.
A zero-port component would be a nonempty 6-regular graph exceeding its
bipartite zero-sum threshold. Hence only the component with all six ports
can remain.

## Why the descent remains unpaid

The first three cut rows yield E3 pieces; the reviewed E3 reduction may
produce C0 pieces. Their boundary incidences are not proved to occur at six
distinct vertices. The last row gives a C1 piece with seven deleted edge
incidences on its larger shore. Nothing in the displayed counts bounds each
of these incidences by one per vertex. Thus the proposed smaller object is
not known to be another G110 gadget.

Enlarging to the old C0/C1/E3/E4 mutual induction reaches its saved C1
exception, with the two output pieces described accurately in section 3.
This is a failure to close the proposed induction. It is not a proof that
no use of the original pieces' additional provenance could close it.
The four aggregate types are necessary data under the no-quartic hypothesis;
they are not explicit counterexamples or a completed classification of
graphs. A quartic subgraph would also still need a separate Hamilton
decomposition argument to yield a pair.

I checked the other cited source in its primary text:
[Katerinis (2025), Theorem 3, printed page 212](https://ajc.maths.uq.edu.au/pdf/93/ajc_v93_p211.pdf).
It requires `ell <= k/2` and edge connectivity at least `2ell - 1`, and
then guarantees an ell-factor after any opposite-shore vertex deletion.
For k=6, ell=4 violates both the degree restriction and the possible
edge-connectivity bound. The paper correctly does not invoke it for G110.

## Fixed-matching certificate: exact narrow scope

The independent replay checks the graph's 12 listed edges and both six-cycles
edge by edge. Each cycle is simple, they have the same six-vertex support,
their edge sets are disjoint, and every cycle edge is present. Their union
is the octahedron graph.

For removed vertex 0, its neighborhood is `{2,3,4,5}`. The fixed matching
`{23,45}` covers that neighborhood and consists of nonedges of the host,
so it is admissible. But the two displayed cycles induce passages with
endpoint matching `{25,34}`. The two matchings differ. Indeed those actual
endpoint pairs are existing host edges, so even admissibility of the
induced matching is not automatic.

The certificate therefore disproves the general inference that **every
displayed pair through a degree-four center uses an externally prescribed
admissible matching**. It does not disprove existence of some other
compatible pair. The six-vertex host has 12 edges, below the W1 threshold
`3*6 - 4 = 14`; it is not a W1 counterexample or a density-qualified
counterexample to a repaired fixed-matching theorem. It demonstrates the
specific inference gap in the old proof, and does not invalidate the census.

## Final state

Accepted as a bounded failure analysis with the conditional four-type
reduction and the exact finite parity falsifier. G110 remains open. Pair
existence, bipartite degree-six forcing, and the global growth objective
are neither proved nor refuted by this packet. No Lean or project oracle
PASS is claimed.

Only this review and files in `reviews/G110/` were written. No source-lane
file, Git state, or public artifact was changed. No further route, census,
or subagent was started. Review complete; stopped.
