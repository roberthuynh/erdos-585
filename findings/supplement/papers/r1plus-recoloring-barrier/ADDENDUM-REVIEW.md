# Pass 103 independent review of the color-closure addendum

## Disposition and exact artifact

**Accepted unchanged as a complete paper argument for the stated
color-closure proposition and R1-plus corollary.** No correction, gap, or
repair was found. This is a separate strengthening of the accepted R1
statement. It is not a project `RESULT: PASS`, a growth theorem, or a
historical novelty assessment.

Reviewed source: `paper103/radius/COLOR-CLOSURE.md`.

SHA-256:
`0f8ab500ef3577e61c18fa204321642278290304fb79242dbaf1a88fa892e637`.

Exact preread snapshot: `root-COLOR-CLOSURE.initial.md` in this directory.
The addendum review contract was saved before opening its proof:
`ADDENDUM-CONTRACT.md`, SHA-256
`68fc0e5043ff7b4f96cc8f09c45b17737b82a85bb69b4a9d798a0bc91985413b`.

The unchanged main paper supplying the graph and affine-independence
lemma has SHA-256
`dd8912d9c9139c0cfd56f5a9cfe1685e7c7bbac4e92f08f632aac5d8e0f30c60`.
Its independent review was completed before reading the adversary paper
or this addendum. The adversary review was also completed before this
addendum review. The separate receipts preserve that order.

## Domain and the lemma actually used

The host is the literal simple bipartite graph from the main paper:
two disjoint copies of `V = F_q^2`, where `q = 3^k`, `k >= 2`, with
canonical color `a` giving the matching `X -> X + v_a`, where
`v_a = (a,a^2)`. Spans and affine dependence are over `F_3`, not `F_q`.
The main paper's verified statement is that every set of at most four
distinct canonical color vectors is affinely independent over `F_3`.

The addendum explicitly takes a nonempty color set `T` with `|T| <= 3`.
It claims inducedness for each full connected component of the subgraph
with all canonical edges of colors in `T`. It does not claim that an
arbitrary connected subgraph, or each cycle contained in such a component,
is induced. That distinction is correct and sufficient for its endpoint.

## Exact component: both containment and full reachability

Choose `a_0 in T`, and let

`U = span_F3 {v_a - v_a0 : a in T}`.

For any left vertex `X`, use the actual two shores

`L(X + U)` and `R(X + v_a0 + U)`.

For a selected color `a`, addition of `v_a` carries the first coset to
the second, because `v_a - v_a0` belongs to `U`. In the reverse direction,
subtracting `v_a` from the right coset returns to the left coset. Thus
selected edges cannot leave the proposed component from either shore.

For every left point `Y`, traversing color `a` from left to right and
color `a_0` from right to left reaches `Y + v_a - v_a0`. Traversing the
colors in the reverse order realizes the negative displacement from
any left point. Concatenating these actual two-edge walks realizes every
finite `F_3`-linear combination of the generators. Their displacements
are exactly `U`, so every left point of `X + U` is reachable. The
`a_0` matching then reaches every point of the right coset. These are
walks in the original graph, with no quotient or contraction inference.

Every component contains a left vertex because the selected set is
nonempty and each selected canonical color is a perfect matching.
Consequently the argument classifies every component, including those
initially specified by a right vertex.

## Internal host edges and affine dependence for each size

An actual edge of canonical color `z` from a point of `X + U` stays
within the two proposed shores if and only if

`v_z - v_a0 in U`.

This condition is independent of the point of the left coset. If it
holds, the translation maps the entire left coset bijectively to the
right coset. Thus it describes all internal edges on both shores,
not merely the colors encountered along one selected walk.

Suppose it holds with `z` outside `T`. Write

`v_z = v_a0 + sum_{a in T\{a_0}} lambda_a (v_a - v_a0)`.

Moving terms to one side gives an affine relation on the distinct points
indexed by `T union {z}`. The coefficient of `v_z` is one, so the
relation is nontrivial. The coefficients sum to zero in `F_3`, including
when some of the displayed `lambda_a` vanish. The set has at most four
points, so the verified affine-independence lemma excludes the relation.

This covers every allowed size without an implicit full-support
coefficient assumption:

- If `|T| = 1`, then `U = {0}`. Membership would give `v_z = v_a0`,
  contradicting injectivity. The component is one actual edge.
- If `|T| = 2`, an outside member of the affine line would give a
  nontrivial affine relation on at most three distinct points.
- If `|T| = 3`, the analogous relation uses at most four distinct points.
  A zero coefficient merely reduces its support and does not evade the
  lemma.

Every selected color already belongs to the internal set of colors.
No other one does. Each selected translation is a perfect matching on
the two cosets, and distinct colors give distinct actual edges. Hence
the full host induced on the component is exactly the selected-color
subgraph, regular of degree `|T|` on both shores. The addendum's
inducedness and degree statements follow.

## Passing from a color component to a cycle support

A simple cycle whose actual edges have canonical colors in `T` is
connected in the selected-color subgraph. All its vertices therefore
lie in one of the components just identified. Its actual vertex support
`S` may be a strict subset of that component. The host graph induced
on `S` is then an induced subgraph of the already checked component,
so every degree in `G[S]` is at most `|T| <= 3`.

This implication neither assumes that the cycle visits the entire
component nor identifies a cycle's selected edges with all host edges
on its support. It proves the required host-degree bound despite that
distinction.

## Arbitrary simultaneous swaps on one fixed pair

Take distinct canonical colors `a,b`. Their matching union is a
spanning two-regular graph, so its components are disjoint actual
even cycles. Any chosen collection is a union of entire components.
At each vertex either both incident `a,b` edges are swapped or neither
is. After swapping, the vertex still has exactly one edge of color `a`
and one of color `b`; all other incident colors are unchanged. Thus
the operation is an actual proper recoloring of the same host and
preserves each color class as a perfect matching. The argument applies
to an empty collection, every component, or any intermediate collection,
without a limit on changed edges.

For any bichromatic component in the resulting coloring, the two new
color labels exhaust the following cases:

- Neither label is `a` or `b`: its actual edges have only the same two
  canonical colors.
- The two labels are `a,b`: their actual edge union is unchanged and
  uses only canonical colors `a,b`.
- Exactly one label is `a` or `b`, and the other is `c` outside the
  pair: every edge of the changed label had canonical color `a` or
  `b`, and every edge labeled `c` retains canonical color `c`.
  The actual cycle is contained in the canonical `{a,b,c}` subgraph.

These are all possible pairs. The new coloring is proper, so its
bichromatic components are actual simple cycles in the simple host.
Each such cycle uses at most three canonical colors, and the preceding
proposition bounds the degree of the host on its actual support.
The initial coloring is included as well. This is uniform over every
choice of pair and collection and does not use the narrower main
paper's one-component orbit classification.

## Faithful collision exclusion across the full stated family

If two simple cycles are edge-disjoint and have the same actual vertex
support `S`, then each vertex of `S` is incident to four distinct
actual edges of their union. Therefore `G[S]` has degree at least four
at every vertex. Every exposed support in the addendum has induced
host maximum degree at most three, a contradiction.

The argument is a property of the fixed uncolored host on `S`, so it
also applies when the two candidate cycles arise in different allowed
states, from different swapped color pairs, or from different component
collections. In fact a detected support cannot have an edge-disjoint
mate even if that other cycle is not detected. This does not prohibit
faithful pairs on other supports that the stated family never exposes.

## Inherited quantifiers, exclusions, and status

The construction, simplicity, connectedness, `C4`-freeness, degree `q`,
order `N = 2q^2`, and unbounded family `q = 3^k` are exactly those
already checked in the unchanged main paper. The addendum imposes no
new restriction on `k`. Consequently the previously verified comparison
`q > C (log N)^a` for every fixed `C > 0`, fixed real `a >= 0`, and all
sufficiently large `k` is inherited without a new loss.

The accepted detector starts at the specified canonical coloring and
performs at most one whole transformation on a fixed color pair,
allowing arbitrary simultaneous component swaps. Its output family
unions the results of all such choices. It does not permit first
transforming one pair and then a different pair. The three-color
containment argument gives no degree bound for that larger family.
The addendum correctly retains this boundary and does not infer global
graph avoidance or reopen KS102.

The main paper's six/eighteen-cycle classification is retained only
for its original single-component operation. This addendum does not
assert that classification for its larger family. Its final formal
endpoint is explicitly only a suggestion subject to independent source
and formalization gates, not an already proved Lean declaration or an
authorization to run Lean.

No mathematical computation, field/orbit enumeration, graph search,
source expansion, Lean, oracle, nested agent, public action, or author
edit was used for this review. Only the review directory was written;
hashing and exact snapshots were used for artifact integrity. The
mathematical paper audit is complete. Novelty, usefulness, faithful
formalization, and project result status remain separate root gates.
