# Stronger route to R1: three-color components are induced

October 4, 2026. Complete written addendum awaiting independent review.
The frozen main paper is unchanged. This is a strengthening and a shorter
proof interface, not a repair of a failed statement or a new growth claim.
No Lean is authorized by this note alone.

Use the literal field, graph, translations and canonical colors from
PAPER.md. Section 3 there proves that every at-most-four distinct parabola
points are affinely independent over F_3.

**Color-closure proposition.** For every nonempty color set T with |T|<=3,
every connected component of the subgraph consisting of those canonical
matching colors is an INDUCED subgraph of the full host, regular of degree
|T|. Consequently any simple cycle using at most three canonical colors
has induced host degree at most three on its own vertex support.

Proof. Choose a_0 in T and put

    U=span_(F_3){v_a-v_(a_0): a in T}.

For a left vertex X, let B_X have shores X+U and X+v_(a_0)+U.
Every selected color stays inside B_X. Conversely a two-edge walk using
color a and then a_0 moves a left vertex by v_a-v_(a_0). These differences
generate U; their negatives are attained by reversing the walk. Thus all
left vertices in X+U are reachable, and the a_0 matching reaches every
right vertex in the other shore. B_X is exactly the connected component
through X, with no reference to a chosen cycle or quotient walk.

An additional color z has an edge inside B_X exactly when

    v_z belongs to v_(a_0)+U.

If z is outside T, this membership is an affine dependence among the
|T|+1 distinct points indexed by T union {z}. That set has at most four
points, so Section 3 excludes it. Hence the only host edges within B_X
are the selected |T| matching classes, each still perfect on B_X.
This proves inducedness and regularity, including the case |T|=1, where
each component is just one edge. Every cycle using these colors lies in
one such component. Passing to its actual vertex support cannot increase
the induced degree. This proves the proposition.

**Corollary R1-plus.** Starting from the canonical coloring, fix a pair of
colors a,b and swap them on ANY chosen collection of components of their
bichromatic factor. There is no restriction on the number of components
or changed edges. Take all such resulting colorings, all choices of a,b
and component collection, and the initial coloring. Every bichromatic
cycle in this whole family has induced host degree at most three on its
support, so none of those supports can contain a faithful pair.

Proof. A resulting cycle using colors i,j has canonical edge colors
contained in a set T of size at most three. If neither i nor j is in
{a,b}, it uses only canonical colors i,j. If {i,j}={a,b}, it uses only
canonical a,b. Otherwise exactly one is switched and the other is a
third color c, so every actual edge has canonical color in {a,b,c}.
Apply the proposition. Four distinct incident edges are necessary for
a faithful pair on a common support, giving the same contradiction as
in the main paper, even for cycles from different resulting states.

Thus the barrier does not depend on a bound of six changed edges. It
also covers one whole two-class transformation, with independently many
component swaps. It does not cover a second transformation involving
another color pair: an exposed cycle can then use four canonical colors,
and the color-closure proposition deliberately stops at three.

The exact graph counts, C4-freeness, connectedness and fixed-polylogarithm
comparison are unchanged from PAPER.md. The 6/18-cycle classification in
that paper remains valid for its narrower single-component move and is
not asserted for this larger simultaneous-swap family by this addendum.

Suggested faithful formal endpoint, only after review and the source gate:
prove induced closure of actual color subgraphs, connect actual proper
two-class recoloring and actual cycle edges to at most three canonical
colors, then deduce faithful pair exclusion and the explicit growing
family. Do not replace the endpoint with a conditional degree assumption
or a named opaque detector predicate that has no graph/move bridge.
