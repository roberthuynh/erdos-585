# Independent review of the complete R1-plus formal endpoint

October 4, 2026. **Accepted unchanged as the complete faithful endpoint
specified by the pass 104 contract.** No vacuity, lost quantifier,
missing construction bridge, source-scope mismatch, or proof gap was
found. No correction is requested. The reviewer did not run Lean or
check.sh; this acceptance precedes and is separate from the root oracle.

The exact reviewed declaration is
`Erdos585.ParabolaBarrier104.arbitrary_polylog_barrier` in
`openmath/Openmath/Proofs/ParabolaBarrier104.lean`, SHA-256
`6ac3c052cfb4b0efac39f91dd47f87b502846d90c55be0029fd36257168adef5`.

## Frozen input and compilation evidence

All seven source hashes were matched against root's
`paper104/integration/FROZEN-COMPILE.json` before their exact bytes
were copied into the review directory. The receipt has SHA-256
`36853c270e527fd586e47df00b8ac1543d0ecd7c2b7618328df2d87d4090ae08`.
It identifies the declaration above, records the integrated
`timeout 240 lake env lean` command, exit code zero, no diagnostics,
and no oracle result. The named `full-compile-02.log` was read and
is empty. Source-level inspection below concerns that compiled frozen
statement, its actual definitions, and the proof bridges it uses.

| Source module | Reviewed SHA-256 |
| --- | --- |
| `InducedComponentBarrier104.lean` | `a3002db95ec2a071300343d7e2263562865e05bec12abca7809eec22136ad3cf` |
| `ParabolaAlgebra104.lean` | `82ea82ae83fd41ec50d431205e86407b701ec520b5c8e8757f69da690a1d9679` |
| `HaarComponents104.lean` | `a998560c36757cd03bea6d5a34b4bf4a431db7c092fe5b04f6561d1fe94fa7bc` |
| `KempeSwap104.lean` | `cd967de019c9b22184596ed3be7b3c07f02481665f3d0a210437eaae1790b006` |
| `ParabolaGraph104.lean` | `d40ce651e68d034a386acd0536cf27c03b1f2fdbc3ccf675c015089291c785f0` |
| `ParabolaGrowth104.lean` | `8e8ad0b7ec27e1f255abf7c1d117b6f1d0c263f1362f99c7438b6db9211b8cd2` |
| `ParabolaBarrier104.lean` | `6ac3c052cfb4b0efac39f91dd47f87b502846d90c55be0029fd36257168adef5` |

The support and numerical modules match their previously completed
independent reviews, which are reused without repeating those audits.
The other five modules were read in full at their frozen revisions.
Relevant existing graph and mathlib definitions were inspected directly
where required to establish the meaning of the endpoint.

## Exact final quantifiers and transparent properties

The final theorem has parameters `C A : Real`, hypotheses `0 < C`
and `0 <= A`, and an arbitrary natural `K`. It returns a natural `k`
with `K <= k`, `2 <= k`, `FamilyProperties k`, and, at every actual
vertex `v`,

`C * Real.rpow (Real.log (Fintype.card (FamilyVertex k))) A`
`< ((familyGraph k).degree v : Real)`.

`FamilyProperties` at integration lines 124-130 is a transparent
conjunction: actual connectedness, bipartiteness, the explicit total
vertex count, degree `3^k` at every vertex, absence of any actual
`Walk.IsCycle` of length four, and `OneRoundBarrier` for the actual
family field. It is not a hypothesis supplied by the theorem caller.
`family_properties` constructs each conjunct before the final theorem
uses it.

`OneRoundBarrier` at lines 50-69 is also transparent. It includes:

- Full canonical coloring of the actual full graph.
- Every distinct pair `a,b` of canonical colors.
- Every `J : Set (twoFactor canonical a b).ConnectedComponent`,
  without cardinality or changed-edge restriction.
- Full coloring after that actual swap.
- For every distinct resulting pair `i,j` and every resulting actual
  factor component `D`, a closed factor walk that is an `IsCycle`
  and has `p.toSubgraph.verts = D.supp`.
- For every resulting factor cycle, exclusion of an unrestricted
  original-host cycle with the same actual support and disjoint
  actual edge set.

No desired closure, degree-at-most-three condition, detector-failure
premise, favorable component selection, or cycle-existence hypothesis
is left for the final theorem caller to assume. The negative cycle
clause even permits equal resulting labels; it does not lose any
distinct-label cycle required by the contract.

## Literal finite-field family, counts, and nonemptiness

`FamilyField k` is the actual `GaloisField 3 k`, not an arbitrary field
whose required size is assumed. The imported primary library definition
in `Mathlib/FieldTheory/Finite/GaloisField.lean:69` is a splitting field
over `ZMod 3`; it supplies Field, CharP, Algebra, and Finite instances.
The module proves the prime-three Fact with kernel-checkable `decide`,
then obtains Fintype and DecidableEq without extra caller assumptions.
The library's cardinality theorem requires `k != 0`; `2 <= k`
discharges that condition explicitly.

The vertex type is literally `(FamilyField k × FamilyField k) × Bool`.
The graph is `Parabola104.fullGraph` on that type. The inspected
`Haar.graph` definition has an edge between `(X,false)` and `(Y,true)`
exactly when `Y-X` belongs to the supplied translation set. It has
the symmetric reverse-shore case and no same-shore edges. Symmetry
and looplessness are fields of that actual SimpleGraph definition.
The translation set is all `(a,a^2)` with `a` in the family field.
Color zero connects distinct vertices on different shores; it is
not a loop.

`field_card` proves field cardinality `3^k`. `vertex_card` computes
the product with both field coordinates and Bool and proves exactly
`2 * 3^(2*k)`. The graph's degree is proved to be the cardinality of
the actual color set, hence `3^k`. The legacy `HaarDegree` source was
inspected: on the false shore it uses the bijection `s -> X+s` on
the true shore, and on the true shore it uses `s -> X-s` on the false
shore. Point injectivity removes image-cardinality loss.

The field and vertex types are nonempty. The palette contains distinct
colors such as zero and one because it is a field. Thus the universal
component-cycle clauses are not vacuous because of an empty host,
empty palette, or lack of distinct colors. Since `K` is arbitrary and
the proven count and degree are powers of three, the family is
unbounded in actual order and degree, not only in a redundant label.

## Prime-field algebra and exact component reachability

The algebra module defines the literal point `(a,a^2)`, proves its
injectivity, and proves the pair-sum identity allowing repeated
parameters. The proof uses that two is nonzero in characteristic
three. Its zero triple-sum identity and the nine scalar possibilities
over `ZMod 3` prove `point_span_pair` with duplicates allowed. The
span is over the prime field, not over the full extension field.
This is the exact affine-closure statement required for palettes
of one, two, or three colors, including cases represented by repeated
entries in a triple.

`span_range_point_eq_top` is proved rather than assumed. It obtains
vertical square vectors from points at `a` and `-a`, all vertical
vectors from the characteristic-three difference-of-squares identity,
and all horizontal vectors by subtraction from a parabola point.
Their sums give the entire product. No finiteness, connectivity, or
desired graph property is an input to this algebra proof.

`HaarComponents104.differenceSpan` is the `ZMod 3` span of actual
color differences. One direction of `reachable_iff_mem_differenceSpan`
tracks the shore-offset difference along actual edges and the reflexive
transitive reachability relation. The reverse direction realizes
each generator by two actual edges, concatenates walks for sums, and
handles all three scalars for scalar multiples. A final actual edge
of the chosen base color reaches the full right-shore coset.
The theorem requires the base color to belong to the palette and
does not infer original reachability from a contracted or quotient
walk. Its exact two-shore criterion is the one used by the graph
module.

## Actual canonical coloring and induced color components

The inspected mathlib definition of `EdgeLabeling G C` is a function
from the actual undirected edge set of `G` to `C`. Its `get` reads
that label on the actual edge `s(u,v)`; `labelGraph c` contains
exactly the host edges with label `c`. These are not partial labels
or labels on an abstract auxiliary graph.

`Parabola104.canonical` reads the first coordinate of right minus
left, independently of edge orientation. `canonical_label_cross`
proves that color `a` is precisely the translation by `(a,a^2)`.
`canonical_labelGraph` treats all four shore combinations and gives
the exact singleton-color graph. `canonical_full` explicitly supplies
the unique neighbor on each shore. `canonical_colorSubgraph` identifies
the union of actual canonical label graphs with the translation graph
for every finite color set.

For any nonempty palette of size at most three,
`three_color_component_induced` proves

`(graph T).Reachable u v -> fullGraph.Adj u v -> (graph T).Adj u v`.

The proof represents the palette as a triple, allowing repeats; uses
the actual component reachability criterion; and applies the proved
prime-field span closure to an internal full-host edge's actual color.
It handles the reversed opposite-shore case by symmetry and rules
out both same-shore cases by the literal host adjacency. It therefore
controls all internal full-host edges on both shores, not only the
edges selected by a witness cycle.

`graph_degree` simultaneously gives degree `T.card` at every vertex.
The empty-palette issue is not hidden: the inducedness theorem requires
nonemptiness, and the Kempe palette theorem supplies it explicitly.

## Connectedness and C4-freeness

The full-color difference span at color zero is proved to be top using
the algebra module. The reverse reachability theorem reaches every
actual vertex from `(0,false)`, yielding actual Connectedness. This
argument supplies both shores and the nonempty witness required by
Connectedness; it is not only a claim about a quotient or span.

The graph module uses the proved pair-sum identity to show that two
distinct vertices on one shore have at most one common neighbor on
the other. It proves the corresponding statement for the other shore
and then checks all Bool cases in `common_neighbors_unique`.
`fullGraph_no_four_cycle` takes an actual `Walk.IsCycle`; a hypothetical
length four supplies distinct vertices at positions zero/two and
one/three, with the actual four consecutive edges including the closing
edge. Common-neighbor uniqueness contradicts the second distinctness.
Thus the endpoint's C4 condition is absence of actual simple
four-cycles, not a differently named pattern or only an initial-color
restriction.

## Arbitrary legal component-union swaps

`Selected` uses membership of `connectedComponentMk v` in the arbitrary
set `J`. The inspected library defines ConnectedComponent as the
quotient by actual Reachable, with component equality equivalent to
that reachability. The quotient is used only to index which actual
components are selected; cycle supports remain actual vertex sets.

At a selected vertex the operation applies `Equiv.swap a b` to the
actual old edge label. For an edge with old color `a` or `b`, its
endpoints belong to the same actual two-color component, so selection
agrees at both endpoints. For any other old color the transposition
fixes the label, whether or not selection agrees. This proves endpoint
symmetry and defines an actual EdgeLabeling of the same host.

The selected and unselected `labelGraph` lemmas show exactly which
old color supplies a new color at each vertex. They prove FullColoring
for every set `J`. There is no restriction to one component, bounded
support, bounded number of changed edges, or a graph-specific legal
selection hypothesis. Both the empty and whole component collections
are included.

`swap_empty` proves exact equality with the original labeling. Since
the family has distinct colors, the endpoint's universal distinct
swapped-pair quantifier can be instantiated with zero and one and
`J = empty`. Its cycle and no-partner clauses therefore include the
canonical initial coloring. This inclusion is not only an informal
statement in a comment.

## Actual component cycles and nonvacuity

The generic module proves that every vertex has a neighbor in a
two-color factor and that for distinct labels its neighbor set has
exactly two elements. Distinctness uses the fact that an actual edge
has one label. It does not rely only on the weaker library IsCycles
property, which by itself allows isolated vertices.

The library theorem
`IsCycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp`
was inspected with its Finite-vertex and nonempty-neighbor hypotheses.
The module supplies both hypotheses and obtains a genuine closed walk
that is an IsCycle, spanning each actual component support. In the
library, `p.toSubgraph.verts` is exactly the set of vertices in
`p.support`, by `Walk.mem_verts_toSubgraph` and `verts_toSubgraph`.
Thus the existential in `OneRoundBarrier` is an actual connected
factor-cycle witness, not a surrogate component token.

The proof applies this to the full coloring after every legal swap,
every distinct resulting color pair, and every resulting component.
The original components selected by `J` have the same cycle-witness
property from the canonical full coloring. No component is discarded
by the definition of the move or the exposure family.

## Three-color containment and faithful partner exclusion

`canonicalPalette a b i j` explicitly handles the three cases: neither
resulting label is switched; one is switched; or both are switched.
The possible old colors are the new labels and their images under
the same transposition. The supplied Finset has at most three colors
and contains an actual label, so it is nonempty.

`twoFactor_swap_le_colorSubgraph` proves an inclusion of actual graphs:
every actual edge of the resulting factor belongs to that union of
canonical label graphs. It does not merely bound a list of color
names. The integrated `exposed_cycle_no_partner` rewrites the union
as `Parabola104.graph T`, maps the actual factor cycle into it by
graph inclusion, and proves that mapped walk is still a cycle.

It then discharges every premise of the already reviewed support
helper: inclusion in the literal full host, actual induced component
closure, and degree at most three. The only remaining operation is
rewriting `Walk.support_mapLe_eq_support` and
`Walk.edges_mapLe_eq_edges`, so the conclusion compares the original
exposed cycle's actual support and actual undirected edges in the
original host.

The partner `q` is any original-host closed walk that is an IsCycle,
with any base vertex. It has no color, reachability-state, component,
or exposure restriction. The equal-support and disjoint-edge Finset
conditions are exactly the faithful `HasPairF` conditions checked in
the earlier support review. No spanning-host condition excludes
proper supports.

Consequently a cycle from another allowed resulting state, even from
a different swapped pair or component selection, cannot be a faithful
mate on the same support. It is an original-host cycle and is already
covered by the unrestricted partner quantifier. A separate weaker
same-state formulation has not replaced this cross-state consequence.

## Exact quantitative integration

The previously accepted numerical module supplies the estimate for
all positive real `C`, nonnegative real `A`, and arbitrarily large
natural `k >= 2`. `family_ledger_exceeds_polylog` rewrites its literal
`2 * 3^(2*k)` and `3^k` using the actual vertex and field cardinalities,
including the natural-to-real casts. The final theorem rewrites the
actual graph degree to the field cardinality at every vertex.

Thus the inequality is attached to the same actual graph that has
the structure and detector properties. There is no independent
numerical witness or abstract size variable disconnected from the
family. The logarithm argument is positive, the field and graph are
nonempty, the exponent is a genuine real power, and the strict
inequality and arbitrary lower bound `K` survive integration.

## Paper, source, and result boundary

The implementation matches the accepted color-closure addendum
`paper103/radius/COLOR-CLOSURE.md`, SHA-256
`0f8ab500ef3577e61c18fa204321642278290304fb79242dbaf1a88fa892e637`,
and the unchanged main paper's family/count/connectedness/C4/growth
claims. It implements the stronger one-whole-two-class-transformation
scope, not merely one move changing a bounded number of edges.
The unnecessary six/eighteen-cycle classification is not used.

The already accepted root source reviews were read only to retain
their boundary, without repeating literature research. They credit
the classical ternary affine/Sidon ingredients and the saved earlier
method obstructions. They do not establish historical priority for
this assembled detector statement. The formal endpoint makes no
additional literature or priority claim. Its proof does not assume
Hamilton decomposability, regular-subgraph extraction, or full graph
avoidance. Existing H4 positivity remains outside this implementation's
claimed credit.

The accepted endpoint concerns the supplied canonical coloring and
one transformation on a fixed pair, with arbitrarily many component
swaps. It gives no theorem about two successive transformations
using different pairs, every possible starting coloring, all supports
of the host, global graph avoidance, KS102, or an improved extremal
growth bound. It is the authorized further method-barrier endpoint.

The seven inspected sources contain explicit proofs; no new local
axiom, sorry, admit, or native_decide was found. Final axiom checking
and `RESULT: PASS` belong exclusively to root's check.sh run. The
reviewer made no proof edit, compilation, oracle call, mathematical
experiment, nested-agent request, public action, or task-tracker change.
Only the assigned review directory was written. The independent
faithful-endpoint review is complete at the exact frozen hashes above.
