# Root review of the new forcing statements

October 3, 2026. This review concerns the newly implemented statements. It is
not a rerun of older mathematical audits or a novelty assessment.

The unchanged definition in `Openmath/Target.lean` requires two actual closed
walks satisfying `IsCycle`, equality of their full support sets, and disjoint
edge lists. Every endpoint below concludes that definition. The compatible
Finset predicate is converted only through the existing proved equivalence.

## Selected incidence and actual lift

`TwinZeroSum.exists_nonempty_selected_incidence` takes a finite actual incidence
set, its left cap six and right cap three, a nonempty right type, and the exact
integer threshold `3*|I|+|R| <= |J|`. It constructs a nonempty subset with degrees
zero/four and zero/two. It does not assume a polynomial solution or cycle.
The quadratic polynomial sums unordered two-element subsets, and the omitted
right parity equation follows from the two actual incidence sums. Critical91's
independent implementation review found no gap.

`TwinDoubleCycle.hasPair_of_selected_incidence` constructs the initial cycle
factor, then minimizes its finite component count over legal clone assignments.
A switch between separated clones merges their components and preserves every
old reachability. It therefore leaves each active clone pair in one component.
An actual cycle on a nontrivial component is extracted. Swapping the clones
preserves its whole support; the legal assignment prevents a shared edge.
Inactive isolated vertices are outside the selected support. Switching91's
separate source review found no correspondence gap.

## Counted represented graph and its host map

`TwinCoreForcing.hasPair_of_twin_incidence` takes actual incidences and an
injective map to actual host vertices with both clone adjacencies. It constructs
the selected subset and cycle pair internally. The map preserves simple cycles,
support equality and edge disjointness. No projection or artificial completion
is used.

`groupedGraph_hasPair_of_no_singletons` assumes only group sizes at least two,
maximum degree six, and `e+2=3v` in its explicitly defined graph. Its count
argument proves balanced shores and deficit two. Pair/triple groups meet the
selection budget. A larger group forces an actual K4,4. The endpoint assumes
neither a selected set, a cycle factor, a walk, nor the desired pair.

The statement is stronger than the no-singleton exact-core claim on this
represented class because it does not use proper-subset criticality. It does
not by itself construct the maximal neighborhood classes of an arbitrary
graph. It passed the unchanged oracle; see `verification.json` and
`oracle-grouped-no-singletons.log`.

## Arbitrary graph with typed bipartite shores

Root read the complete `TwinNoSingleton.lean` source. The public statement takes
an actual graph on `A + R`, no same-shore edges, maximum degree six,
`e+2=3v`, and a distinct equal-right-neighborhood partner for every left vertex.
The finite image of the actual neighborhood function names its maximal
classes. The proof enumerates the exact fibers, proves their sizes at least
two, constructs a graph isomorphism, and transports the degree and edge counts
and the resulting faithful pair. No quotient representation is supplied in
the public hypotheses. The typed shores state bipartiteness explicitly.

The complete finite partition argument was written in `lean-partition/PLAN.md`
before implementation. The source compiles; root's final oracle for this
endpoint is pending at this note's creation. Later verification belongs in
`verification.json`, not an inferred PASS from this review.

## Scope retained

These are restricted forcing statements, rung(b) when the specific endpoint
passes check.sh. The degree record remains general five and bipartite four.
There is no unrestricted degree-six forcing theorem or improved growth bound.
The one-singleton and at-most-two-singleton paper corollaries must not be
silently included in the implemented no-singleton endpoint. A common-neighbor
extension is under separate review and implementation ownership.

All new proof modules have no sorry or native_decide. The final axiom check is
transitive. Unrelated admitted research statements in Target.lean are not
used by the checked endpoint. Pins, Final.lean and the oracle were not edited.
