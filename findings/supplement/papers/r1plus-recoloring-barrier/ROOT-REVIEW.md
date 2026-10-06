# Independent review of root's radius-one proof

October 4, 2026. Accept the mathematical R1 statement and proof
unchanged. No gap or correction was found. This review was completed
and recorded before reading the separate adversary proof.

Accepted radius/PAPER.md SHA-256:
`dd8912d9c9139c0cfd56f5a9cfe1685e7c7bbac4e92f08f632aac5d8e0f30c60`.
The exact initial bytes are preserved in root-PAPER.initial.md.
STATE.md was snapshotted at
`ff98609c34689e578a406080835ec3910f2e35028bcf59959e8e41733c9cb5c7`.

Acceptance here concerns the literal graph and every initial or
one-move bichromatic component. Historical priority, useful-method
classification, formalization authorization and project-oracle status
remain separate gates owned by root. This is not graph avoidance,
a bound on f(n), or a counterexample to unbounded-radius KS102.

## 1. Accepted quantified statement

For every integer k>=2, take q=3^k and the specified two-shore
translation graph over F_q^2, with its specified q-coloring. The
graph is connected, simple, bipartite, C4-free and q-regular, with
exactly 2q^2 vertices. Every actual bichromatic component in the
initial state or any state obtained by one legal component swap
has support S with maximum_degree(G[S])<=3.

The detector includes every choice of first color pair and component,
then every color pair and every component in each resulting state.
It may compare actual cycles from different such states. Radius one
is measured from the fixed canonical coloring; it is not the closure
under further moves. The graph itself and its original edges remain
unchanged throughout.

The proof actually gives a sharper classification: initial and
unaffected components are six-cycles whose supports induce degree
two; each affected third-color factor has one eighteen-cycle whose
support induces degree three. These support restrictions suffice to
exclude a faithful pair even if only one of its cycles is detected.

## 2. Field, graph and both-shore coloring

The construction uses a field of order 3^k for every k>=2. Standard
finite-field existence supplies these fields. All subsequent formulas
work over any such field, with no choice of special primitive element,
irreducible polynomial or numerical sample. The resulting graph is
given explicitly by its adjacency formula once the field is fixed.

The color vectors v_a=(a,a^2) are distinct because their first
coordinates distinguish a. In the two disjoint vertex copies,
L(X)R(Y) is an edge exactly when Y-X is one of these vectors.
Each left vertex has the q distinct neighbors X+v_a. Each right
vertex has the q distinct neighbors Y-v_a. Thus both shore degrees
are q, each color is a bijective translation matching, and the
matchings partition the actual edge set. The two disjoint copies
prevent v_0=0 from creating a loop. There are 2q^2 vertices and q^3
edges, all simple bipartite edges.

The comparison with incidence coordinates is faithful. Because 2 is
invertible in characteristic three, both displayed coordinate maps
are bijections on their own shores. Under y=mx+b,

    (2b+m^2)-(2y-x^2)=(m-x)^2.

Together with the first-coordinate difference m-x, this gives the
same vector v_a with a=m-x. This changes labels, not adjacency or
the identity of a graph edge. No quotient is used.

The additive subspaces in the proof are over F3, not F_q. Nonzero
translations have additive order three even when q is much larger
than three. This distinction is retained in every orbit calculation.

## 3. Every affine relation on at most four colors

Suppose v_a+v_b=v_c+v_d. Equality of the first coordinates gives a
common sum, and equality of the second coordinates gives the same
product because 2ab=(a+b)^2-a^2-b^2. Thus the unordered pairs are
the same as multisets. This reasoning allows repeated entries; no
unstated distinctness is needed for this preliminary identity.

Three distinct points on an affine F3-line have sum zero. Applied
to three color vectors, this would give c=-a-b and

    a^2+b^2+(a+b)^2=2(a-b)^2=0.

The identity holds in characteristic three. A field has no nonzero
square equal to zero, and 2 is nonzero, so it forces a=b. Hence
three distinct colors are not affinely collinear. In particular the
two nonzero difference vectors from any one of them to the other
two are F3-linearly independent.

For an affine dependence on four distinct color points, pass to its
nonzero coefficient support. One nonzero coefficient cannot sum to
zero. Two would force equality of their distinct points. Three were
just excluded. Thus a minimal dependence would have four nonzero
coefficients, each 1 or -1 in F3. Their integer sum is one of
-4,-2,0,2,4; only zero vanishes modulo three. There must be two
coefficients of each sign. The resulting equality of two disjoint
pair sums contradicts the preceding multiset identity.

This accounts for zero coefficients as well as full four-element
support. Every affine F3-plane contains at most three color vectors,
and every affine F3-line at most two. All dimensions here are over
the prime field; no F_q-dimension inference is substituted.

## 4. C4-freeness and connectivity

For a proposed four-cycle with distinct left vertices X,X' and
distinct right vertices Y,Y', assign

    Y-X=v_a,   Y-X'=v_b,
    Y'-X=v_d,  Y'-X'=v_c.

Then v_a-v_b=v_d-v_c=X'-X is nonzero. The pair-sum identity permits
only a=b and c=d, contradicting that nonzero difference, or a=d
and b=c, which forces Y=Y'. Thus no actual four-cycle exists.

Connectivity is also proved on the literal graph. The two-edge walk
using a followed by 0 translates a left vertex by v_a. Such walks
therefore realize the additive F3-span of the color vectors. The sum
v_a+v_-a=(0,2a^2), followed by multiplication by 2 in F3, puts every
(0,a^2) in that span. Every field element is a difference of two
squares by the displayed identity, so every (0,z) is in the span.
Subtracting (0,a^2) from v_a gives every (a,0). Hence the span is all
F_q^2, every left vertex is reachable, and color 0 reaches every
corresponding right vertex. Walk reachability is sufficient for
connectedness; no Hamiltonicity theorem or contraction is invoked.

These arguments prove the required growing-degree, bounded-biclique
host conditions, rather than assuming them from the older graph name.

## 5. All initial components and their induced edges

For any distinct a,b, w=v_b-v_a is nonzero. The alternating left
permutation translates by w or its inverse. Its order is exactly
three, so its orbits are precisely the additive affine lines
ell=X_0+F3 w. Both matchings are bijections, and their edges are
distinct, so each orbit corresponds to one connected simple six-cycle.
The full right support is ell+v_a=ell+v_b.

For a left vertex X in ell, its color-z edge lands in this right
support exactly when v_z-v_a belongs to F3 w. This condition is
independent of X. It admits just a and b by the affine-line result.
Conversely each admitted translation maps the entire left line
bijectively onto the entire right line. Consequently both shores
have induced degree exactly two. Counting only the selected cycle
edges would not have sufficed, but the proof excludes all extra host
colors and therefore all possible chords.

The argument covers every component of every initial color pair,
not a chosen representative.

## 6. Legal first swap and exhaustive color-pair cases

Choose any a,b and any of their initial components, with left support
ell. Its two matchings have the same right image. Exchanging their
maps on ell preserves bijectivity on both shores, because their old
restrictions outside ell both map onto the complementary right set.
The displayed T'_a and T'_b formulas therefore make a legal proper
recoloring on exactly that component. No host edge or palette color
is added or removed.

The post-move color pairs fall into three exhaustive cases:

* A pair using neither a nor b is unchanged.
* The pair a,b has unchanged union, hence unchanged actual components.
* A pair using exactly one of a,b and an arbitrary other color c is
  governed by the two calculations below.

The first two cases have all the original supports and induced-degree
bounds. Swapping the order of a color pair reverses an alternating
traversal but leaves its undirected component edge set unchanged.

## 7. Exactly one changed color: all inside and outside orbits

For a,c, put u=v_a-v_c and w=v_b-v_a. The noncollinearity of the
three color points makes u,w F3-linearly independent. Thus
U=span_F3{u,w} has nine elements, and Pi=X_0+U is a nine-point
affine plane. The left permutation is exactly

    sigma(X)=X+u+w 1_ell(X).

It preserves Pi. Modulo F3 w, addition of u has order three, so
each three consecutive steps visit the three quotient classes once,
including the class ell exactly once. Summing all increments yields
sigma^3(X)=X+w for every X in Pi.

A return time must be a multiple of three by quotient motion. At
time 3j the displacement is j w, because the three-step identity
holds for every starting point. Its first positive zero is at j=3.
Conversely sigma^9 is the identity. Each orbit in Pi therefore has
length nine; since Pi has only nine points, it is one orbit.

The corresponding right support is initially described by the
unchanged matching c as Pi+v_c. Since v_a-v_c=u lies in U,

    Pi+v_c=Pi+v_a.

Thus the asserted eighteen-vertex support includes exactly the correct
right vertices. The two distinct perfect matchings on this orbit form
one simple eighteen-cycle, not several cycles or an Eulerian walk.

If X lies outside Pi, its entire old translation orbit X+F3 u
avoids ell; otherwise subtracting a multiple of u would put X in Pi.
Hence the switch indicator is zero along that whole orbit. The new
permutation there is the old translation by u, with its old three-point
orbits and old six-cycle supports. It cannot enter Pi. The matching
edges and right supports of these components are also unchanged.
This proves the classification for every outside component.

For b,c, use u'=v_b-v_c=u+w and the perturbation -w. They span the
same U and give the same Pi. The quotient argument gives three-step
displacement -w, again one orbit of length nine in Pi and unchanged
length-three orbits outside it. Its right support is also Pi+v_c,
equal to both Pi+v_a and Pi+v_b. Both switch signs and every third
color have therefore been covered.

## 8. All induced host edges on the eighteen-vertex support

The selected left set is Pi=X_0+U and the selected right set is
Pi+v_a. For every left vertex in Pi, a color-z edge stays in these
sets exactly when v_z-v_a belongs to U. Again this condition is
independent of the chosen left vertex.

The affine color plane v_a+U contains v_a,v_b,v_c. The four-color
independence result excludes every other color vector. Each of the
three admitted translations maps Pi bijectively onto Pi+v_a.
Accordingly every selected left vertex has exactly three induced
neighbors, and every selected right vertex has exactly one preimage
from each of the same three colors. Those preimages are distinct
because the color vectors are distinct. Both shores have degree three.

The calculation uses the original host color decomposition only to
enumerate its uncolored edge set. The induced-degree conclusion is
therefore independent of the post-switch color names. Together with
the original six-cycle cases, it proves R1 for every component after
every legal first move and for every initial component.

## 9. Cross-state collision exclusion and exact asymptotic ledger

Two simple cycles with the same actual support and disjoint actual
edge sets contribute four distinct incident edges at each support
vertex. Their common induced host must have minimum degree at least
four. Every support arising in the declared detector family has
maximum induced degree at most three. This contradiction applies if
even one of the cycles is detected; the second cycle need not be
bichromatic in any state. In particular all comparisons between
different initial/one-move states are excluded without identifying
color names across those states.

For k>=2, the graph has degree 3^k and order N_k=2*9^k. The logarithm
identity is exact, and log_2 3<2 gives

    log_2 N_k=1+2k log_2 3<=5k.

For every fixed real exponent a>=0 and every fixed C>0, the successive
ratio of 3^k/(5k)^a is 3(k/(k+1))^a, tending to three. It is eventually
greater than two, so the sequence diverges. Hence for all sufficiently
large k, degree 3^k exceeds C(log_2 N_k)^a. The case a=0 is included.
Changing the fixed logarithm base only changes the constant.

The infinitely many resulting graph orders suffice to refute a
guarantee asserted for every host above any such threshold. The same
graphs remain connected, C4-free and regular, and the same canonical
colorings retain the complete radius-one exclusion. No numerical
instance, heuristic scaling or parameter-dependent threshold constant
is substituted for the universal comparison.

## 10. Scope, gaps and review verdict

No missing color-pair case, outside orbit, right support, affine
dependence, induced host edge, cycle-connectedness requirement or
quantifier loss was found. No correction is requested. The mathematical
R1 candidate is accepted at the exact initial hash recorded above.

The detector is restricted to the supplied canonical coloring and
at most one legal component switch. A different starting coloring,
a different trade, further switches or cycles outside the detected
supports are outside this theorem. The full host is not certified
pair-free. Unbounded-radius KS102 is neither refuted nor reopened.
No estimate for f(n) or new avoiding construction follows.

The characteristic-three calculation is compatible with the earlier
prime-field one-switch positive control: its additive translation
orbits have size three, not q. No k=1 degree-three case is credited;
the theorem's degree grows through q=3^k with k>=2.

Historical novelty and comparison against already banked method
barriers remain the separately assigned source review. This review
alone confers no project `RESULT: PASS`, formalization permission or
completed growth goal. The finite-field graph formulas and all orbit
calculations were checked symbolically, without mathematical
computation, a sampled graph, finite enumeration, Lean or oracle.
The separate frozen adversary is reviewed next, without changing
this root-proof audit's independent mathematical record.
