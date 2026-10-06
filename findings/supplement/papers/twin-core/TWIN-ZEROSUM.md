# Mixed-modulus selection forces an actual pair in twin quotients

October 3, 2026. Complete written proof, independently reviewed. This lane
owns only this note and `twin-zerosum/`. No Lean, oracle, computation, Git or
public action. No novelty claim. The exact object remains an actual simple host
and two actual edge-disjoint simple cycles with identical full vertex support.

## 1. Primary theorem checked before use

Read directly: Alon, Friedland and Kalai, *Regular subgraphs of almost regular
graphs*, printed p.81, Theorem2.1, and printed pp.81–82, Corollary2.2:

https://web.math.princeton.edu/~nalon/PDFS/Publications/Regular%20subgraphs%20of%20almost%20regular%20graphs.pdf

Theorem2.1 says that a sequence of integer vectors has a nonempty subsequence
whose j-th coordinate sum is divisible by p^(d_j), provided its length exceeds
sum_j(p^(d_j)-1), where p is prime and the positive exponents are sorted. Thus
for the abelian group C4^g x C2^r the sufficient strict threshold is 3g+r.
This is a primary source statement, not a claim of a new zero-sum theorem.

Incidence vectors enjoy one extra parity relation. Each has one group coordinate
and one right coordinate equal to one, so the sum of all coordinates is even.
The kernel of total parity in C4^g x C2^r, for r>=1, is isomorphic to
C4^g x C2^(r-1): drop one right coordinate and reconstruct it as the sum modulo
two of the remaining coordinates. Consequently the threshold improves to
3g+r-1. This also follows from the source's Corollary2.2. Section3 gives the
needed special case by an elementary Boolean polynomial proof.

The resulting selection is then lifted by the actual Euler/twin construction
already checked in TWIN-CORE.md and TWIN-REVIEW.md. The algebra selects a smaller
quotient subgraph, not a formal coloring of cycles. Thus it does not encounter
the equivariant faithful-pair counting obstruction in ALGEBRA.md.

## 2. Quotient selection lemma and exact host theorem

Let J be a finite simple bipartite graph with group shore X and right shore Y,
where |X|=g, |Y|=r>=1. Suppose

    degree_J(x)<=6 for x in X,
    degree_J(y)<=3 for y in Y,
    m=|E(J)| > 3g+r-1.                                  (1)

**Selection lemma.** There is a nonempty edge subset K of J in which every group
vertex has selected degree zero or four and every right vertex has selected
degree zero or two.

To apply this inside a host G, suppose each x represents a distinct group of at
least two actual left vertices with the same neighborhood, groups are disjoint,
and xy in J means every original vertex in group x is adjacent to y in G. The
groups may be pairs or triples; the selection lemma itself needs only the stated
quotient degree caps.

**Host theorem.** Under these premises G contains the faithful pair on an actual
support, which may be proper. It is not claimed that the resulting cycles extend
to spanning factors of the entire host.

## 3. Complete polynomial proof of the selection lemma

Give every actual edge e of J a variable x_e in F2. No auxiliary variables or
Boolean-domain equations are needed. At a group vertex v define

    L_v = sum_{e incident to v} x_e,
    Q_v = sum over UNORDERED TWO-ELEMENT subsets {e,f} of incident edges of x_e*x_f.

The degrees of these polynomials are at most one and two. For an assignment
selecting k incident edges, their values are k modulo two and binom(k,2) modulo
two. For 0<=k<=6 both vanish precisely when k=0 or k=4. Indeed for even k in
this range, k=0,2,4,6, the binomial residues are respectively0,1,0,1; odd k is
excluded by L_v.

Choose one right vertex y0 and impose L_y=0 at all other right vertices. Together
with L_v=Q_v=0 at every group, the sum of equation degrees is at most

    3g+(r-1) < m.                                       (2)

The omitted right equation holds automatically: the sum of all group L_v equals
the sum of all right L_y because each edge appears exactly once on each side.
Thus every right selected degree is even, hence zero or two under its cap three.

Here is the entire zero-count argument. For all imposed polynomials f_i, form

    P(x) = product_i (1+f_i(x)) over F2.

On F2^m this equals one exactly at common zeros. Its degree is less than m by
(2). Every monomial of total degree below m omits at least one variable. Summing
it over F2^m gives zero, since summing the constant one over the omitted variable
gives 1+1=0. Therefore the number of common zeros is even.

The all-zero assignment is one common zero, because every imposed polynomial has
zero constant term. There must be another. It selects a nonempty actual edge set
K, and the local count calculation gives exactly the degrees claimed. This
proves the selection lemma without using a general zero-sum theorem as a black
box. It is the appropriate specialization of the source method, not a new
Chevalley–Warning theorem.

Optional refinement, not needed below: one may omit one right equation in EACH
nonempty connected component. The same parity argument inside each component
then gives the sufficient threshold m>3g+r-c after discarding isolated vertices,
where c is the number of components.

## 4. Proof that the selected actual edges give the faithful pair

Take a connected component of K containing an edge. Discard vertices of selected
degree zero. Every remaining right vertex has two distinct group neighbors,
because J is simple. Suppress that right vertex to a separately labeled edge
between those two groups. No loop is created. Distinct right vertices may become
parallel edges and retain their distinct labels.

The resulting multigraph M is nonempty, connected and four-regular. It has an
Euler circuit: an unused-edge walk cannot stop away from its start because every
degree is even; closed trails can be spliced until all edges are covered. In the
cyclic traversal each group occurs twice, since its four incident edges give
two arrivals and two departures.

Choose two distinct original vertices in each active group and assign them
bijectively to its two occurrences. Reinsert each suppressed right vertex between
the endpoints of its labeled edge. Each chosen left vertex occurs once, and
each right label occurs once. Every consecutive pair, including the closing
pair, is an actual G edge by the complete-neighborhood premise. Thus this is one
actual simple cycle C.

Swap the chosen two vertices inside every active group and fix all right
vertices. Equal neighborhoods ensure that the image C' is another actual simple
cycle, with exactly the same support. At a right vertex, C uses one vertex from
each of two distinct groups; C' uses the other chosen vertex from each. Hence
none of its two incident edges is shared. This holds at every right vertex, so
the two cycles are edge-disjoint.

A loopless four-regular component has at least two group vertices and four
edge labels. Thus the lifted cycles have at least eight vertices; no degenerate
two-edge closed walk is being counted as a simple cycle. Extra unused group
vertices and host edges have no effect on either cycle's correctness.

## 5. Six-regular hosts with at most two singleton twin classes

Let G be a nonempty finite simple six-regular bipartite graph with shores A,Y.
The shores are balanced by summing degrees. Partition A into its maximal actual
equal-neighborhood classes. A class of size at least four immediately gives
K4,4 using any four of its six common neighbors, hence the faithful pair. It
remains to handle classes of size two or three and singleton classes.

Let their counts be p,q,s respectively. Collapse the nonsingleton classes and
omit the singleton left vertices, retaining all original right vertices. The
resulting J satisfies

    g=p+q,    r=|Y|=|A|=2p+3q+s,    m=6(p+q).

Each group degree is six. Every incidence to a right vertex accounts for at
least two original neighbors, so its quotient degree is at most three. Thus

    m-(3g+r-1) = p-s+1.

**Threshold corollary.** If p>=s, the strict inequality(1) holds and G contains
the faithful pair. This improves the uncorrected p>s count by retaining the
global parity dependency. The collapsed graph is nonempty in these cases: if
p=q=0, then p>=s would force an empty left shore, contradicting the host.

**At-most-two-singleton corollary.** Every such six-regular G with s<=2 contains
the pair.

For s=0 the threshold is automatic. For s=1, take any of the singleton's six
neighbors. Its remaining five original neighbors must be unions of size-two
and size-three classes. The only possible partition of five is2+3, so p>=1=s.

For s=2, suppose p<=1. A right vertex adjacent to both singletons would have four
remaining neighbors from whole nonsingleton classes. This requires two DISTINCT
size-two classes; one cannot use the same class twice. Thus the two singleton
neighborhoods are disjoint. Every neighbor of either singleton then has remaining
weight five, so it must be adjacent to the unique pair class. If p=0 this is
already impossible. If p=1, that pair class must have at least twelve distinct
neighbors, contradicting its degree six. Therefore p>=2=s, and the threshold
applies.

With exactly one singleton, maximality actually rules out p=1: all six singleton
neighbors would also be the six neighbors of the unique pair class, making the
singleton a member of that same maximal class. This strengthening is correct
but not needed for the threshold argument.

No at-most-three-singleton conclusion is claimed. The local weighted degree
equations can permit p=1,s=3, below the sufficient threshold. Arithmetic
feasibility is neither a constructed avoider nor a proof that forcing fails.

## 6. Exact capped critical cores with no singleton twin class

Let H satisfy the actual common core contract

    e(H)=3|V(H)|-2,
    e(H[S])<=3|S|-3 for every nonempty proper S,
    Delta(H)<=6,

and suppose H is bipartite and one shore A has no singleton maximal twin class.
As checked in TWIN-CORE.md, the shores are balanced, each has nonnegative
degree-six deficit two, and minimum degree is at least four.

A class of size at least four has at least four common neighbors and directly
supplies K4,4. Otherwise all classes have sizes two or three. Since class
members have equal degree, their contribution to the left deficit is their
size times their common deficit. The only way to total two is exactly one
size-two class of degree five. All remaining classes have degree six. In
particular p>=1.

The quotient after collapsing these classes has

    g=p+q,    r=2p+3q,    m=6(p+q)-1,
    m-(3g+r-1)=p>0.

Its group degrees are at most six; right degrees are at most three because
every class has size at least two. The selection lemma and actual lift force
the faithful pair. This gives an independent algebraic proof of the no-singleton
core forcing conclusion in TWIN-CORE.md, with a possibly proper support and no
spanning-exposure claim.

The more detailed profile identity from that paper forces p>=3: it gives
n222=2p-1>0, and a right vertex of type222 needs three distinct pair classes.
That identity is consistent with this proof, but the parity-improved algebraic
threshold already works with p>=1 and does not need it.

## 7. Saved controls and exact remaining scope

* The zero-sum subset consists of actual incidence edges. The degree caps turn
  modular statements into exact degrees before the Euler lift.
* The Euler lift proves two connected actual cycles on identical support. A
  four-factor or an arbitrary even subgraph is not substituted for that proof.
* Proper supports and unused third clones remain available. No conclusion
  about every spanning four-factor, and no Paper66 exposure assumption, is used.
* No cover, smoothing, artificial completion, or projected-walk inference is
  involved. Parallel edges arise only in the intermediate labeled multigraph;
  their distinct right vertices keep the lifted host cycles simple.
* ALGEBRA.md's characteristic-three symmetry barrier counts faithful pairs
  themselves with specified witness fibers. This proof counts quotient edge
  subsets in characteristic two and performs the cycle construction afterward.
  Its hypotheses are different and its counts need not share that obstruction.
* The degree cap and twin premise are essential to the stated proof. The
  irregular high-degree avoiding family from Paper90 does not meet these
  premises. Twin-free cores and six-regular hosts outside the sufficient class
  remain unresolved.

The paper proves restricted forcing, not a new avoiding-degree record or a
general upper bound for f(n). Root decides whether its complete reviewed proof
justifies Lean under the current forcing-only rule. No project result exists
until the required oracle reports PASS.

Independent review: [TWIN-ZEROSUM-REVIEW.md](TWIN-ZEROSUM-REVIEW.md).
