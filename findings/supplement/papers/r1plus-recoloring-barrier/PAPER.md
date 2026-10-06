# Candidate barrier: one Kempe switch cannot force the pair at any polylogarithmic degree

October 4, 2026. Complete written argument submitted for independent
review. Not yet a check.sh result. Historical priority is unestablished;
a primary-source comparison is assigned separately. This is a method
boundary, not an improved bound on f(n) or an avoiding construction.

## 1. Exact method class and theorem

A supplied proper r-edge-coloring of a finite r-regular bipartite graph
partitions its edges into r perfect matchings. An allowed move swaps two
colors on ONE bichromatic cycle component. Let O_1(phi) consist of the
supplied coloring and every coloring obtained from it by at most one such
move. Let C_1(phi) contain all actual bichromatic cycle components in
all these colorings. The class includes every choice of colors and
component and compares cycles from different resulting states.

The one-switch detector succeeds if two members of C_1(phi) have equal
actual vertex support and disjoint actual edge sets. No runtime or cycle
enumeration restriction is placed on the detector. What is restricted is
its reachable coloring radius. Arbitrarily choosing another initial
coloring, using three-color trades, or making two or more moves is outside
this method class.

**R1 candidate theorem.** For every integer k>=2 there is an explicit
connected simple C4-free bipartite graph G_k on N_k=2*3^(2k) vertices,
regular of degree r_k=3^k, with a specified proper r_k-edge-coloring phi_k,
such that every C in C_1(phi_k) has

    maximum_degree(G_k[V(C)]) <= 3.                       (R1)

In particular C_1(phi_k) contains no collision. Indeed no exposed cycle
support can support ANY faithful pair, whether its cycles are exposed
or not. The full graph is not claimed to avoid the pair.

Since r_k grows faster than C(log N_k)^a for every fixed C>0 and a>=0,
there is no sufficient fixed polylogarithmic degree threshold for this
detector to work on every supplied coloring. This does not refute KS102,
whose move class has unbounded radius, or an algorithm that chooses a
different initial coloring by some other argument.

## 2. The literal graph and canonical coloring

Let F be the field of order q=3^k. View V=F^2 as a vector space over its
prime field F_3. Use two disjoint copies L(V) and R(V). Put

    v_a=(a,a^2),  a in F,
    L(X) adjacent to R(Y) iff Y-X=v_a for some a in F.

Color this edge a. Distinct a give distinct v_a, so the host is simple,
q-regular on both shores, has 2q^2 vertices and q^3 edges. Each color
is the translation matching T_a:X -> X+v_a. These are actual host
edges; a change of coloring never changes the graph.

For comparison with the earlier biaffine control, the bijections

    P(x,y) -> L(x,2y-x^2),
    L(m,b) -> R(m,2b+m^2)

send y=mx+b and color a=m-x to the displayed matching. The two vertex
shores remain distinguished. We use additive F_3-lines, not F-lines.
For k>1 these have three elements rather than q elements, which is
exactly the boundary of the prime-field calculation in pass102.

## 3. Affine independence of every four distinct colors

First, v_a+v_b=v_c+v_d implies {a,b}={c,d} as multisets. The first
coordinates give a+b=c+d; the second then gives ab=cd because 2 is
invertible. Thus a,b and c,d are roots of the same monic quadratic.
Equivalently (a-c)(a-d)=0 and the sum fixes the other root.

Three distinct v_a,v_b,v_c cannot be collinear over F_3. Three points
on an affine F_3-line have sum zero. But a+b+c=0 and
a^2+b^2+c^2=0 imply

    0=a^2+b^2+(a+b)^2=2(a-b)^2,

so a=b, a contradiction. In particular the difference vectors of
three distinct color points from any one of them are independent.

Now suppose four distinct color points were affinely dependent over
F_3. Choose nonzero coefficients lambda_i in a minimal dependence,
with sum lambda_i=0 and sum lambda_i v_i=0. Dependences supported on
one or two distinct points are impossible, and support three was
just excluded. Hence all four coefficients are nonzero, each +1 or -1.
Their sum is zero only when there are two of each sign: the possible
integer sums of four signs are -4,-2,0,2,4, and only zero is divisible
by three. This gives equality of two disjoint pair sums, contradicting
the preceding quadratic calculation.

Consequently every affine F_3-plane contains at most three color
points. Every affine F_3-line contains at most two.

The pair-sum calculation also proves C4-freeness. Two distinct left
vertices and two distinct right vertices in a four-cycle would give

    v_a-v_b=v_d-v_c != 0.

The two possible matchings of the pair sums force either a=b or a=d
and b=c. The former contradicts nonzero difference, and the latter
identifies the two right vertices. Thus no four-cycle exists.

## 4. Connectivity of the literal host

Since v_0=0, a two-edge walk through colors a and 0 translates a left
vertex by v_a. It suffices to show the v_a span the additive group V.
The sum v_a+v_(-a)=(0,2a^2) shows that every (0,a^2) is in that span.
Every z in F is a difference of two squares:

    z=((z+1)/2)^2-((z-1)/2)^2.

Thus every (0,z) is in the span. Subtracting (0,a^2) from v_a then gives
(a,0) for every a. Both coordinate directions are available, so every
left vertex is reachable. The color-0 edge reaches the corresponding
right vertex. This proves connectedness without using a Cayley-graph
Hamiltonicity theorem.

## 5. The initial cycle supports have induced degree two

For distinct colors a,b, put w=v_b-v_a != 0. The alternating left
permutation is translation by w or its inverse. In characteristic three,
each orbit is exactly the affine F_3-line

    ell=X_0+F_3 w.

Each bichromatic component is therefore a simple six-cycle, with left
support ell and right support ell+v_a=ell+v_b.

An edge of another color z could occur inside this vertex support only
if v_z-v_a belongs to F_3 w. That would put v_z on the affine color
line through v_a,v_b. Section 3 excludes a third color there. Thus the
entire induced host on this support consists of the two original
matchings and has degree exactly two.

## 6. Complete classification after one component switch

Switch a,b on one component with left support ell=X_0+F_3 w. Its common
right support is ell+v_a=ell+v_b, so the following really are bijections
and a legal proper recoloring on both shores:

    T'_a(X)=X+v_a+w*1_ell(X),
    T'_b(X)=X+v_b-w*1_ell(X).

The union of the two switched color classes is unchanged. Any pair of
colors disjoint from {a,b} is unchanged as well. Their components have
the supports already treated in Section 5.

It remains to examine one switched color and one untouched color c.
For the pair a,c put u=v_a-v_c, and U=span_(F_3){u,w}. Section 3 gives
dim(U)=2. The alternating left permutation after the switch is

    sigma(X)=T_c^(-1) T'_a(X)=X+u+w*1_ell(X).

Put Pi=X_0+U, a nine-element affine plane. It is invariant under sigma.
On Pi modulo F_3 w, each step adds the nonzero class [u]. Every three
consecutive steps therefore visit the three quotient classes exactly
once, including ell exactly once. Summing the increments gives

    sigma^3(X)=X+w   for every X in Pi.

A positive return time is divisible by three from the quotient. If it
is 3j, the identity then requires j*w=0, so three also divides j.
Conversely sigma^9(X)=X. Every orbit in Pi has length nine, so it is
one full orbit. Its matching union is one simple cycle of length 18,
with exact support

    S_Pi=L(Pi) union R(Pi+v_a).

Outside Pi, a translation orbit X+F_3 u never meets ell, since otherwise
X would lie in Pi. Hence sigma is ordinary translation by u there.
Those components are unchanged original six-cycles, already covered by
Section 5. This accounts for every component, not just the modified one.

For b,c repeat the argument with u'=v_b-v_c and -w. Its plane is the
same Pi, since u'=u+w, and its three-step displacement is -w. The same
classification holds. Renaming the order of the two colors does not
change their undirected component edge sets.

Finally an actual edge inside S_Pi of color z requires

    v_z in v_a+U.

This affine color plane already contains v_a,v_b,v_c, and Section 3
allows no fourth color. Conversely all three corresponding translations
send Pi onto Pi+v_a, so the induced host on S_Pi is exactly cubic.
It has degree three at every selected vertex. Together with the
unchanged six-cycle cases, this proves (R1) for every color pair after
every possible single move, and for the initial coloring.

## 7. Cross-state collisions and the degree threshold

Suppose any two simple cycles on the same vertex set S are edge-disjoint.
At every vertex of S each cycle uses two incident edges. Disjointness
makes these four distinct edges of G[S]. Thus its minimum degree is at
least four. This contradicts (R1) if even one of the cycles is in C_1(phi).
In particular the detector fails even when it compares all states and
all components at once. It is not rescued by palette labels changing
between states, because the obstruction concerns the actual induced host.

For q=3^k the exact ledger is

    r_k=3^k,  N_k=2*9^k,  log_2 N_k=1+2k log_2 3 <= 5k  (k>=1).

Exponential growth exceeds every fixed power: for fixed C>0 and a>=0,
3^k/(5k)^a tends to infinity. For example its successive ratio is
3*(k/(k+1))^a, eventually greater than two, which proves divergence.
Hence r_k>C(log_2 N_k)^a for all sufficiently large k. Changing the log
base only changes the fixed constant. The graphs are C4-free, so no
large balanced biclique is being used to produce this method failure.

## 8. Verification boundary and kill criterion

The paper is a proposed complete proof, not an oracle result. Independent
adversary and reviewer must check all four-point affine relations, the
complete component classification and the exact cross-state predicate.
Primary comparison must distinguish prior one-step/local-repair barriers,
the classical parabola construction, and this claimed detector boundary.

No graph avoidance conclusion or improved f(n) bound is drawn. Full
Kempe-class growth is still open; the failed KS102 proof attempt is not
reopened by this one-step barrier. No k=1/degree-three case earns credit.
If the classification or the growing-degree construction fails and no
single precisely stated repair survives independent review by end103,
close R1. If accepted, assess the method-barrier Lean gate before writing
any formalization. No computation or Lean has been run for this note.
