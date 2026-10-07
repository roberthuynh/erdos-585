# E110: Hall losses and actual boundary compatibility

2026-10-04. Frozen attempt for independent review. E110 remains unresolved; the registered mechanism is closed. No project result is claimed. Only a root oracle PASS can establish one. This paper tests the E110 extraction statement registered in `FINAL-SYNTHESIS.md` (not included), Section 4. The terminal subgraph may have arbitrarily small order. No polynomial retained-order hypothesis is introduced.

## 1. Exact target and comparison boundary

E110 asks for fixed positive gamma<=1/4, eta<=gamma^2/8, c, and A such that an actual bipartite r-regular avoider G of order N>=4, r>=A(log(2N))^3, contains a balanced actual H with degree interval [(1-eta)k,k], k>=cr, k>=16/gamma^2, and cut expansion gamma*k through half its order. Reviewed local Lemma F and BM-2 would then contradict avoidance for sufficiently large A. Those are written local inputs, not kernel-checked inputs here.

A Pair means two simple edge-disjoint cycles with exactly the same full vertex support, possibly a proper subset of G. A factor, two arbitrary connected cycles, or a pair in a graph obtained by adding edges is insufficient.

The rule below keeps actual edges throughout. The first rule checks whether Hall losses concentrate on four common neighbors. Its single repair stores actual same-support path systems at the real cut. The test succeeds only if it obtains a quantitative loss estimate strong enough to retain a constant fraction of r, or a literal counterexample to the proposed estimate. An identity that does not use avoidance cannot close E110.

## 2. Saved controls

[paragraph omitted]

The room ring R_(4,q), q>=3, has rooms K4,4-a0b0 and connectors a_(i,0)b_(i+1,0). Every vertex has degree four. It is connected and bipartite. A pair in a connected quartic host has full support because all four incident edges at every selected vertex belong to its union. Each room has an actual two-edge boundary, which two disjoint spanning cycles cannot both cross. Hence this is an avoider, with arbitrarily many rooms. Degree four lies outside E110's large-degree scale.

The R1 gadget Gamma5 has six vertices on its degree-five shore and seven on the other, with other-shore degrees 5,5,5,5,4,3,3. The specified construction order makes it 3-degenerate, so no nonempty quartic subgraph is possible. Deleting any one larger-shore vertex makes the sides equal but still produces no quartic subgraph. Its deficiency-five port multiset has multiplicities 1,2,2. A new vertex cannot be attached once to each unit while retaining simplicity. By contrast B-o has degree-six ports at six distinct vertices. R1's single-passage proof uses total boundary at most seven; it does not extend that conclusion to the high r in E110.

The high-girth 6240-vertex reducibility control has a saved actual pair. It refutes certain pure local lift rules, not E110. The corrected control statement and the actual-pair certificate must be retained together.

## 3. The oriented Hall-loss calculation

Let H have equal bipartition classes P,Q and degrees at most r. Let q=r-l be a positive integer. The unit-capacity flow network for a q-factor has capacities q from the source to P, one on actual P-Q edges, and q from Q to the sink. A finite augmenting-path proof gives the criterion

    e_H(X,Q\\Y) >= q(|X|-|Y|)                         (3.1)

for every X subset P, Y subset Q: a residual source-side cut consists of X and Y, with capacity q(|P|-|X|)+e(X,Q\\Y)+q|Y|. Integer augmentations give an actual, unweighted q-factor when all cuts have enough capacity. Thus no external factor theorem is needed for this criterion.

For a violated cut set

    t=|X|-|Y|>0, a=e(X,Q\\Y), b=e(P\\X,Y),
    D_X=sum_(x in X)(r-deg_H(x)), and similarly D_Y.

Subtracting the degree sums of X and Y cancels e(X,Y) and gives

    D_X-D_Y=rt-a+b.                                    (3.2)

Consequently a<qt implies

    D_X-D_Y>l*t+b.                                     (3.3)

If all H-degrees are at least (1-eta)r and l=epsilon*r with 0<=eta<epsilon<1, then

    t/|X| < eta/epsilon,
    e(X,Y)/|X| > r(1-eta/epsilon).                      (3.4)

Indeed D_X-D_Y<=eta*r|X| and b>=0 give the first inequality. For the second, e(X,Y)>= (1-eta)r|X|-a > (1-eta)r|X|-(1-epsilon)rt; substitute the first inequality. These inequalities locate an almost balanced, internally dense rectangle. They hold for positive and avoiding hosts alike.


## 4. The attempted descent and its first charge

The finite candidate rule is the following. Fix 0<epsilon<1 and gamma>0. The current object K is an actual d-regular bipartite subgraph of G. If K has the desired constant expansion, it is already balanced and exactly regular. Otherwise choose a cut U, |U|<=|K|/2, with boundary less than gamma*d*|U|. For each side T of that cut, consider every largest balanced subset W of T, obtained by deleting exactly the shore excess from the larger shore. Set q=floor((1-epsilon)d). If q<1, terminate this candidate step without success. Discard every empty W; if none remain, likewise terminate without success. For the remaining W test a q-factor of K[W] by (3.1). If a nonempty factor exists, retain it and repeat. Its order is strictly smaller. If none exists, use its actual Hall witnesses (3.2). No completion edges are inserted. Even when a factor exists, its degree reduction must be charged before this can prove E110.

The attempted charge first tests concentration: four vertices with four common actual neighbors give K4,4 and hence a pair on exactly those eight vertices. To see the pair explicitly, label the shores a_i,b_i modulo four. The two perfect-matching unions using offsets {0,3} and {1,2} are disjoint 8-cycles. This is a paid same-support conclusion.

An exact avoidance-dependent consequence is available, but it is too weak. In an avoider, for every bipartite rectangle X,Y,

    sum_(x in X) binom(deg_Y(x),4) <= 3 binom(|Y|,4).    (4.1)

Each four-subset of Y has at most three common neighbors; otherwise the displayed K4,4 pair exists. If mu=e(X,Y)/|X|>3, then

    |X|(mu-3)^4 <= 3|Y|^4.                            (4.2)

Indeed binom(d,4)>=(max(d-3,0))^4/24, and the convexity of z -> (max(z-3,0))^4 gives the lower bound after summing. The upper bound follows from (4.1).

For the Hall rectangle in (3.4), |X|>|Y|, so when d0=r(1-eta/epsilon)>3,

    |Y| > ((d0-3)^4/3)^(1/3).                          (4.3)

Thus concentrated Hall obstructions either furnish an actual pair or have order at least a constant times r^(4/3), with the stated dependence on eta/epsilon. This is the ordinary K4,4 obstruction in Hall coordinates. It does not bound their number, total defect, degree loss, or boundary expansion. It does not control the factor failures when eta>=epsilon. At r of order (log N)^3, the lower order scale in (4.3) is only of order (log N)^4. It cannot prevent many successive cuts on larger supports.

This is an easy-end control, not progress toward E110. [sentence omitted] The only permitted repair below therefore operates on K4,4-free graphs as well.

## 5. An exact Hall obstruction inherited from the verified degree-five avoider

Use the actual graph G5 defined in `openmath/Openmath/Proofs/BipartiteFive.lean`, whose unchanged source SHA-256 agrees with the saved official PASS receipt. Its vertices are 0,...,103. The half A={0,...,51} is balanced, with 26 vertices of each bipartition color. Its only boundary edges are {38,77} and {25,90}.

Delete vertices 0 and 55. In the source coloring, 0 has color zero inside A, and 55 has color one outside A. They are nonadjacent and neither is a boundary endpoint. Call the induced graph H.

- H has 102 vertices, 250 edges, and 51 vertices on each shore.
- Its ten vertices adjacent to a deleted vertex have degree four; the other 92 have degree five. Every surviving vertex can lose at most one neighbor because one vertex was deleted from each shore.
- H is an avoider by heredity from G5. This uses the previously checked theorem; no new oracle run is made for H.
- H has no spanning q-regular subgraph for any q>=2, despite minimum degree four.

For the last claim, orient the factor problem with the color-one shore first. Set

    X = (A minus {0}) intersect {color-one vertices},
    Y = (A minus {0}) intersect {color-zero vertices}.

Then |X|=26, |Y|=25. Exactly one available edge goes from X to the opposite shore outside Y, namely {38,77}. Thus the Hall requirement is

    1 >= q(26-25)=q,

which fails for every q>=2. Equivalently a q-factor would need signed boundary difference q around a region with shore imbalance one, while only one edge is available in the required direction. For the cap r=5, (3.2) reads

    D_X=5, D_Y=0, t=1, a=b=1, and 5=5-1+1.

A separately checked perfect matching is listed in `CONTROL-CHECK.json`, so the maximum spanning regular degree is exactly one. The small checker reconstructs the source's literal recursive graph, records its source hash, and checks the displayed Hall witness and matching. Equality of that recorded hash with the saved PASS receipt was checked separately when preparing this paper. It performs no cycle-pair search.

This gives a concrete reason not to infer a spanning factor from balance and degree concentration alone, even under actual avoidance. It is not a counterexample to Lemma F, whose expansion and much smaller relative-spread hypotheses fail here. Nor is it an E110 counterexample: its degree is fixed at five, and E110 allows a proper subgraph.

## 6. The sole repair: actual boundary path systems

Replace the four-common-neighbor charge with the full real-cut interface. For a cut U,W and disjoint selected sets R,B of actual cut edges, require both |R| and |B| to be positive and even. The labels are the actual edges, not only their endpoints. Each side Z in {U,W} has a state if there exist red and blue internal edge sets with the following properties.

1. Their internal supports are the same set T_Z. This includes vertices incident to selected cut edges even when an internal path has length zero.
2. At v in T_Z, the color-i internal degree plus the number of color-i selected cut edges at v is exactly two. Outside T_Z both quantities are zero. The two internal edge sets are disjoint.
3. Each internal color component is a path, possibly a single vertex. No internal closed cycle is permitted in a state in which that color crosses the cut. A closed cycle would remain disconnected from the crossing component after gluing.
4. Each path has exactly two selected boundary-edge incidences of its color. A one-vertex path uses two distinct incidences at that vertex. The component therefore pairs their actual cut-edge labels. Repeated boundary vertices across colors are allowed whenever the degree and disjointness conditions hold.

Let Sigma_Z(R,B) be the set of pairs of perfect matchings on the labels R and B realized by such actual internal systems. Different witnesses may use different T_Z, but within each witness the two colors have identical T_Z. Forgetting a witness's support would invalidate the definition; its existence is part of membership in Sigma.

**Exact gluing criterion.** A pair using exactly R and B at the cut exists if and only if some state from Sigma_U and some state from Sigma_W have the following property: for each color, the colored multigraph union of its two label matchings is connected. The U-side and W-side matching edges retain their distinct colors, so the same label pair on both sides gives two parallel matching edges, not a single set edge.

For the forward direction, restrict each simple cycle to the two sides. Because the cycle crosses the cut, its restrictions have only path components, including any one-vertex components. Its cut traversal makes the alternating union of the two matchings connected. The common cycle support gives the common support on each side.

Conversely glue the actual path witnesses along the selected actual cut edges. At every selected vertex each color has degree two. The connected union of the matchings makes that entire color connected, including every internal path. Thus each color is a connected 2-regular subgraph of the original simple graph, hence a simple cycle. Their edge sets are disjoint and their full vertex sets are both T_U union T_W. No artificial edge, prescribed endpoint completion, or unsupported factor-to-cycle implication appears.

The repaired descent tests these actual compatible states at a Hall cut or at a cut where the accumulated factor degree would fall below c*r. If compatible states exist it returns the literal pair. If none exist, it would have to use this exclusion to bound the degree losses before continuing. The next section records exactly what the exclusion does and does not give.

## 7. Quantitative state exclusion, and where the repair stops

On an avoider, the two state sets in Section 6 have no compatible cross-pair. This is a real global-avoidance restriction. Its force depends on the number of crossings and on which states are actually realizable.

With two red and two blue cut edges, each color has one matching, so nonempty state sets on both sides immediately give a pair. This is the single-passage situation used by R1. It cannot be assumed in E110. In Q4, every pair uses the full connected quartic host and therefore all eight edges of every coordinate cut. The saved cycle lists use respectively (4,4), (6,2), (4,4), (2,6) edges across the four coordinate cuts. The entire Q4 pair is missed by an interface requiring exactly four total crossings at that cut.

For four red and four blue edges, each color has three possible label matchings. Two matchings on four labels have connected colored multigraph union exactly when they are different. The state space is therefore a subset of {1,2,3} squared, with two states compatible precisely when both coordinates differ. Cross-incompatible families A,B satisfy the sharp bound

    |A| |B| <= 9.                                    (7.1)

Here is a direct proof. If A lies in one row or column and has at least two points, B lies in that row or column and both sizes are at most three. A singleton permits at most five B points. Otherwise A contains two points differing in both coordinates; B then has at most the two crossed-coordinate points. If it has both, A has at most two points; if it has one, A has at most five. The empty case is immediate. A=B equal to one full row attains nine. This small compatibility bound was independently evaluated on all 512 subsets of the nine-state space, not on graphs.

For larger port sets, compatibility alone permits very large abstract cross-incompatible families. Suppose |R|=2a with a>=2 and |B|=2b with b>=1. On each side allow every red matching that contains one fixed pair of red labels, and every blue matching. Each side then has

    (2a-3)!! (2b-1)!!

states, a fraction 1/(2a-1) of all abstract states. No red union can be connected: the common fixed pair forms its own two-label alternating component, and other red labels remain. These are abstract families, not asserted realizations in high-degree avoiders. They show that the exclusion equation alone does not force exponentially small state families or make every large pair of families compatible.

**The unpaid step is now explicit.** The Hall data (t,a,b,D_X,D_Y), the degree cap, and the cut size have not supplied a lower bound on the actual Sigma_Z(R,B), or ruled out their concentration on incompatible label pairings. In particular they do not show the existence of even one same-support red/blue path system for a useful port assignment. Independent single-color linkages would not pay this obligation. Neither (7.1) nor the exact gluing criterion relates the loss l*t+b in (3.3) to a quantity that telescopes over the descent.

This is the failure of the single repair. Its state characterization is correct, but no quantitative avoidance-dependent bound on accumulated density or regularity loss was obtained. The definition of Sigma cannot be substituted for such a bound.

## 8. Terminal audit and stop

Even if every descent step could halve the support, successive factors of degree floor((1-epsilon)d) could undergo order log N losses. For fixed epsilon this does not retain a constant fraction of the initial r. The elementary Hall count only excludes small concentrated rectangles, and the state inequalities supply no bound on the number or total weight of the remaining losses. The actual procedure may retain the larger cut side, so halving is not being asserted as a proved invariant.

No bound of the form sum of relative degree losses <= an absolute constant was derived. No balanced constant-gap subgraph of comparable degree was constructed in every high-degree avoider. No example satisfying E110's growing-degree hypothesis and violating its conclusion was constructed. Therefore E110 itself remains open in this record, and the conditional O(n(log n)^4) ledger does not advance.

What is retained is the exact Hall identity, the elementary concentration control, a literal 102-vertex balanced avoider with degrees {4,5} whose maximum spanning regular degree is one, and a correct arbitrary-crossing real-boundary interface with its explicit missing lower bound. These are written control statements. They are not a new growth result, a degree-six forcing result, or a new project PASS.

The one initial charge and one repair are closed. No new search, rule, route, or pass is authorized here. Independent review may correct this record without renewing the mathematics.
