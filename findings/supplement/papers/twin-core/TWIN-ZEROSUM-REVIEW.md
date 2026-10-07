# Independent mixed-modulus twin review

October 3, 2026. The complete [TWIN-ZEROSUM.md](TWIN-ZEROSUM.md) and its separate one-singleton core extension (not included) were independently reviewed. No mathematical gap was found in the stated forcing arguments. No Lean, oracle, numerical search, Git mutation, or public step. This is paper validation, not a project result or novelty claim.

## Source theorem and the strict threshold

I directly read [Alon, Friedland and Kalai, Regular Subgraphs of Almost Regular Graphs](https://web.math.princeton.edu/~nalon/PDFS/Publications/Regular%20subgraphs%20of%20almost%20regular%20graphs.pdf), Theorem 2.1 and Corollary 2.2 on printed pages 81-82. These give a nonempty zero-sum subset for mixed prime-power coordinate moduli, and improve the threshold when every vector has total coordinate sum divisible by the underlying prime. The latter condition is essential to the one-coordinate saving used here. This is an existing algebraic theorem, not a new zero-sum result.

For a simple incidence graph J with g group vertices and r>=1 right vertices, label each edge by one in its group coordinate modulo four and one in its right coordinate modulo two. Every label has even total parity. The labels therefore lie in the subgroup

    K = kernel(C4^g x C2^r -> C2, total parity).

Dropping a fixed right coordinate is an isomorphism from K to C4^g x C2^(r-1). Its inverse recovers that coordinate as the parity sum of all remaining coordinates, including the group coordinates reduced modulo two. Hence the corrected sufficient inequality is

    e(J) > 3g+r-1.

The initially proposed e(J)>3g+r remains valid but wastes this one parity relation. The improved strict inequality is also the direct substitution into AFK Corollary 2.2. The requirement r>=1 prevents an empty-graph error; an entirely empty quotient must not be certified by 0>-1.

Each chosen group degree is zero modulo four and is at most six, hence is zero or four. Each chosen right degree is even and is at most three, hence is zero or two. A nonempty zero-sum edge subset activates at least one group and at least one right vertex. These conclusions concern a single simultaneous edge subset, not separately feasible degrees.

## Independent check of the direct Boolean proof

The finished note does not need the general zero-sum theorem as a black box. Its explicit characteristic-two polynomial argument is complete. At each group, L is the sum of incident edge variables, and Q is the sum of their products over **unordered two-element subsets**. On a Boolean selection of k incidences, these values are k modulo two and binomial(k,2) modulo two. With k<=6, the simultaneous zeros are exactly k=0 and k=4. Counting ordered distinct pairs instead would cancel Q in characteristic two and would be wrong; the unordered indexing must be preserved in any implementation.

The imposed equations are L and Q at every group and L at all but one right vertex. Their total degree is at most 3g+r-1<m. The missing right equation follows because both shore sums count the same selected edges modulo two. Its degree cap then gives zero or two, exactly as for the other right vertices.

The product of 1+f over the imposed equations is their common-zero indicator over F2. Its degree is less than the number m of variables. Every monomial therefore omits a variable, and summing over that free Boolean variable gives zero in F2. Summing the product over all assignments is consequently zero. The all-zero assignment contributes one, so at least one further common zero exists. Its support is a nonempty actual incidence edge set. This validates the whole extraction argument, including nonemptiness, without an assumed Davenport constant or an unproved auxiliary fiber count.

The optional componentwise saving is also correct: each nontrivial incidence component supplies its own redundant right parity equation. After discarding isolated vertices, m>3g+r-c suffices, with c its number of components. None of the stated regular or critical corollaries relies on this optional strengthening.

## Actual faithful lifting and its boundary

The groups must be disjoint sets of actual equal-neighborhood vertices, each of size at least two, and J must record actual group-to-right adjacency. From every active group choose two different actual clones. The selected quotient has degree four at each active group and degree two at each active right vertex. Its two right neighbors are distinct groups because the incidence graph is simple.

Use the previously checked two-clone lifting argument, or Section9 of TWIN-REVIEW.md (not included), on each nontrivial selected component. Assign its four group incidences in pairs to its two clones. Minimize the number of cycles among these finite assignments. A switch between clones of one group on different cycles uses actual twin edges and merges exactly those cycles. Thus the two clones of each group lie in one cycle. Since the quotient component is connected, the resulting cycle spans its expanded support. Swapping the two clones in every group yields another actual simple cycle on exactly that support, with no common edge: each right vertex meets distinct groups, and its endpoint within each changes.

No projected closed walk or artificial completion is used. The nonempty selected quotient has at least two groups, so its expanded support has at least four vertices per shore and cycle length at least eight. Parallel edges cannot arise in the expanded simple host. This proves faithful-pair existence.

It does **not** establish spanning paired factors on the original host: inactive quotient vertices and the third clone of an active size-three class may be omitted. Consequently it can replace the flow argument only for pair existence, not the stronger spanning exposure asserted in TWIN-CORE.md.

## Six-regular class count

Assume a nonempty finite simple six-regular bipartite host. A maximal false-twin class of size at least four supplies an actual K4,4 using four of its six common neighbors, so handle that case directly. Otherwise write s,p,q for the numbers of singleton, size-two and size-three maximal classes on one shore. Positive regularity balances the shores, so

    r = s+2p+3q.

Delete the singleton classes from the quotient, without changing any other adjacency. Its g=p+q group vertices each have degree six, so e(J)=6(p+q). Every right vertex meets at most three such groups, since their weights are at least two and its original degree is six. The improved inequality becomes

    6(p+q) > 3(p+q)+(s+2p+3q)-1,
    equivalently p>=s.

The integer endpoint is included. Thus an avoiding six-regular bipartite host without a large left twin class must satisfy p<s. This constrains that class distribution; it does not force a positive singleton density or an unrestricted regular-degree bound.

## At most two singleton classes

For s=0 the inequality p>=s is automatic, including the all-triple case p=0. If s=1, every right neighbor of the singleton needs additional weight five from the size-two/three classes. The only possibility is one pair and one triple. Thus p>=1=s, and the improved zero-sum criterion already suffices. The earlier maximality argument excluding p=1 is correct but unnecessary for this improved threshold: all six neighbors would be the unique pair's full neighborhood, making the claimed singleton a twin.

For s=2 suppose p<=1. A right vertex meeting both singletons would need remaining weight four. This needs two pair classes, impossible under p<=1. The two singleton neighborhoods are therefore disjoint. Each neighbor of either singleton needs weight five from the nonsingleton classes, hence must meet the unique pair class; if p=0 no such neighbor is possible at all. When p=1 both disjoint six-element neighborhoods would be contained in that pair's six-element neighborhood, also impossible. Therefore p>=2=s and the criterion applies.

This proves the at-most-two-singletons corollary on paper. It does not settle s=3. In particular a right vertex may then meet all three singletons and one triple class, so the preceding disjoint-neighborhood proof does not extend.

## Exact capped core count

In the exact bipartite degree-six capped core, both shores have total nonnegative deficit two. If every left maximal twin class has size at least two and no class is large enough for the direct K4,4 case, the deficit must be carried by exactly one size-two class whose common degree is five. Every other size-two or size-three class has degree six. Hence

    g=p+q, r=2p+3q, e(J)=6(p+q)-1, p>=1.

The improved zero-sum budget is 3g+r-1=5p+6q-1. Its strict surplus is exactly p>0, so it forces the pair. This does not need the stronger separate lower bound p>=3.

That stronger count also checks. Let t22,t23,t222,t33 count right neighborhoods by their incident class sizes. Their total deficit is 2t22+t23=2. Counting incidences at pair classes gives

    6p-1 = 2t22+t23+3t222 = 2+3t222,
    t222 = 2p-1.

Since p>=1, at least one type222 vertex exists. It meets three distinct pair classes, so p>=3. The simplicity of the quotient is needed at this last step. This is consistent with, but unnecessary for, the improved forcing budget.

## Separate one-singleton exact-core extension

The additional paper was read independently after the main proof was complete. It extends the exact capped-core conclusion to a shore with **one** singleton, without applying the six-regular at-most-two-singletons theorem to a deficient graph.

After handling a large twin class by K4,4, let u be the singleton. Its degree is between four and six, while every other class has size two or three and equal degree internally. The shore deficit two leaves exactly two possibilities: u has degree four and all other classes have degree six, or u has degree six and exactly one pair class has degree five. A degree-five u would leave a deficit of one, impossible among the nonsingleton classes. Thus the two listed profiles are exhaustive.

Write eta=0 or1 for the second case's exceptional pair-class deficit counted once. The quotient has r=2p+3q+1 and m=6(p+q)-eta, so its strict mixed-modulus surplus is p-eta. In the first profile, p=0 would make each of u's four distinct neighbors have one singleton neighbor and one triple class, hence degree four. Those vertices alone would spend eight right-shore deficit units, exceeding the total two. Therefore p>=1 and the main lemma applies. In the second profile it applies whenever p>=2.

The remaining case has the unique pair class P of degree five and singleton u of degree six. The difference N(u) minus N(P) is nonempty. Every right vertex there must have u and exactly one triple class as neighbors, since its degree lies between four and six. It has degree four and spends the entire right deficit two. There is therefore exactly one such vertex y0. The neighborhood sizes then force N(P)=N(u) minus {y0}. All other right vertices have degree six. The five common neighbors each see u,P and one triple; y0 sees u and one triple Q0; every other right vertex sees two distinct triples. This completely justifies the asserted rigidity.

As an independent count check, let a,b,c be the numbers of right vertices adjacent to P only, both P and u, and u only. They have deficits one, zero and two respectively. The equations

    a+b=5, b+c=6, a+2c=2

give a=0,b=5,c=1, agreeing with the neighborhood proof.

Deleting the actual singleton u and exceptional right vertex y0, then suppressing the remaining right vertices, produces a loopless labeled multigraph on g=p+q=1+q group vertices. P and Q0 are distinct and have degree five; every other group has degree six. Consequently its edge count is 3g-1. Every suppressed edge retains its original distinct right label. There is no completion or arbitrary pair projection.

The exceptional multigraph's Boolean selection proof is valid. Choose a vertex w. Impose L and Q at every other vertex and impose T, the parity of the total selected edge count. The total degree is at most 3(g-1)+1=3g-2, below its 3g-1 edge variables. The same common-zero parity proof therefore supplies a nonempty selection. Every selected degree except that at w is divisible by four. The selected edge count is even, so twice that count is divisible by four. Handshaking then forces the selected degree at w to be divisible by four too. The degree-six cap turns all nonzero selected degrees into four. This is equivalent to the paper's valid recovery of L_w and Q_w separately.

The general source threshold also agrees: AFK Theorem3.1 at q=4 gives the strict threshold e>3g-2 for a loopless multigraph, and the paper explicitly allows parallel edges. The self-contained argument above already proves the specialized extraction, so there is no reliance on a compressed average-degree formula outside its scope.

A nonempty connected component of the selected quartic multigraph lifts by choosing two original clones per active group and reinserting every actual right label. The earlier verified Euler/twin argument gives two actual simple cycles with the same support and disjoint edges. The omitted u,y0 and unused third clones are allowed to remain outside the support. Thus the one-singleton extension has no hidden spanning or regular-completion premise.

The precise consequence is that an avoiding bipartite exact capped core would need at least **two** singleton maximal twin classes on each shore. Two singletons in a deficient core remain unresolved here; the separate six-regular theorem cannot be transferred to that case.

## Saved controls, scope, and formalization boundary

The final note retains all exact hypotheses and does not assume any arbitrary four-factor is positive. Its specially selected quotient and actual twin lift prove connected cycles directly. Proper supports and unused third clones are allowed, so the Paper66 spanning-exposure obstruction is not bypassed by an unsupported extension. The irregular signed-deficit controls do not satisfy the maximum-degree premise. The characteristic-three faithful-pair counting barrier concerns different variables, witnesses and characteristic; this proof counts characteristic-two incidence subsets before constructing the cycles.

The conclusion strengthens the paper-level restricted forcing class to six-regular hosts with at most two singleton classes on one shore. In particular, a bipartite six-regular avoider would need at least three singleton maximal twin classes on each shore and, after excluding large classes, fewer pair classes than singleton classes. These are structural restrictions, not a positive singleton-density bound, an unrestricted forcing theorem, or a regular-degree record.

The algebraic selection theorem is existing source material in specialized form, and the two-clone lifting mechanism was already saved. No priority or novelty conclusion is drawn from composing them. The s=3 case remains unresolved; arithmetic feasibility in that regime supplies neither an avoiding graph nor a failure of forcing.

For eventual Lean, preserve the original faithful-pair predicate, finite nonempty host assumptions, quotient simplicity, distinct group neighborhoods at each selected right vertex, and unordered indexing of Q. Encode exact criticality as m+2=3n, or separately require nonemptiness if using natural-number subtraction; the empty graph must not enter through 3*0-2=0 in Nat. Proving only the polynomial selection lemma would be infrastructure, not verification of the whole restricted graph class. No simulations or formalization have been started in this review.

Final reviewed SHA256 values:

    TWIN-ZEROSUM.md
    a897283e4fd5badf64fdeba95faa5cb054cc374fc7cc992945cdbbbddc8e0e21

    twin-zerosum/ONE-SINGLETON-CORE.md
    a19bf97b02c563263bef2addfdfe5cff1201b22fa0eb96879fd9fae815c9b82f
