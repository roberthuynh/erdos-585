# R1: unbalanced bipartite gadgets behave like vertices

Status: written proof, rung (a) on paper for the theorem and rung (b) for the degree-5 graph. Not a
project result until a Lean file passes `check.sh`. Independent review: see REVIEW-R1.md.

## Conventions

A *multigraph* is loopless and may have parallel edges; each parallel edge is its own edge. A *cycle*
is a connected 2-regular subgraph, so in a multigraph two parallel edges form a cycle of length 2. A
*pair* is two edge-disjoint cycles with the same vertex set. For simple graphs this is the usual
notion. A graph or multigraph is *pair-free* if it has no pair.

## Gadgets and substitution

**Definition (d-gadget).** A simple bipartite graph Γ with sides I and O such that every vertex of I
has degree d, every vertex of O has degree at most d, and |O| = |I| + 1. The *deficiency* of o ∈ O is
d − deg(o). Counting edges from both sides, the deficiencies sum to d(|I| + 1) − d|I| = d.

**Definition (substitution).** Let L be a d-regular multigraph and Γ a d-gadget. A graph G is a
*substitution of Γ into L* if
1. V(G) is the disjoint union of copies Γ_u of V(Γ), one for each vertex u of L, and G induces a copy
   of Γ on each Γ_u;
2. the remaining edges of G ("link edges") are in bijection with E(L): the link edge of an L-edge uw
   joins an O-vertex of Γ_u to an O-vertex of Γ_w;
3. every O-vertex o of every copy lies on exactly d − deg_Γ(o) link edges;
4. G is simple (no two link edges join the same two vertices).

Then G is d-regular: an I-vertex keeps its d neighbors inside its copy, and an O-vertex has
deg_Γ(o) + (d − deg_Γ(o)) = d. If L is bipartite with sides X and Y, then G is bipartite: put the
O-side of Γ_u and the I-side of Γ_w in one class and the I-side of Γ_u and the O-side of Γ_w in the
other, for u ∈ X and w ∈ Y; gadget edges join I to O inside a copy, link edges join the O-side of an
X-copy to the O-side of a Y-copy.

## The single-passage lemma

**Lemma 1.** Let G be a substitution of a d-gadget Γ into L with d ≤ 7, and let (C1, C2) be a pair of
G on the vertex set S. Let u be a vertex of L with S ∩ V(Γ_u) ≠ ∅. Then either S ⊆ V(Γ_u), or exactly
four link edges at Γ_u lie in C1 ∪ C2, two of them in C1 and two in C2.

*Proof.* Let H = C1 ∪ C2; every vertex of S has degree 4 in H and every other vertex has degree 0.
Write S_I and S_O for the vertices of S on the I-side and the O-side of Γ_u, and let x be the number
of link edges at Γ_u that lie in H. Every neighbor in G of an I-vertex of Γ_u is an O-vertex of
Γ_u, so the 4|S_I| edges of H at S_I all end in S_O. Every neighbor of an O-vertex of Γ_u is an
I-vertex of Γ_u or the far end of a link edge, so the 4|S_O| edge-ends of H at S_O consist of those
4|S_I| edges and x link edges. Hence

    x = 4(|S_O| − |S_I|).

There are d ≤ 7 link edges at Γ_u, so x ∈ {0, 4}.

If x = 0, no edge of H leaves Γ_u from S ∩ V(Γ_u). C1 is connected and meets Γ_u, so C1 lies inside
Γ_u, and S = V(C1) ⊆ V(Γ_u).

If x = 4: the link edges at Γ_u are exactly the edges of G with one end in V(Γ_u). A cycle with
vertices on both sides of this cut uses an even, positive number of cut edges. S meets Γ_u and, since
x > 0, also meets the outside; both cycles have vertex set S, so each uses at least two cut edges.
With four in total, each uses exactly two. ∎

Remark. For the gadget Γ5 below, the same statement is checked by a program that uses no counting:
`tools/gadget_traces.py` lists every way a pair can meet the gadget (all colorings of its edges and
dangling edges by unused, red, blue with red degree = blue degree ∈ {0, 2} at every vertex).

## Theorem R1

**Theorem R1.** Let Γ be a pair-free d-gadget (d ≤ 7) and L a pair-free d-regular multigraph. Then
every substitution G of Γ into L is pair-free. G is simple and d-regular, and bipartite if L is.

*Proof.* Suppose (C1, C2) is a pair of G on S. If S ⊆ V(Γ_u) for some u, the pair lies in the copy
of Γ induced on Γ_u (link edges join different copies), contradicting that Γ is pair-free. So by
Lemma 1, for every u in the set U of vertices of L whose copy meets S, each of C1, C2 uses exactly
two link edges at Γ_u.

Fix i ∈ {1, 2}. Delete from Ci its edges inside copies. What remains is a set of link edges; in L it
is a set E_i of edges in which every vertex of U has degree exactly 2 and every other vertex degree
0. The subgraph (U, E_i) of L is connected: walk around Ci and record the copy of each vertex;
consecutive vertices lie in the same copy or in two copies joined by an edge of E_i, and the walk
visits every copy in U because V(Ci) = S. A connected 2-regular loopless multigraph is a cycle (of
length 2 if |U| = 2; |U| = 1 would mean S ⊆ V(Γ_u), which was excluded). So E_1 and E_2
are cycles of L with the same vertex set U. They are edge-disjoint because C1 and C2 are and link
edges correspond one-to-one to edges of L. That is a pair in L, a contradiction. ∎

## Corollary A: a bipartite 5-regular graph with no pair

**Gadget Γ5** (13 vertices, 30 edges). I = {a1, a2, a3, x4, x5, x6}, O = {b1, b2, b3, o4, o5, o6, o7}.
Start with K_{3,3} on {a1,a2,a3} and {b1,b2,b3}, then add in this order
x4 ~ b1,b2,b3; o4 ~ a1,a2,x4; x5 ~ b1,b2,o4; o5 ~ a3,x4,x5; x6 ~ b3,o4,o5; o6 ~ a1,a2,x6;
o7 ~ a3,x5,x6.
Every I-vertex has degree 5. The O-degrees are 5,5,5,5 (b1,b2,b3,o4), 4 (o5), 3 (o6), 3 (o7). So Γ5
is a 5-gadget with deficiencies 1, 2, 2 at o5, o6, o7.

Γ5 is pair-free: in the order above each added vertex has exactly three earlier neighbors and
K_{3,3} has maximum degree 3, so every subgraph of Γ5 has a vertex of degree at most 3 (its last
vertex in the order, or any vertex if it lies in the K_{3,3}). A pair is a 4-regular subgraph. So
there is none.

**Skeleton L5** (8 vertices, 20 edges): the bipartite multigraph on x0..x3, y0..y3 with
multiplicities x0y2: 2, x0y3: 3, x1y1: 1, x1y2: 3, x1y3: 1, x2y0: 2, x2y1: 3, x3y0: 3, x3y1: 1,
x3y3: 1. Every vertex has degree 5.

L5 is pair-free. Its underlying simple graph has 10 edges on 8 vertices and is connected, so its
cycle space has dimension 3. It is spanned by the 4-cycles A = x0 y2 x1 y3, B = x2 y0 x3 y1 and
C = x1 y1 x3 y3; the cycles of the graph are A, B, C, A+C (a 6-cycle), B+C (a 6-cycle) and A+B+C (the
8-cycle x0 y2 x1 y1 x2 y0 x3 y3); A+B is two disjoint 4-cycles. These six cycles have six different
vertex sets. A cycle of length at least 3 in a multigraph uses at most one edge from each parallel
class, so it lies over one of these six. So a pair in L5 would be either two cycles of length 2 on
the same two vertices, which needs multiplicity 4, or one of the six cycles taken twice on parallel
copies, which needs every edge of it to have multiplicity at least 2. But A contains x1y3, B contains x3y1, C contains x1y1,
and the other three contain x1y1 or x3y3, all of multiplicity 1.

**The graph.** A substitution of Γ5 into L5 exists: at each copy the five link edges go to o5 once,
o6 twice and o7 twice, and parallel edges of L5 must get different pairs of end vertices. One valid
assignment, found by backtracking in `tools/bip5.py`, is in `data/bip5-avoider-104.edges`; the script
checks that the result is simple, bipartite and 5-regular. Theorem R1 does not depend on which valid
assignment is used. By Theorem R1:

> **Corollary A.** There is a bipartite 5-regular graph on 104 vertices with no two edge-disjoint
> cycles on the same vertex set.

The project's bipartite record was degree 4. Nothing here is optimized for size.

**Remark (a second route, used by the Lean file).** L5 is pair-free for cut reasons: the edges
x1y1 and x3y3 form a 2-edge cut separating {x0, x1, y2, y3} from {x2, x3, y0, y1}, and inside each
half the edges x0y2 (two of them) and x1y3 form a 3-edge cut separating the triple bundle x0y3 from
the triple bundle x1y2 (similarly in the other half). After substitution these are edge cuts of the
same sizes in the simple graph, so a pair would have to lie inside one block, and blocks are
pair-free. So this particular graph is also "cut-explained" in the sense of FACTS.md B2a, through
cuts of sizes 2, 3 and 3 applied to induced subgraphs in turn. The Lean file
`openmath/Openmath/Proofs/BipartiteFive.lean` (LEAN.md) proves Corollary A this way with the
project's `not_hasPairF_of_small_cut_map`, using a substitution in which every triple bundle joins
o5-o5, o6-o6, o7-o7; its graph is not isomorphic to `data/bip5-avoider-104.edges` (same
Weisfeiler-Lehman hash, `networkx.is_isomorphic` false), both are valid substitutions. Theorem R1 is
not needed for the Lean proof; it is what explains why such skeletons exist at degree 5 and shows
what a degree-6 analog would need.

Checks beyond the proof (see CHECKPOINT-01.md for the logs):
- `tools/gadget_traces.py`: Γ5 with its five dangling edges has 260,736 traces, every one of type
  (one red path, one blue path), and no internal pair.
- L5: 411 cycles as a multigraph, no pair by plain enumeration; no pair by the integer program.
- The 104-vertex graph: integer program (HiGHS with lazy subtour cuts) hit its 6000-second limit and decided nothing (correction to this sentence; the run log is census/logs/bip5-ilp.log in this supplement).

## Corollary B: what R1 says at degree 6

**6-regular multigraphs can avoid.** Let K be the 4-regular multigraph on {0,1,2,3} with edges 03
(three times), 12 (three times), 02, 13. K has no two edge-disjoint Hamilton cycles: its simple
graph is one 4-cycle, and two edges of it are single.
- L6: replace each vertex of K by a triangle abc with ab and bc tripled and ca single (degrees 4, 6,
  4), and each edge of K by an edge between vertices of degree 4. 12 vertices, 6-regular.
- L6b: replace each vertex of K by a 4-cycle abcd with ab, bc, cd tripled and da single (degrees
  4, 6, 6, 4), orient K as 0→3, 0→3, 3→0, 3→1, 1→2, 1→2, 2→1, 2→0, and for each arc u→w join d of
  piece u to a of piece w. 16 vertices, 6-regular, bipartite.
Both are pair-free: each piece is pair-free (two cycles on the same vertices would need the single
edge twice or four parallel edges), each piece is attached by exactly four edges, so by the cut
calculus (FACTS.md, C1) a pair that leaves a piece passes through every piece once per cycle and
projects to two edge-disjoint Hamilton cycles of K. Both were also checked by cycle enumeration and
by the integer program.

> **Corollary B.** Let B be a bipartite 6-regular graph and o a vertex such that B − o is pair-free.
> Then there is a simple 6-regular graph with no pair, and also a bipartite one. Consequently the
> statement "every bipartite 6-regular graph contains a pair" is equivalent to the stronger
> statement "for every bipartite 6-regular graph B and every vertex o, B − o contains a pair".

*Proof.* Let X, Y be the sides of B with o ∈ X. Then B − o is a 6-gadget with I = X − o and O = Y:
the vertices of X − o keep degree 6, |Y| = |X − o| + 1, and the six neighbors of o have degree 5,
so the six units of deficiency sit on six different vertices. A substitution into any 6-regular
multigraph L therefore exists: at each copy use each of the six deficient vertices for exactly one
link edge; parallel edges of L then get different end vertices, so the result is simple. Apply
Theorem R1 with L = L6 or L = L6b. For the equivalence: if every bipartite 6-regular graph has a
pair and some B − o had none, the bipartite substitution would be a bipartite 6-regular graph with
no pair; the other direction is trivial because a pair of B − o is a pair of B. ∎

So a proof of the degree-6 statement for bipartite graphs has to prove more than it says: for every
vertex o of every bipartite 6-regular graph there is a pair avoiding o. The same holds for any
pair-free 6-gadget for which a substitution exists, not only for gadgets of the form B − o.

## Corollary C: no easy certificate gives a pair-free 6-gadget

A d-gadget has d|I| edges and n = 2|I| + 1 vertices. For d = 6 that is exactly 3n − 3 edges.

- A bipartite graph in which every subgraph has a vertex of degree at most 3 has at most 3n − 9
  edges for n ≥ 6 (the first six vertices of a degeneracy order span at most 9 edges, each later
  vertex adds at most 3). So a gadget with no subgraph of minimum degree 4 needs d|I| ≤ 6|I| − 6,
  which holds for d = 5 from |I| = 6 on (Γ5 is the extremal case) and never for d = 6.
- A simple graph on n ≥ 3 vertices in which every subgraph of minimum degree at least 4 has an edge
  cut of size at most 3 has at most 3n − 6 edges (FACTS.md, B2a'). A 6-gadget has 3n − 3. So every
  6-gadget contains a subgraph of minimum degree at least 4 with no edge cut of size at most 3, and
  it cannot be pair-free for cut reasons either.

So neither of the two easy certificates (no subgraph of minimum degree 4; small edge cuts) can
produce a pair-free 6-gadget. What is proved is only that: Corollary B still applies at degree 6 as
soon as any pair-free 6-gadget exists. The proved thresholds are 3n − 9 for bipartite degeneracy and
3n − 6 for cuts, against 3n − 3 for a 6-gadget; "everything easy stops near 3n edges" is a summary,
not a theorem.
