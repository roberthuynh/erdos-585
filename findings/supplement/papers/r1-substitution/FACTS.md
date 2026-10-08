# FACTS: the lemmas this lane relies on, each with a proof

Graphs are finite and simple unless stated. A *pair* on S is two edge-disjoint cycles C1, C2 with
V(C1) = V(C2) = S. An *avoider* has no pair. e(S) counts edges with both ends in S. Rung labels:
(a) proof, (b) special case, bound or counterexample, (c) literature, (d) formalization. Nothing here
is a project result until `check.sh` passes; these are written proofs, rung (a) or (b) on paper.

## The three facts from the brief

**B1. A pair is a 4-regular graph.** Each vertex of S has degree 2 in C1 and 2 in C2, and the cycles
share no edge, so C1 ∪ C2 is 4-regular on S. Conversely a 4-regular graph on S that splits into two
Hamilton cycles is a pair. So: G has a pair iff G has a (not necessarily induced) 4-regular subgraph
with a Hamilton decomposition. ∎

**B2a. Cut bound.** If every subgraph of G with minimum degree >= 4 has an edge cut of size <= 3
(a split of its vertex set into two nonempty parts with at most 3 edges across), then
e(G) <= 3n - 3.
*Proof.* Induction on n. n = 1: 0 <= 0. Let n >= 2. The hypothesis passes to every subgraph. If some
vertex v has degree <= 3, then e(G) <= e(G - v) + 3 <= 3(n-1) - 3 + 3 = 3n - 3. Otherwise G has
minimum degree >= 4, so G has a cut (A, B) with at most 3 edges, and
e(G) <= (3|A| - 3) + (3|B| - 3) + 3 = 3n - 3. ∎

**B2a'. Cut bound for simple graphs.** Under the same hypothesis, a simple graph on n >= 3 vertices
has e(G) <= 3n - 6.
*Proof.* n = 3, 4: at most 3 and 6 edges. Let n >= 5. If some vertex has degree <= 3, remove it:
e(G) <= 3(n-1) - 6 + 3. Otherwise the minimum degree is >= 4 and there is a cut (A, B) with at most
3 edges. If |A| = a <= 4, each vertex of A has at most a - 1 neighbors in A and so at least 5 - a
across, which gives a(5 - a) >= 4 cut edges, a contradiction. So |A|, |B| >= 5 and
e(G) <= (3|A| - 6) + (3|B| - 6) + 3 < 3n - 6. ∎

**B2b. Avoiding piece.** If G is a 6-regular avoider, G has a subgraph H with max degree <= 6,
e(H) = 3|H| - 2, e_H(S) <= 3|S| - 3 for every nonempty proper S, and H is an avoider.
*Proof.* G has 3n >= 3n - 2 edges. Among subgraphs with e >= 3|V| - 2 pick H with fewest vertices,
then fewest edges. Deleting an edge keeps the vertex set, so e(H) = 3|H| - 2. A proper S with
e_H(S) >= 3|S| - 2 would be a smaller choice. Subgraphs of avoiders are avoiders. ∎

**B2c. Shape of the piece.** H is 4-edge-connected, its degrees lie in {4,5,6}, the deficiencies
6 - deg(v) sum to 4, and |H| >= 7.
*Proof.* For a split (A, B): e(A,B) = 3n - 2 - e(A) - e(B) >= 3n - 2 - (3n - 6) = 4. So every degree
is >= 4. The degree sum is 6n - 4. A simple graph needs 3n - 2 <= n(n-1)/2, so n >= 7. ∎

**B3. Bipartite reduction.** A bipartite r-regular graph with r >= 6 has a spanning 6-regular
subgraph. *Proof.* By Koenig's theorem it splits into r perfect matchings; take six. ∎ (c: Koenig.)

## Cut calculus

**C1.** If a cycle has vertices on both sides of a split (A, B), it uses an even number >= 2 of cut
edges. So a pair whose vertex set meets both sides uses at least 4 cut edges. A pair cannot straddle
a cut of size <= 3. If it straddles a cut of size 4, all four edges are used, two by each cycle, and
each cycle meets each side in exactly one path. The proof is parity of crossings along the cycle,
so it holds verbatim for multigraphs (a cycle of length 2 across a cut uses both of its edges); it
is used that way for L6 and L6b in PROOF-R1.md. ∎

**C2. Piece gives a 6-regular avoider.** Let H be an avoider with max degree <= 6 and
e(H) = 3|H| - 2 (total deficiency 4). Let K be a connected 4-regular simple graph with no Hamilton
decomposition (example: two copies of K5 minus an edge, plus a vertex joined to the four vertices of
degree 3; it has a cut vertex). Replace every vertex of K by a copy of H and realize every edge of K
by an edge between deficient vertices of the two copies, one unit of deficiency per end. The result
G is simple and 6-regular, and G is an avoider.
*Proof.* A pair inside one copy is impossible. Otherwise S meets a copy Hi and leaves it; the cut
around Hi has 4 edges, so by C1 each cycle passes through Hi exactly once and all four skeleton edges
at Hi are used. Then the neighboring copies are also met, so every copy is met (K connected), and
contracting the copies turns C1, C2 into two edge-disjoint Hamilton cycles of K. Contradiction. ∎

So: **a 6-regular avoider exists iff an avoider with max degree <= 6 and >= 3n - 2 edges exists.**

**C3. Six-pole form.** A 6-regular avoider exists iff there is a graph P with max degree <= 6 and
six units of deficiency such that P has no pair and P has no *4-passage*: two edge-disjoint paths
with the same vertex set whose four ends carry four distinct units of deficiency.
*Proof.* Given G and a vertex v, P = G - v works: a 4-passage closes through v into a pair. Given P,
add a vertex joined to the six deficiency units; a pair through it is a 4-passage. ∎

**C4. Cut-only avoiders stop at 3n - 6 with max degree 6.** The cube of a path (i ~ j iff
0 < |i-j| <= 3) has 3n - 6 edges, max degree 6, and is 3-degenerate, so it has no subgraph of
minimum degree 4 and no pair. By B2a, any avoider with >= 3n - 2 edges contains a 4-edge-connected
subgraph (B2c), so it must avoid for a reason that no small cut explains. ∎

## Easy positive classes (each contains the pair)

**P1. Squares of cycles.** C_m^2 (i ~ i±1, i±2 mod m), m >= 5. m odd: the ±1 edges and the ±2 edges
are two Hamilton cycles. m even, m >= 6: A = 0,2,4,...,m-2,m-1,m-3,...,3,1,0 and
B = 1,2,3,...,m-2,0,m-1,1 are edge-disjoint Hamilton cycles (A uses every ±2 edge except {m-2,0} and
{m-1,1}, plus {m-2,m-1} and {0,1}; B uses the rest). ∎

**P2. K_{4,4}.** With parts a_i, b_j (i, j mod 4): the edges a_i b_{i+t} for t in {0,3} form an
8-cycle, and those for t in {1,2} form another. ∎

**P3. Line graphs of connected 4-regular graphs.** Let K be connected, 4-regular, simple. Then L(K)
is 6-regular and has two edge-disjoint Hamilton cycles.
*Proof.* A transition system picks, at each vertex, one of the three pairings of its four edges.
*Kotzig's lemma:* for any transition system T there is an Euler tour using no pairing of T. Choose at
each vertex a pairing other than T's so that the number of resulting closed trails is least. If there
are two trails, connectivity gives a vertex v on both; the third pairing at v (not T's, not the
current one) merges them, a contradiction. So one trail, an Euler tour. Now take any Euler tour T1 and
a tour T2 that avoids T1's pairings. Consecutive edges of a tour are adjacent in L(K), so each tour is
a Hamilton cycle of L(K); an edge of L(K) is a pair of K-edges at their unique common vertex, and it
lies on a tour iff the tour uses that pair consecutively, so the two cycles are edge-disjoint. ∎

**P4. Total graphs of cubic graphs.** T(J) is 6-regular. For a cycle v1 e1 v2 e2 ... vk ek in J the
sequence v1, e1, v2, e2, ..., vk, ek has consecutive and second-consecutive terms adjacent in T(J),
so T(J) contains C_{2k}^2 with 2k >= 6. Apply P1. ∎

**P5. (c) Where 4-regular subgraphs are forced. Depends on Olson's theorem; citation not checked
against the source.** Olson (1969): for a finite abelian p-group that is a sum of cyclic groups of
orders p^{e_i}, every sequence of 1 + sum (p^{e_i} − 1) elements has a nonempty subsequence with sum
zero. Give an edge uv the vector e_u + e_v in (Z/4)^V. All edge vectors lie in the subgroup of
vectors with even coordinate sum, which is (Z/4)^{n−1} + Z/2, so any 3n − 1 edges contain a nonempty
set in which every degree is 0 mod 4. With maximum degree at most 7 that set is a 4-regular
subgraph. For a bipartite graph the edge vectors lie in a subgroup (Z/4)^{n−1} and 3n − 2 edges
suffice. So an avoider with maximum degree 6 and 3n − 2 edges that is bipartite always has a
4-regular subgraph, and one with 3n − 1 edges always does. Multigraphs show the bound is tight there
(an odd cycle with all edges tripled except one has 3n − 2 edges and no such subgraph); in simple
graphs the census finds none above 3n − 5. This plays no role for 6-regular graphs themselves, which
have 4-regular subgraphs by Petersen's 2-factor theorem.

**P6. (c) Literature, not re-proved here.** Connected 4-regular Cayley graphs on abelian groups have
Hamilton decompositions (Bermond, Favaron and Mahéo, JCTB 46 (1989), 142–153, Main Theorem).
Kim and Wormald, *Random matchings which induce Hamilton cycles, and Hamiltonian decompositions
of random regular graphs*, JCTB 81 (2001), 20–44, prove the random-regular conclusion for each
fixed even degree 2k >= 4 as the order tends to infinity. This does not claim the conclusion for
k = 1 or for arbitrary growing degree.
