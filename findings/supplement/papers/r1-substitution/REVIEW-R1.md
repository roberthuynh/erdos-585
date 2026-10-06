# REVIEW-R1: adversarial review of PROOF-R1.md and data/bip5-avoider-104.edges

Reviewer: independent subagent, 2026-10-04. Inputs read: PROOF-R1.md, FACTS.md (C1, B2a'),
data/bip5-avoider-104.edges. Nothing under tools/ was read, imported or run. All code for this
review is in review/ and was written from scratch.

Status of this file: complete (A, B, C, verdicts). Written incrementally during the review.

## A. Proof audit

Line numbers refer to PROOF-R1.md as read on 2026-10-04.

### A0. Definitions (lines 15-32)

- Deficiency sum (line 17): the gadget has d|I| edges, all I-to-O, so the O-degrees sum to d|I|
  and the deficiencies sum to d(|I|+1) - d|I| = d. CORRECT.
- d-regularity of G (line 28): I-vertices carry no link edges (item 2 puts link ends on O-vertices
  only) and keep their d gadget edges; an O-vertex has deg(o) + (d - deg(o)) = d. CORRECT.
- Item 1 ("G induces a copy of Γ") plus item 2 ("the remaining edges are link edges") together
  give the two facts every later step uses: no edge of G joins two O-vertices or two I-vertices of
  the same copy, and every link edge has exactly one end in each of two different copies (L is
  loopless). Both are stated, not hidden.

### A1. Hidden assumptions in x = 4(|S_O| - |S_I|) (lines 40-49). CORRECT.

The count uses exactly these facts, each of which follows from the definitions:
1. Every vertex of S has degree exactly 4 in H = C1 ∪ C2 (edge-disjoint, 2 + 2), every other
   vertex degree 0, so every H-edge has both ends in S.
2. No H-edge joins two I-vertices of Γ_u (Γ bipartite, G induced on the copy), so the 4|S_I| edge
   ends at S_I belong to 4|S_I| distinct edges, and each ends in S_O (I-vertices have no link edges
   and their gadget neighbors are O-vertices of the same copy).
3. No H-edge joins two O-vertices of Γ_u (no O-O gadget edges; link edges join different copies),
   so each H-edge at S_O is counted once at S_O: either one of the 4|S_I| gadget edges or one of
   the x link edges at Γ_u.
4. The number of link edges at Γ_u is deg_L(u) = d (L is d-regular), so 0 <= x <= d <= 7.

Nothing else is used: the count does not need G simple, Γ connected, or |O| = |I| + 1 (that
condition only makes the deficiency total equal d). x >= 0 forces |S_O| >= |S_I| automatically.
With 0 <= x <= 7 and 4 | x, x ∈ {0, 4}.

### A2. The case x = 0 (lines 51-52). CORRECT.

The edges of G with exactly one end in V(Γ_u) are exactly the d link edges at Γ_u. If x = 0, no
edge of C1 crosses this cut. C1 meets Γ_u (V(C1) = S and S ∩ V(Γ_u) is nonempty) and C1 is
connected, so V(C1) ⊆ V(Γ_u). The same holds for C2 without extra work because V(C2) = V(C1).

### A3. "Each cycle uses exactly two link edges" gives one cycle of L (lines 54-57, 74-79). CORRECT, one wording fix.

- Lemma 1, x = 4: x > 0 puts an H-edge across the cut, and both its ends are in S, so S meets
  both sides. Each of C1, C2 has vertex set S, so each crosses the cut an even, positive number
  of times; edge-disjointness splits the 4 crossing edges as 2 + 2. Correct.
- Degree 2 in L: the two link edges of Ci at Γ_u are distinct edges of G, so they are distinct
  L-edges at u (bijection, item 2), each contributing 1 to deg(u) because L has no loops. Vertices
  of L outside U meet no edge of Ci. So (U, E_i) is 2-regular. Its edges have both ends in U
  because both ends of a link edge of Ci lie in S.
- Connectivity: the phrase "contracting each copy to a point is a continuous image of the cycle"
  (line 76) is informal. The rigorous version is one line: walk around Ci and record the copy of
  each vertex; consecutive vertices are in the same copy or in two copies joined by an edge of
  E_i, and the walk visits every copy in U because V(Ci) = S. Suggested fix: replace the
  topological phrase by this walk argument. No mathematical gap.
- A connected, loopless, 2-regular multigraph is a cycle. |U| = 2 gives two parallel L-edges,
  which is a cycle under the convention of line 9. |U| = 1 cannot occur: it would mean
  S ⊆ V(Γ_u), already excluded at line 69 (the loopless argument in line 78 is a second reason).
  If |U| >= 3 the cycle cannot use two parallel edges, since those two edges alone would form a
  component. Correct.

### A4. Edge-disjointness and "same vertex set" survive the projection (lines 78-80). CORRECT.

V(E_1) = V(E_2) = U because both are 2-regular exactly on U. The link edges of C1 and C2 are
disjoint sets of G-edges and the map from link edges to L-edges is a bijection, so E_1 and E_2
share no L-edge. They may use different parallel copies of the same L-pair, which is exactly what
the multigraph definition of a pair allows. If |U| = 2 the projected pair is two 2-cycles on
{u, w} and needs multiplicity >= 4 on uw; a pair-free L excludes that, consistent with line 9.

### A5. Bipartiteness of the substitution (lines 29-32). CORRECT.

Classes P = O(Γ_u) for u ∈ X plus I(Γ_w) for w ∈ Y, and Q = the rest. Gadget edges join I to O
inside one copy, so they cross P/Q in both kinds of copy. A link edge of an L-edge uw has u ∈ X,
w ∈ Y (L bipartite) and joins O(Γ_u) ⊆ P to O(Γ_w) ⊆ Q. Every edge crosses.

### A6. Γ5 is pair-free and is a 5-gadget (lines 84-94). CORRECT (hand check; machine check in B1).

- Edge count 9 + 7·3 = 30. Degrees by hand: a1, a2, a3, x4, x5, x6 all 5; b1, b2, b3, o4 all 5;
  o5 = 4, o6 = 3, o7 = 3. Deficiencies 1, 2, 2 sum to 5. Every edge joins I to O, |O| = 7 =
  |I| + 1, no repeated edge. So Γ5 is a 5-gadget.
- Each added vertex has exactly three earlier neighbors (checked for x4, o4, x5, o5, x6, o6, o7),
  so Γ5 is 3-degenerate: the last vertex (in this order) of any subgraph has at most 3 neighbors
  in it, and a subgraph inside the K_{3,3} has max degree 3. A pair is 4-regular on its vertex
  set, so Γ5 has none. Correct.

### A7. L5 is pair-free (lines 96-107). CORRECT (re-derived; machine check in B1).

Re-derivation. The underlying simple graph is the 8-cycle Z = x0 y2 x1 y1 x2 y0 x3 y3 x0 plus the
chords x1y3 and x3y1. On Z (positions 0..7 = x0, y2, x1, y1, x2, y0, x3, y3) the chords are
(2, 7) and (3, 6), nested, not crossing. Cycles:
- chord x1y3 alone: x0 y2 x1 y3 (= A, 4 vertices) and x1 y1 x2 y0 x3 y3 (= B + C, 6 vertices);
- chord x3y1 alone: x2 y0 x3 y1 (= B) and x3 y3 x0 y2 x1 y1 (= A + C);
- both chords: the 4 chord ends cut Z into arcs {2-3}, {3..6}, {6-7}, {7..2}; a single cycle must
  use the arcs {2-3} and {6-7}, giving x1 y1 x3 y3 (= C); the other choice splits into A and B;
- no chord: Z (= A + B + C).
So exactly six cycles, matching lines 102-104, with six distinct vertex sets. Multiplicities: no
pair has multiplicity 4 (max is 3), and each of the six cycles contains an edge of multiplicity 1
(A: x1y3; B: x3y1; C, A+C, B+C, Z: x1y1). One step is implicit: a cycle of length >= 3 in a
multigraph uses at most one edge from each parallel class (two parallel edges would already close
a 2-cycle component), so it projects onto a simple cycle with the same vertex set. With that, the
argument is complete. The multigraph cycle count is 14 two-cycles plus 18 + 18 + 1 + 18 + 18 + 324
longer ones = 411, matching line 122.

### A8. Corollaries B and C.

Corollary B (lines 125-157). CORRECT. Machine check (review/a8_cor_b.py, review/a8_cor_b.log):
K has no pair at all (15 multigraph cycles enumerated); all 1296 ways of attaching the K-edges to
the a/c vertices of L6 give a 6-regular multigraph with no pair; L6b is 6-regular, bipartite and
pair-free. The exact multigraph test used there agrees with plain cycle enumeration on 355 random
multigraphs (254 with a pair).
- K: degrees 4 each; its simple graph is the 4-cycle 0-3-1-2-0; a Hamilton cycle of a 4-vertex
  multigraph has length 4 and projects onto that 4-cycle, so two edge-disjoint ones would need 02
  and 13 twice. Correct.
- L6: piece degrees a = 3 + 1 = 4, b = 6, c = 4; each piece gets 4 K-edges (2 at a, 2 at c), so
  6-regular on 12 vertices. L6b: piece degrees 4, 6, 6, 4; the orientation lists 8 arcs, one per
  K-edge (03 three times, 12 three times, 02, 13), and every vertex has out-degree 2 and in-degree 2,
  so d and a each get two outside edges: 6-regular on 16 vertices. Bipartite with classes {a, c}
  and {b, d} in every piece, since outside edges join d to a. Correct.
- Pieces are pair-free: two edge-disjoint cycles on the same vertex set inside a piece need the
  single edge twice or four parallel edges. Correct.
- C1 is stated for simple graphs, but its parity proof works verbatim in multigraphs (a 2-cycle
  across a cut uses 2 cut edges). With 4 edges around each piece, a pair that meets a piece and
  leaves it uses all 4, 2 per cycle; the neighboring pieces are then met and left, so by
  connectivity of K every piece is met, and contracting gives two edge-disjoint Hamilton cycles
  of K. Correct. The assignment of K-edges to a/c in L6 is unspecified; the argument covers every
  assignment.
- B − o is a 6-gadget: B is simple (FACTS.md convention), X − o keeps degree 6, |Y| = |X| =
  |X − o| + 1, and the six neighbors of o are distinct, each of deficiency 1. Assigning the 6
  L-edges at u bijectively to the 6 deficient vertices of Γ_u makes parallel L-edges get distinct
  ends at u, so G is simple. Theorem R1 applies with d = 6 <= 7. The equivalence is correct in
  both directions.

Corollary C (lines 159-173). Both counting claims CORRECT; the closing sentence overstates.
- Claim 1: in a 3-degenerate bipartite graph the first six vertices of a degeneracy order span at
  most 9 edges (bipartite on 6 vertices), each later vertex adds at most 3, so e <= 3n - 9 for
  n >= 6. With n = 2|I| + 1 this is 6|I| - 6. d = 5 needs |I| >= 6 (Γ5 meets it with equality,
  30 = 6·6 - 6); d = 6 never. A 6-gadget has |I| >= 5 (each I-vertex has 6 distinct O-neighbors),
  so n >= 11 and the n >= 6 hypothesis holds. Correct.
- Claim 2: B2a' re-checked: base n = 3, 4; a vertex of degree <= 3 is removed; otherwise a cut
  with a part of size a <= 4 has at least a(5 - a) >= 4 edges, so both parts have >= 5 vertices and
  e <= 3n - 9. Its hypothesis passes to subgraphs. A 6-gadget has 6|I| = 3n - 3 > 3n - 6 edges, so
  it has a subgraph of minimum degree >= 4 with no edge cut of size <= 3. Correct.
- GAP (wording only): line 172 says the substitution "stops at degree 5". What is proved is
  narrower: a pair-free 6-gadget cannot be certified by 3-degeneracy or by cuts of size <= 3.
  Corollary B itself shows the substitution works at degree 6 if any pair-free 6-gadget exists.
  "Each stops at the same edge count 3n" is a heuristic summary (the proved thresholds are 3n - 9
  for bipartite degeneracy and 3n - 6 for cuts, against 3n - 3 for a 6-gadget), not a theorem.
  Suggested fix: say "none of the three easy certificates can produce a pair-free 6-gadget".

### A9. Text versus data. GAP (documentation only; see B1 for the evidence)

Lines 109-110 describe the link rule as "for a triple edge of L5 the three link edges use o5-o5,
o6-o6, o7-o7". The rule is realizable (the four triple edges of L5 form a perfect matching x0y3,
x1y2, x2y1, x3y0, so every copy has exactly one triple edge and its o5 can go there). But
data/bip5-avoider-104.edges does not follow it: for the triple edge between blocks 0 and 7 the
three ends in block 0 are o6, o7, o7, and block 0's o5 (vertex 10) goes to block 6 instead. No
triple edge in the file is realized as o5-o5, and the o5 of six of the eight copies (all but
blocks 3 and 7) sits on a non-triple edge. The file is still a valid substitution of Γ5 into L5 (B1), and
Theorem R1 needs no particular rule, so Corollary A is unaffected. Suggested fix: say "one valid
substitution, for example ..." or describe the rule the file actually uses.

## B. Independent machine check of data/bip5-avoider-104.edges

All code is in review/ and was written for this review; nothing under tools/ was read or used.
Logs: review/b1_structure.log, review/test_dp.log, review/cache104/block_*.txt,
review/b2_combine104.log, review/b2_combineP1.log, review/b2_combineP2.log,
review/b2_combineN1.log, review/b2_combineN2.log, review/b2_cport_compare.log,
review/test_pairbf.log, review/ilp104.json.log, review/d5_random.log.
Disclosure: after the B2 verdict was complete, a directory check printed the first five lines of
the author's data/bip5-ilp.log (summary lines only). Nothing in this review depends on it.

### B1. Basic properties and substitution structure (review/b1_structure.py). ALL PASS.

- Vertex labels exactly 0..103; 260 edge lines; no loops; no repeated edge (simple); every vertex
  has degree 5; bipartite (own BFS 2-coloring, classes 52/52, and networkx); connected.
- Γ5 rebuilt from the text of lines 84-87: 13 vertices, 30 distinct I-O edges, I-degrees 5,
  O-degrees 5,5,5,5,4,3,3, deficiencies 1,2,2; its 4-core is empty (3-degenerate), so it has no
  4-regular subgraph and no pair.
- L5 rebuilt from lines 96-98: 5-regular, 20 edges; plain enumeration of all 411 multigraph cycles
  (matches line 122) finds no two edge-disjoint cycles on one vertex set.
- The 8 blocks {13k, ..., 13k+12} each induce a copy of Γ5 (isomorphism respecting the I/O sides);
  the 20 remaining edges join different blocks, sit only on O-vertices, and each O-vertex carries
  exactly 5 - (internal degree) of them; the quotient multigraph is isomorphic to L5 with
  multiplicities (block k = x_k for k <= 3, y_{k-4} for k >= 4). So the file is a substitution of
  Γ5 into L5 in the sense of lines 19-26, and Theorem R1 applies to it.
- The file does not follow the link rule written on lines 109-110 (see A9). Not a correctness issue.

### B2. Exact pair test by block decomposition (review/pairdp.py). RESULT: NO PAIR.

Method. A pair is the same thing as a coloring c: E -> {0, red, blue} with
(V) every vertex has (red degree, blue degree) equal to (0, 0) or (2, 2), and
(G) the red edges form exactly one cycle and the blue edges form exactly one cycle.
(Given a pair, color C1 red and C2 blue. Conversely (V) gives V(red) = V(blue) and (G) makes each
color a cycle; the colors share no edge.)
Partition V into blocks. (V) only involves the edges at one vertex, so restricted to the edges
with an end in a block P (internal plus boundary edges) the coloring is a "local coloring" of P
that satisfies (V) on P; local colorings that agree on all boundary edges glue back to a global
coloring that satisfies (V). For each local coloring I record its signature: the colors of the
boundary edges, and for each color the matching of that color's boundary edges given by the
paths inside P, plus the number of closed cycles of that color lying entirely inside P. The
global red subgraph is then the disjoint union of the internal closed red cycles and the cycles of
the "link structure" (nodes: red edges between blocks; one arc for each matched pair in each
block), so its number of cycles is determined by the signatures, and likewise for blue.

Completeness argument.
1. The local enumerator is exhaustive: it walks the block's vertices in a fixed order and at each
   vertex tries every one of the patterns allowed by (V) (1 + 30 for degree 5) that agree with the
   edges already fixed; every valid local coloring is produced exactly once. Checked against a
   naive 3^m enumeration on 60 random blocks: 0 mismatches.
2. The only pruning is a filter that drops a signature if, for some color, it has two or more
   internal closed cycles, or one internal closed cycle and a boundary edge of that color. Such a
   block always contributes at least two components of that color (an internal closed cycle
   touches no boundary edge), so (G) fails for every global coloring using it.
3. The combine step enumerates every choice of one boundary coloring per block that agrees on
   every edge between blocks (backtracking with an agreement check per edge), then every choice of
   surviving signature per block, and evaluates (G) exactly with a union-find over the link
   structure plus the internal cycle counts.
4. So a pair exists if and only if some combination passes. The partition can be anything; it
   only affects running time. Here it is the 8 blocks of 13 vertices.

Result on the 104-vertex graph:
- Every block has 923,041 local colorings (including the empty one), 31 distinct boundary
  colorings and 237 signatures (review/cache104/block_*.txt). Every nonempty local coloring
  uses exactly 2 red and 2 blue boundary edges and leaves the fifth unused. This is an
  independent, purely local confirmation of the x = 4, two-plus-two conclusion of Lemma 1 for Γ5
  (the enumeration does not use the counting argument).
- 260,736 of the nonempty local colorings have no internal closed cycle; each of them is one
  red path and one blue path through the block. This equals the "260,736 traces" of line 120.
  The other 662,304 contain an internal closed cycle.
- Of the 30 patterns (one unused, two red, two blue) on the 5 boundary edges, 20 occur without an
  internal closed cycle: exactly those in which neither deficiency-2 vertex (o6, o7) has both of
  its link edges in the same color. The other 10 occur only with an internal cycle.
- After the filter each block keeps 21 boundary colorings (20 plus empty) and 21 signatures.
  The combine step reaches 417 boundary-consistent assignments (one of them all-empty) and checks
  417 signature combinations; none satisfies (G). RESULT: no pair (review/b2_combine104.log).
- Compute: about 135 s per block in Python, 8 blocks in parallel; combine under 1 s. Total about
  18 CPU-minutes, about 2.5 minutes wall clock.

Validation of the checker itself.
- Random small graphs (G(n,p) with n <= 9, random 4-, 5- and 6-regular graphs, random bipartite
  graphs, with random edge deletions) and random partitions into 1 to 4 blocks. Logged runs
  (review/test_dp.log, two seeds): 283 graphs, 126 with a pair and 157 without. The DP verdict
  equals the verdict of a separate brute force (all cycles, grouped by vertex set, two
  edge-disjoint ones in a group) in every case, and every pair either method returned passed an
  independent verifier (verify_pair: both colors are single cycles, edge-disjoint, same vertex
  set, edges in the graph). Two earlier runs of the same script (505 graphs with a slightly larger
  generator, and 262 graphs that include the first logged run) also had 0 mismatches; their
  output went to the console only.
- Positive controls with the same gadget (review/b2_controls.py, review/controls/):
  P1 = Γ5 substituted into the 4-vertex 5-regular bipartite multigraph x0y0^4, x1y1^4, x0y1, x1y0,
  which has a pair (two 2-cycles). The DP finds a pair on 22 vertices, verified.
  P2 = Γ5 substituted into a doubled 8-cycle plus a perfect matching (pair: two 8-cycles). The DP
  finds a pair on 88 vertices through all 8 copies, verified. The cycles are printed in
  review/b2_combineP1.log and review/b2_combineP2.log. So the same code on the same gadget does
  find pairs when L has one; the "no pair" verdict on the 104-vertex graph is not vacuous.
- Negative controls, two more valid substitutions of Γ5 into L5: N1 follows the link rule written
  on lines 109-110 (o5-o5, o6-o6, o7-o7 on every triple edge); N2 is a random valid assignment
  (seed 7). The DP reports no pair for both (419 and 705 boundary-consistent assignments
  checked; review/b2_combineN1.log, review/b2_combineN2.log). So Theorem R1's "every
  substitution" claim holds on three different substitutions of Γ5 into L5, not only the file.
- Speed port. The machine was heavily loaded by other jobs during this review (load average
  about 90 on 18 cores), so the per-block enumeration was ported to C (review/blocksig.c,
  wrapper review/b2_block_c.py). The C port is trusted only because it reproduces the Python
  enumerator exactly: same local coloring count and identical signature sets on all 28 blocks
  of the 104-vertex graph, P1, P2 and N1 (review/b2_cport_compare.log). N2 was computed with
  the C port. The 104-vertex verdict above comes from the Python enumerator.

### B3. Second method, integer program with lazy cuts (review/b3_ilp.py). INCOMPLETE; not used as evidence.

Variables r_e, b_e, s_v in {0, 1}; degree constraints sum r = 2 s_v and sum b = 2 s_v at every
vertex, r_e + b_e <= s_u for both ends, sum s >= 1; whenever a solution has a color with several
cycles, add for each cycle T and vertices u ∈ T, w ∈ S \ T the cuts
r(δ(T)) >= 2(s_u + s_w - 1) and b(δ(T)) >= 2(s_u + s_w - 1), which every pair satisfies. Solver:
scipy.optimize.milp (HiGHS). It behaves correctly on small cases (finds a verified pair in K34
into L2 in 4 rounds; proves K34 into K pair-free in 2 rounds). On the 104-vertex graph it ran
48 rounds and added 13,380 cuts without converging (every round found a new 4-regular subgraph
whose color classes split into 2 to 9 cycles, with |S| between 44 and 102), and I stopped it
because the machine load had reached about 147. It found no pair in those rounds, but an
unconverged lazy-cut loop proves nothing, so this review's verdict rests on B2 alone. State and
log: review/ilp104.json, review/ilp104.json.log.

### B4. Extra degree-5 tests of Theorem R1 with random skeletons (review/d5_random.py)

Γ5 substituted (random valid link assignment) into random connected 5-regular loopless
multigraphs L on 4, 6 or 8 vertices with multiplicities at most 3, alternating L pair-free and L
with a pair (L's status by the exact multigraph test of review/a8_cor_b.py). Pair test: the block
DP, block phase by the validated C port. All 12 generated skeletons happen to be non-bipartite,
which Theorem R1 allows. review/d5_random.log, graphs in review/d5/.

- L pair-free (trials 0, 2, 4, 6, 8, 10; L on 6, 8, 8, 6, 6, 8 vertices, so G has 78 to 104
  vertices): no pair in all six. Theorem R1 holds.
- L with a pair (trials 1, 3, 5, 7, 9, 11): verified pairs in five (44 vertices for the four
  4-vertex skeletons, 88 vertices for the 8-vertex one). Trial 7 has no pair, and the reason is
  checkable by hand: its L (on 0..3, multiplicities 01:1, 02:3, 03:1, 12:1, 13:3, 23:1) has only
  one kind of pair, the Hamilton cycles 0-1-3-2-0 and 0-2-1-3-0 on different copies of 02 and 13.
  The three link edges between copies 1 and 3 are o6-o7, o7-o6 and o5-o5. Γ5 never lets a cycle
  pass when a deficiency-2 vertex has both of its link edges in one color (B2). At copy 1 this
  rules out o6-o7 for red and o7-o6 for blue; at copy 3 it rules out o7-o6 for red and o6-o7 for
  blue. So both cycles would need the o5-o5 edge, which is impossible. The converse direction
  therefore depends on the link assignment; Theorem R1 does not claim it.

## C. Sanity tests of Theorem R1 at degree 4 (review/c_degree4.py, review/hdsearch.py)

Gadgets (both pair-free by brute force, both checked to be 4-gadgets):
- K34 = K_{3,4}: I = 3 vertices of degree 4, O = 4 vertices of degree 3 (deficiency 1 each).
  Its automorphisms permute O arbitrarily, so all substitutions of K34 into a given L are
  isomorphic; one per L is enough.
- G4b, an asymmetric 4-gadget: I = {a1, a2, a3, x4}, O = {b1, b2, b3, o4, o5}; edges K_{3,3} on
  a's and b's, x4 ~ b1 b2 b3, o4 ~ a1 a2 x4, o5 ~ a3. Deficiencies o4: 1, o5: 3. 3-degenerate.
  Three random valid substitutions per L.

Skeletons (loopless 4-regular multigraphs; pair status by plain enumeration of all cycles):
L2 = two vertices joined by 4 parallel edges (pair), C4x2 = doubled 4-cycle (pair), Tri2 =
doubled triangle (pair), K5 (pair), K = the 4-vertex multigraph of Corollary B (pair-free),
C6(3,1,3,1,3,1) = 6-cycle with multiplicities 3,1,3,1,3,1 (pair-free).

Three pair tests per substitution G, every reported pair re-checked by verify_pair:
(1) pairbf (review/pairbf.c): plain enumeration of every cycle C1, each with a Hamilton-cycle
    search in G[V(C1)] - E(C1); complete when it finishes. Cross-checked against the Python brute
    force and the DP on random small graphs (review/test_pairbf.log).
(2) the block DP of B2 with blocks = copies.
(3) review/hdsearch.py, a Hamiltonian-decomposition search. Complete here by a one-line reduction:
    in a connected 4-regular graph, C1 ∪ C2 is 4-regular on S, so every vertex of S has all its
    neighbors in S, so S = V and the pair is a Hamiltonian decomposition of G.

| gadget | L | L has a pair | n | prediction | pairbf | DP | HD search |
|---|---|---|---|---|---|---|---|
| K34 | L2 | yes | 14 | pair (converse intuition) | pair, verified | pair, verified | pair, verified |
| K34 | C4x2 | yes | 28 | pair (converse intuition) | pair, verified | pair, verified | pair, verified |
| K34 | Tri2 | yes | 21 | pair (converse intuition) | pair, verified | pair, verified | pair, verified |
| K34 | K5 | yes | 35 | pair (converse intuition) | pair, verified | pair, verified | pair, verified |
| K34 | K | no | 28 | no pair (Theorem R1) | none (complete, 5,778,951 cycles) | none | none (complete) |
| K34 | C6(3,1,..) | no | 42 | no pair (Theorem R1) | timeout | none | none (complete) |
| G4b | L2 | yes | - | no simple substitution exists | - | - | - |
| G4b x3 | C4x2 | yes | 36 | pair (converse intuition) | none (complete, 45,212,992 cycles each) | none | none (complete) |
| G4b x3 | Tri2 | yes | 27 | pair (converse intuition) | none (complete, 551,980 cycles each) | none | none (complete) |
| G4b x3 | K5 | yes | 45 | pair (converse intuition) | timeout | none | none (complete) |
| G4b x3 | K | no | 36 | no pair (Theorem R1) | none (complete, 40,507 cycles each) | none | none (complete) |
| G4b x3 | C6(3,1,..) | no | 54 | no pair (Theorem R1) | timeout | none | none (complete) |

Findings.
- Theorem R1: 0 violations. Every substitution with L pair-free (8 graphs) has no pair, by at
  least two complete methods each.
- Converse direction: it holds for K34 (all four skeletons with a pair give a verified pair) and
  fails for G4b (all nine substitutions into skeletons with a pair are pair-free). This is not a
  counterexample to anything claimed, since Theorem R1 is one-directional. The reason is local:
  in G4b the vertex o5 has one gadget edge and three link edges, so in a pair (where S = V at
  degree 4) one color uses two of o5's link edges, its path through the copy is the single vertex
  o5, and the other vertices of the copy then carry a closed cycle of that color inside the copy.
  The HD search dies inside the first copy (145 nodes) for every G4b graph, matching this.
- G4b into L2 has no simple substitution: the 4 parallel edges need 4 distinct end pairs, but the
  slot multisets are {o4, o5, o5, o5} on both sides, which give at most 3 distinct pairs.
- Limitation: at degree 4 a pair in a connected regular graph must use every vertex, so these
  tests only exercise the case S = V. Partial S is exercised at degree 5 in B: P1's pair uses 22 of
  52 vertices, and the negative controls N1, N2 and the 104-vertex graph cover every S.
- Logs: review/c_degree4.log (pairbf and DP), review/c_hdsearch.log (HD search). The pairbf
  timeouts are wall-clock limits of 50 to 60 s under heavy machine load; they are reported as
  incomplete and not used as evidence.

## Verdicts

- **Lemma 1: SOUND.** Every step follows from the definitions (A1-A3). The count
  x = 4(|S_O| - |S_I|) has no hidden assumption beyond "link edges sit only on O-vertices, there
  are no O-O or I-I edges inside a copy, L is loopless and d-regular". Independently, the exhaustive
  local enumeration in B2 shows that for Γ5 every nonempty local coloring uses exactly 2 red and
  2 blue link edges.
- **Theorem R1: SOUND WITH FIXES (wording only).** Fix: replace "contracting each copy to a
  point is a continuous image of the cycle" (line 76) by the one-line walk argument of A3. No
  counterexample at degree 4 (8 pair-free-L substitutions, two gadgets, all pair-free by at least two
  complete methods) or degree 5 (three substitutions of Γ5 into L5, and Γ5 into six random
  pair-free 5-regular skeletons in B4, all pair-free by the exact DP).
- **Corollary A: SOUND WITH FIXES.** The conclusion is independently machine-verified: the
  104-vertex graph is simple, bipartite, 5-regular, a substitution of Γ5 into L5, and has no pair
  by an exact, complete block DP whose "yes" answers were validated on positive controls. Fixes:
  (1) lines 109-110 describe a link rule that data/bip5-avoider-104.edges does not follow (A9);
  (2) in the L5 proof, state that a cycle of length >= 3 in a multigraph uses one edge per
  parallel class and so projects onto a simple cycle with the same vertex set (A7).
- **Corollary B: SOUND WITH FIXES (citation scope only).** K, all 1296 versions of L6 and L6b are
  machine-checked pair-free, 6-regular, and L6b bipartite (review/a8_cor_b.log). Fix: C1 is stated
  for simple graphs (FACTS.md line 3) but is applied to the multigraphs L6 and L6b; say that its
  parity proof holds verbatim for multigraphs. Optional: note that the argument covers every
  attachment of K-edges to the a/c vertices of L6, which line 131 leaves unspecified.
- **Corollary C: SOUND WITH FIXES.** Both counting claims are correct (A8). Fix: lines 172-173
  overstate. What is proved is that no pair-free 6-gadget can be certified by 3-degeneracy or by
  cuts of size <= 3; Corollary B shows the substitution itself works at degree 6 if a pair-free
  6-gadget exists. "Each stops at the same edge count 3n" is a heuristic summary (the proved
  thresholds are 3n - 9 for bipartite degeneracy and 3n - 6 for cuts, against 3n - 3 for a
  6-gadget).

Statements in PROOF-R1.md this review could not verify:
1. Lines 3-4: the status and rung labels (process statements, not mathematics).
2. Lines 59-62 (Remark): that tools/gadget_traces.py checks Lemma 1 "for d = 5 and d = 6 ... for
   one gadget each". The program was not read, by instruction. The d = 5 statement for Γ5 is
   confirmed by this review's own enumeration; the d = 6 gadget is not named in PROOF-R1.md and
   was not checked.
3. Lines 111-112: that tools/bip5.py built the file and checks it. The properties it is said to
   check (simple, bipartite, 5-regular) were verified independently.
4. Line 117: "The project's bipartite record was degree 4" (project history).
5. Lines 119-123: the author's own tool runs and integer-program results as such. Their content was
   reproduced by different code: 260,736 traces (matches, B2), 411 cycles of L5 and no pair
   (matches, B1), no pair in the 104-vertex graph (matches, B2). This review's own integer program
   is reported in B3.
6. Lines 138-139: "Both were also checked by cycle enumeration and by the integer program"
   (author's runs). Pair-freeness of L6 and L6b was re-checked here by different code.
7. Lines 172-173: the closing summary of Corollary C, which is heuristic as written.
Out of scope: FACTS.md beyond C1 and B2a' (both re-checked, A8).
