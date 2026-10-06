# Bipartite-hamilton lane: Lemma BM (bipartite Müyesser) written out in full

> **Review status (added by the lane lead, 2026-10-04).** Heavy independent review:
> `BM-REVIEW.md` (FINAL). **No gap found: Theorem BM holds at c = 5, and at c = 6
> under the conservative reading of Müyesser's Lemma 4.7.** Lemma B4.7 is ACCEPTED WITH FIX (one
> clarifying sentence). Lemma Ch, Part 2, Lemmas B2.2 and R2, the Section 4 quotes, and the
> divisibility step are ACCEPTED. Corollary BM-2 is ACCEPTED WITH
> FIX. Fixes, none affecting validity:
> - F1: [Omitted from this copy.]
> - F2: the c = 6 fallback constants are d >= 65 C_BM δ^-6 (log n)^3, and d >= 2^13 C_γ γ^-12 (log n)^3
>   with C_γ = 32^6 C_BM.
> - F3: add one sentence on merged template connections of length >= 2.
> - F4: two sanity checks are not load-bearing ("40/40 proper" holds by construction; the sampling
>   test used multigraphs).
> - F5: the (P2) union bound is about 2n^-2.
> - F6: the δ^2 argument also improves Müyesser's non-bipartite Theorem 1.3 to δ^-5. A third
>   reader should check this before it is mentioned outside the project.
> - F7: two more harmless typos in Müyesser's paper.
> Still trusted, not re-derived: Haxell's theorem, the Alon-Hoory-Linial Moore bound, Tropp's
> matrix Bernstein, hypergeometric Chernoff bounds, and BJ Lemma 3.3.


Lane: bipartite-hamilton. Session 2026-10-04. Status: FINAL (Sections 0-11; the log sits just before the summary).

Rungs: (a) proof, (b) special case, bound or counterexample, (c) literature find, (d) formalization.

## 0. Bottom line

1. **Theorem BM holds, with exponent c = 5** (rung (a), written proof below, unpublished
   adaptation, needs heavy review). There is an absolute constant C_BM such that every bipartite
   d-regular n-vertex graph G with λ2(G) <= (1-δ)d, δ in (0,1), and d >= C_BM δ^-5 (log n)^3 is
   Hamiltonian. Taking Müyesser's Lemma 4.7 exactly as stated gives c = 6 (his exponent). The
   improvement to 5 comes from slack in his Lemma 4.7, which asks for δ^3 where δ^2 suffices
   (Section 10, item U3). If a reviewer rejects that, c = 6 holds with no other change.
2. **Edge-expansion form, c' = 10** (rung (a)). A bipartite d-regular γ-expander (Bradač-Janzer
   sense) with d >= C_γ γ^-10 (log n)^3 is Hamiltonian, via BJ Lemma 3.3 (δ = γ^2/32).
3. **Corollary** (rung (a)). If λ2(G) <= (1-δ)d and d >= 33 C_BM δ^-5 (log n)^3, or G is a
   γ-expander with d >= 2^11 C_γ γ^-10 (log n)^3, then G minus one Hamilton cycle satisfies the
   hypotheses again (with δ/2 or γ/2), so G has two edge-disjoint Hamilton cycles: a pair with
   support V(G).
4. **No obstruction.** Nothing in Müyesser's proof uses odd cycles, a two-sided gap, or mixing
   between the sides. Four things change:
   - Lemma 2.2 becomes Lemma B2.2: sample U ⊆ P and V ⊆ Q independently. The proof is shorter
     than the original and drops the hypothesis p <= δ/100.
   - Every random set is chosen inside one side; layers alternate sides; there are 2τ layers.
   - A new parity lemma (R2): an A,B-Hamilton router with A ⊆ P and B ⊆ Q has equally many
     vertices on each side. So the leftover after the router is balanced.
   - The divisibility step. The remainder r < k is removed by contracting r disjoint P-Q-P paths of
     3 vertices ("cherries") into super-vertices, found greedily in spare layers (Lemma Ch, Section 6
     Steps 4-7). [Omitted from this copy.]
5. **Checks** (rung (b), sanity only). Lemma 4.5's explicit pairing verified for every even cycle
   length 6..600. Proposition 4.4 verified for router orders 2..9. 40 random basic routers built
   from Lemma 4.5 comparators with random subdivisions, embedded in bipartite 2-colorings with
   A in P and B in Q, orders 2..5, up to 128 vertices: all proper, all balanced, and the router
   property holds for every bijection. Negative controls fail as expected.
6. **Effect on the spectral lane.** Proposition C there (bipartite expanding hosts, K = 3) no
   longer depends on an unwritten lemma; it depends on this write-up passing review, and its
   γ^-12 becomes γ^-10.

**Independent review needed: YES, heavy** (an unpublished adaptation of a 13-page proof; start
with Sections 5.1, 5.4, 5.5 and 6).

## 1. Sources, verified against the PDF text

Fetched 2026-10-04 with `curl -sL -A "openmath-research-lane/1.0"` into the session scratchpad
(`bipartite-hamilton/`), converted with pdftotext (plain and `-layout`).

**Müyesser, "Hamiltonicity of mildly pseudorandom regular graphs", arXiv:2609.35766v1** (13 pages,
read in full).
- Theorem 1.3: "Let G be an (n, d, λ)-graph. If λ ≤ (1 − δ)d and d ≥ C · δ^−6 (log n)^3, where
  δ ∈ (0, 1) and C is a sufficiently large absolute constant, then G is Hamiltonian."
- After Corollary 1.4: "An analogous result can be obtained for bipartite graphs with one-sided
  spectral gap as well, as was done in [5], but we do not pursue this here." ([5] = Bradač-Janzer.)
- Lemma 2.2 assumes "p ≤ δ/100 and D ≥ C_a δ^−2 log n", C_a = 30000(a + 4), and samples "(U, V)
  uniformly among all ordered pairs of disjoint m-subsets of V(G)".
- Lemma 2.4 sets "c = max_{j∈[s]} ∥f_j∥_2" (Euclidean norm, not squared) and bounds
  P(∥F_I∥ > √q ∥F∥ + c√t) ≤ r(s + 1)e^−t.
- Lemma 4.7 assumes "0 < q ≤ δ/100 with qn ∈ 2N", "qd ≥ Kδ^−4 (log n)^2", "every v ∈ R satisfies
  d_H(v, A ∪ B) ≤ cδ^3 qd/log n", and "k ≤ cδ^3 |R|(log n)^−2".
- Main proof: "put q := c0 δ and k := c1 δ^3 qn/L^2" (L is log n), "Set h := 2qk and
  m := k − h = (1 − 2q)k". Divisibility: "we assume that all set sizes below are integers and that
  k divides n − |V(S)| once the router S has been found. These assumptions can be removed by
  starting the proof by finding a short path whose remainder is appropriately divisible,
  contracting the vertices of the short path, and essentially following the below proof verbatim."
- Typos noticed (harmless): Lemma 4.5 says "Let M0 be the perfect matching of C matching c0 to
  c2"; it must be the matching {c0c1, c2c3, ...}, since c0c2 is not a cycle edge and the next
  sentence uses the path c0-c1 in M0 ∪ P. The main proof says "k ≤ cδ^3 |R| log log n/ log(n)^2";
  the intended bound is k ≤ cδ^3|R|/(log n)^2.

**Bradač, Janzer, "Hamiltonicity of regular sublinear expanders", arXiv:2605.15043v1** (47 pages;
read the statements used and Section 3.1).
- Theorem 1.3: "Let G be a bipartite n-vertex d-regular γ-expander and assume that n is
  sufficiently large. If d > (γ^−1 log n)^(10^8), then G is Hamiltonian."
- Corollary 1.4: "Let G be a bipartite n-vertex d-regular graph and assume that n is sufficiently
  large. If λ2(G) = (1 − δ)d and d > (3δ^−1 log n)^(10^8), then G is Hamiltonian."
- Lemma 3.3 ([19] = Draganić-Methuku-Munhá Correia-Sudakov): "If G is a (d ± d′)-nearly regular
  γ-expander with d′ ≤ d/4, then λ2(N(G)) ≤ 1 − γ^2/32", where N(G) = D^(1/2) A D^(1/2) with
  D_ii = 1/d_G(i). For d-regular G, N(G) = A/d, so λ2(G) <= (1 - γ^2/32)d.
- Definition 3.1 ("(V0, V1)-alternating") is how BJ treat bipartite and far-from-bipartite hosts in
  one framework; this is the "as was done in [5]" of Müyesser's remark.
- γ-expander (Definition 1.2): e_G(S, V(G) \ S) ≥ γ d̄(G)|S| for every S with 1 ≤ |S| ≤ 2n/3.

## 2. Statements proved here

Notation. log is the natural logarithm, L := log n. For a graph G, λ2(G) is the second largest
adjacency eigenvalue. A d-regular bipartite G with parts P, Q has |P| = |Q| =: N = n/2 (count the
edges from each side). Let W in {0,1}^(P x Q) be its biadjacency matrix. The adjacency spectrum is
{±s_i(W)}, so λ1 = d = s1(W), λ2(G) = s2(W) and λn = -d. The one-sided condition
λ2(G) <= (1-δ)d therefore puts all eigenvalues other than ±d in [-(1-δ)d, (1-δ)d]; it implies that
G is connected.

> **Theorem BM.** There is an absolute constant C_BM such that the following holds. Let G be a
> bipartite d-regular graph on n vertices with λ2(G) <= (1-δ)d for some δ in (0,1). If
> d >= C_BM δ^-5 (log n)^3, then G is Hamiltonian.

> **Theorem BM-γ.** Let C_γ := 32^5 C_BM. If G is a bipartite d-regular n-vertex γ-expander
> (e_G(S, V \ S) >= γd|S| whenever 1 <= |S| <= 2n/3), 0 < γ <= 1, and d >= C_γ γ^-10 (log n)^3,
> then G is Hamiltonian.

> **Corollary BM-2.** Let G be bipartite and d-regular on n >= 4 vertices. If either
> (a) λ2(G) <= (1-δ)d with δ in (0,1) and d >= 33 C_BM δ^-5 (log n)^3, or
> (b) G is a γ-expander as above and d >= 2^11 C_γ γ^-10 (log n)^3,
> then G has two edge-disjoint Hamilton cycles. In particular G contains a pair (two edge-disjoint
> cycles with the same vertex set) with support V(G).

## 3. Lemma-by-lemma correspondence

| Müyesser (arXiv:2609.35766) | Bipartite version here | How it transfers |
|---|---|---|
| Thm 2.3 (matrix Bernstein, Tropp) | same | verbatim, a matrix statement |
| Lemma 2.4 (column sampling) | same | verbatim, a matrix statement |
| Lemma 2.2 (subsampling keeps a gap) | **Lemma B2.2**: U ⊆ P, V ⊆ Q independent uniform m-sets; s2(G[U,V]) <= (1-δ/2)D once D >= 32(a+4)δ^-2 log n; no bound on p | new proof, Section 5.1 (shorter than the original) |
| Lemma 2.1 (gap gives cut-density) | same | verbatim, any graph; applied only to balanced bipartite G[X, Y] |
| Thm 3.2 (Haxell) | same | verbatim |
| Lemma 3.1 (connecting lemma) | same, reservoir graph J = G[U ∪ V] = G[U, V] | verbatim, any graph; no parity constraint on path lengths is needed anywhere |
| Def 4.1, Prop 4.2 (router, closing the cycle) | same | verbatim; G viewed as a digraph with both orientations |
| (implicit) subdividing connections, attaching A to comparator inputs | **Lemmas R0, R1** | Section 5.2, short proofs |
| (none) | **Lemma R2** (parity: A ⊆ P, B ⊆ Q forces a balanced router) | new, Section 5.3 |
| Def 4.3, Prop 4.4 (basic router, from [4]) | same | verbatim; independent proof in Section 4 and a check for orders 2..9 |
| Lemma 4.5 (comparator from an even cycle) | same | verbatim (typo in M0 fixed); short proof in Section 4; check for g <= 600 |
| Lemma 4.6 (short even cycles) | applied to the bipartite graph G[C_P, C_Q] | verbatim (its max-cut step is trivial there) |
| Lemma 4.7 (router in a random reservoir) | **Lemma B4.7**: R = R_P ∪ R_Q, C = C_P ∪ C_Q, U ⊆ P, V ⊆ Q; δ^2 in place of δ^3; q <= δ/100 dropped | new proof, Section 5.4 |
| Lemma 5.1 (Hall after perturbation) | same | verbatim, already a bipartite statement; used with auxiliary graphs that contain super-vertices |
| Divisibility remark | **Lemma Ch** (cherries) + super-vertices | new, Sections 5.5 and 6 |
| Main proof (Section 6) | sides partitioned independently; odd layers in P, even layers in Q; 2τ layers | new write-up, Section 6 |
| Cor 1.4 (via Cheeger) | Theorem BM-γ via BJ Lemma 3.3 | Section 7 |

Places where non-bipartiteness could have entered, and what happens:
- Random sets. Müyesser samples disjoint sets from all of V(G). Here every set lives in one side
  and the two sides are partitioned independently; consecutive layers are on opposite sides.
- Spectral input. In Müyesser's proof the spectrum of G enters only through Lemma 2.2, via
  ||A - (d/n)J|| <= (1-δ)d, which bounds both λ2 and |λn|; that is what fails for bipartite G
  (λn = -d). In the bipartite proof it enters only through Lemma B2.2, via
  ||W - (d/N)J|| = s2(W) = λ2(G), so λn is never used. (Lemma 2.1 is applied to sampled
  bipartite graphs, whose λ2 Lemma B2.2 controls.)
- Path parities. In a bipartite host the parity of every connecting path is forced by its ends.
  The router property is invariant under arbitrary subdivision of connection paths (R0, R1,
  Lemma 4.5), so parities never matter inside the router. They matter only for counting, and
  Lemma R2 shows the count comes out balanced.
- Divisibility. The leftover must split into 2τ layers of size k, τ on each side. Lemma R2 gives
  |P \ V(S)| = |Q \ V(S)| =: M; the remainder M mod k is removed with cherries (Lemma Ch).

## 4. Ingredients used verbatim

These are statements about arbitrary graphs or matrices, or already bipartite statements. Each
was re-read in the PDF; where I re-derived a proof I say so.

**Lemma 2.1** (Müyesser, from Brouwer-Haemers). Let G have n0 >= 2 vertices. If δ(G) > λ2(G),
then e_G(S, V \ S) >= ((δ(G) - λ2(G))/n0)|S||V \ S| for every S ⊆ V(G) ("p-cut-dense" with
p = (δ(G) - λ2(G))/n0). Holds for every graph: the Laplacian L = D_G - A_G satisfies
L ⪰ δ(G)I - A_G, so its second smallest eigenvalue is at least δ(G) - λ2(G) (Weyl), and the test
vector |V \ S|1_S - |S|1_(V \ S) gives the cut bound. Used only for balanced bipartite graphs
H0 = G[X, Y], |X| = |Y| = m, where n0 = 2m and λ2(H0) = s2 of the biadjacency matrix.

**Theorem 2.3** (matrix Bernstein, Tropp 2012, Theorem 1.4) and **Lemma 2.4**: for F in R^(r x s)
with columns f_j and c = max_j ||f_j||_2, and I a uniformly random k-subset of [s], q = k/s:
P(||F_I|| > sqrt(q)||F|| + c sqrt(t)) <= r(s+1)e^-t. Pure matrix statements.

**Lemma 3.1** (connecting lemma), as stated: there is an absolute constant C_L such that if G[R] is
p-cut-dense, ∆ := ∆(G[R]), p|R| >= γ∆ (0 < γ <= 1), the pairs (a_i, b_i) lie in V(G) \ R, every
vertex occurs at most 10 times among the a_i, b_i, d_G(x, R) >= β∆ for x in T := {a_i, b_i},
and d_G(v, T) <= βγ^2∆/(C_L log(2|R|)) for v in R, then there are a_i-b_i paths with pairwise
disjoint interiors inside R. The proof (Haxell's theorem on the hypergraph of short a_i-b_i paths;
a maximal set W with small boundary; vertex expansion and ball growth in K = G[R] - (U ∪ W)) uses
only cut-density, ∆ and the degree conditions. I re-checked the arithmetic of its Claim 1
(|I| <= 5γ^2|R|/(C_L log 2|R|); |U| <= γ|R|/100 once C_L >= 1000 C0; |W| < 16|U|/(3γ) <= 6|U|/γ;
|W ∪ S| <= 0.53|R| < 3|R|/4; final contradiction 140C0/C_L < 1). The paths have bounded length
and no prescribed parity. With a bipartite reservoir graph G[R] = J the proof runs unchanged.

**Definition 4.1** (Hamilton router), quoted: "We call S an A, B-Hamilton-router if, for every
bijection ϕ : A → B, V(S) can be partitioned into a collection of paths, Pϕ, with endpoints in
A × B so that, letting Mϕ be the matching {(ϕ(a), a) : a ∈ A} ⊆ B × A, the edge-set E(Pϕ) ∪ Mϕ
forms a Hamilton cycle over V(S)." In that cycle every terminal has exactly one edge of P_φ, so
P_φ consists of exactly k = |A| paths, each joining A to B. A comparator is a router of order 2;
it realizes both bijections between its inputs and its outputs as path systems.

**Proposition 4.2**, quoted: "Let D be a directed graph containing an A, B-Hamilton-router S.
Suppose that there exists a directed path forest P with exactly |A| = |B| paths, start-vertices in
B, end-vertices in A, and internal vertices partitioning V(D) \ V(S). Then, D has a directed
Hamilton cycle." (Let φ(a) be the start of the forest path ending at a, and replace each edge
(φ(a), a) of E(P_φ) ∪ M_φ by that path.) Applied to G with both orientations of every edge.

**Definition 4.3 and Proposition 4.4** (basic router, from [4] = Bowtell-Montgomery-Müyesser-
Pokrovskiy, arXiv:2608.06369, not fetched). Vertices v_(i,j), (i, j) in [4] x [k]; A = row 1,
B = row 4; for odd i in [k-1] a comparator from {v_(1,i), v_(1,i+1)} to {v_(2,i), v_(2,i+1)};
for even i in [k-1] a comparator from {v_(3,i), v_(3,i+1)} to {v_(4,i), v_(4,i+1)}; a path
v_(2,j) to v_(3,j) for every j; the edge v_(3,1)v_(4,1); and v_(3,k)v_(4,k) if k is even,
v_(1,k)v_(2,k) if k is odd.
*Independent proof of Proposition 4.4.* Identify A and B with [k] by column. A choice of states
(straight or crossed) for all comparators, with every connection path used in full, is a path
system realizing σ = τ_e ∘ τ_o, where τ_o is a product of some of the transpositions (i i+1), i
odd, and τ_e of some of those with i even. For a bijection φ, the cycle E(P_φ) ∪ M_φ runs
a, σ(a), φ^-1(σ(a)), ..., so it is one Hamilton cycle iff π := φ^-1 ∘ σ is a k-cycle. Start with
π = φ^-1. For i = 2, 4, ..., multiply π on the right by (i i+1) iff i and i+1 lie in different
cycles of the current π; then do the same for i = 1, 3, .... Right multiplication by a
transposition whose two points lie in different cycles merges those two cycles, so cycles only
merge. After the even phase, i and i+1 share a cycle for every even i, and this survives the odd
phase; after the odd phase the same holds for odd i. So all of [k] lies in one cycle. The chosen
transpositions within a phase are disjoint, so π = φ^-1 τ_e τ_o with τ_e, τ_o of the required
form. ∎ (Checked by computer for k = 2..9; checks/combinatorics.py.)

**Lemma 4.5** (comparator from an even cycle). For every even g >= 4 there is a comparator of
maximum degree 3 obtained from a g-cycle C = c0 c1 ... c_(g-1) by taking inputs A = {c0, c2},
outputs B = {c1, c4} (for g = 4: B = {c1, c3}, and C itself is the comparator), pairing the other
cycle vertices by P = {c_(2j+1)c_(2j+4) : 1 <= j <= g/2 - 3} ∪ {c_(g-3)c_(g-1)}, and joining each
pair by a path of any length >= 1 (internally disjoint, meeting C only at its ends).
*Proof* (with M0 = {c0c1, c2c3, ..., c_(g-2)c_(g-1)} and M1 = {c1c2, c3c4, ..., c_(g-1)c0}; the
paper's "matching c0 to c2" is a typo). In M_i ∪ P the four terminals have degree 1 and all other
cycle vertices degree 2. In M0 ∪ P the edge c0c1 is a component. From c2 the walk c2, c3, c6, c7,
c10, ... alternates an M0 edge (+1) and a pairing edge c_(2j+1)c_(2j+4) (+3); from c4 the walk
c4, c5, c8, c9, ... does the same. The two walks use the residues {2, 3} and {0, 1} mod 4, so they
are disjoint, and they climb until they reach c_(g-3) and c_(g-1), one each, which the last pair
joins. So M0 ∪ P is the edge c0c1 plus one path from c2 to c4 through everything else. In
M1 ∪ P the edge c1c2 is a component, and the walk c4, c3, c6, c5, c8, ..., c_(g-2), c_(g-3),
c_(g-1), c0 alternates M1 edges and pairing edges and covers everything else. Subdividing pairing
edges changes nothing. So the path systems {c0-c1, c2-c4} and {c2-c1, c0-c4} both partition the
vertex set: this is the comparator property. ∎ (Checked by computer for every even g in [6, 600].)
In a bipartite host the cycle is even, c0, c2, c4 lie on one side and c1 on the other, so a
comparator's own terminals are not side-respecting. This does not matter: comparators are
internal, and only the router's outer terminals A, B must be side-respecting (Lemma R2).

**Lemma 4.6** (packing short even cycles), quoted: "Let G be an n-vertex graph with D ≤ δ(G) and
∆(G) ≤ 2D for some D ≥ 100. Then, G contains at least n/(100 log n) vertex-disjoint even-length
cycles each of length at most 3 log n." The proof takes a max-cut bipartite subgraph and iterates
the Moore bound for irregular graphs (Alon-Hoory-Linial). For a bipartite G the max-cut subgraph
is G itself.

**Lemma 5.1** (Hall after perturbation), quoted: "Let H0 be a balanced bipartite graph with
bipartition (L0, R0), where |L0| = |R0| = m. Suppose that H0 is p-cut-dense and dH0(v) = (1 ± η)D
for every v ∈ V(H0). Set α := pm/D, and suppose that 0 < α ≤ 1/2 and η ≤ α/10. Let X, Y be
disjoint sets with |X| = |Y|, and let H be a bipartite graph with bipartition (L0 ∪ X, R0 ∪ Y)
containing H0. Suppose that every x ∈ X has at least D/2 neighbors in R0, every y ∈ Y has at
least D/2 neighbors in L0, and dH(v, X) ≤ αD/20 for every v ∈ R0, dH(v, Y) ≤ αD/20 for every
v ∈ L0. Then H contains a perfect matching." Already bipartite. I re-derived the proof: if
e_H0(S, T) = 0 with |S| = s <= |T|, then Z = S ∪ (R0 \ T) has |Z| <= m and
αD(2s + h) <= e(Z, V(H0) \ Z) <= D(2ηs + (1+η)h), so h >= 2(α - η)s/(1 + η - α) >= αs; König's
theorem and the degree conditions then give h < (α/10)(h + u) <= (α + 1)h/10 <= 3h/20 with h >= 0,
a contradiction. Lemma 5.1 is about abstract bipartite graphs, so Section 6 may apply it to
auxiliary graphs containing super-vertices.

## 5. New and modified lemmas, with proofs

### 5.1 Lemma B2.2 (bipartite subsampling)

> **Lemma B2.2.** Let a > 0 and C'_a := 32(a + 4). Let G be bipartite and d-regular with parts
> P, Q, |P| = |Q| = N, n = 2N >= 3, biadjacency W, and λ2(G) = s2(W) <= (1-δ)d, δ in (0,1). Let
> 1 <= m <= N, p := m/N, D := pd, and assume D >= C'_a δ^-2 log n. Let U ⊆ P and V ⊆ Q be
> independent uniformly random m-subsets. Then with probability at least 1 - n^-a,
> λ2(G[U, V]) = s2(W[U, V]) <= (1 - δ/2)D.

*Proof.* Let t := (a+4) log n and B := W - (d/N)J, J the all-ones P x Q matrix.
1. ||B|| = s2(W). Since W1 = d1 and 1^T W = d1^T, we get B1 = 0, 1^T B = 0 and
   W^T W = (d^2/N)11^T + B^T B. So the singular values of W are d (vectors 1/sqrt N) together with
   those of B on 1^⊥. As ||W|| <= d (row and column sums d), s2(W) = ||B|| <= (1-δ)d.
2. Every row and column of B has squared norm d(1 - d/N)^2 + (N - d)(d/N)^2 = d - d^2/N <= d.
3. Rows. Lemma 2.4 with F = B^T (its columns are the rows of B, of norm <= sqrt d), I = U, q = p:
   ||B[U, Q]|| <= sqrt(p)||B|| + sqrt(dt), except with probability <= N(N+1)e^-t.
4. Column norms. For j in Q, ||B[U, {j}]||^2 = d_G(j, U)(1 - 2d/N) + m(d/N)^2 <= d_G(j, U) + D.
   d_G(j, U) is hypergeometric with mean D, so P(d_G(j, U) >= 2D) <= e^(-D/3). With probability
   >= 1 - Ne^(-D/3), every column of B[U, Q] has norm <= sqrt(3D).
5. Columns. Condition on a U satisfying 3 and 4. V is independent of U and uniform in Q, so
   Lemma 2.4 with F = B[U, Q], I = V, q = p and c <= sqrt(3D) gives
   ||B[U, V]|| <= sqrt(p)||B[U, Q]|| + sqrt(3Dt), except with probability <= m(N+1)e^-t.
6. Hence ||B[U, V]|| <= p||B|| + sqrt(pdt) + sqrt(3Dt) <= (1-δ)D + (1 + sqrt 3)sqrt(Dt). Since
   W[U, V] = (d/N)J_m + B[U, V] and s2(M) <= ||M - R|| whenever rank R <= 1, we get
   s2(W[U, V]) <= ||B[U, V]||. From D >= 32δ^-2 t: (1 + sqrt 3)sqrt(Dt) <= 2.74δD/sqrt(32)
   < δD/2. So s2(W[U, V]) <= (1 - δ/2)D.
7. Failure probability: N(N+1)e^-t + Ne^(-D/3) + m(N+1)e^-t <= (2N^2 + 3N)n^-(a+4) <= n^-a,
   using D/3 >= t. ∎

Differences from Müyesser's Lemma 2.2: V is independent of U and uniform on all of Q, so the
second sampling has proportion p rather than p/(1-p), and his hypothesis p <= δ/100 (used only to
bound (1-p)^(-1/2)) is not needed. A small numerical run (checks/sampling.py; two-block bipartite
graphs on 600 vertices) shows s2(W[U, V])/D approaching 1 - δ from above as D grows, as expected.

### 5.2 Lemmas R0 and R1 (subdividing connections, extending terminals)

> **Lemma R0.** Let S be an A,B-Hamilton router and e = uv an edge of S such that for every φ the
> path system P_φ can be chosen to contain e. Replacing e by a u-v path with new internal vertices
> gives an A,B-Hamilton router.

*Proof.* Replace e by that path inside the path of P_φ containing e. ∎ In Definition 4.3, the
path systems in the proof of Proposition 4.4 use every connection path in full; in Lemma 4.5 both
path systems contain every pairing path. So all connections may have arbitrary lengths.

> **Lemma R1.** Let S be an A,B-Hamilton router, a in A, and Π a path from a new vertex a' to a
> with V(Π) ∩ V(S) = {a}. Then S ∪ Π is an (A - a + a'),B-Hamilton router. The same holds on the
> B side.

*Proof.* Given φ' for the new terminal sets, let φ(a) := φ'(a') and φ = φ' elsewhere. In the cycle
E(P_φ) ∪ M_φ the vertex a has one M_φ-edge, hence exactly one P_φ-edge: a is the A-end of one
path of P_φ. Prepend Π to it. The new system covers V(S) ∪ V(Π), and with M_φ' (the edge
(φ(a), a) replaced by (φ(a), a')) it forms a Hamilton cycle. ∎ This is how the router's actual
terminals (layers A, B outside the reservoir) attach to comparators whose terminals lie on cycles
inside the reservoir. Müyesser does this implicitly ("include one pair for every fixed connection
joining the inputs/outputs of the comparators").

### 5.3 Lemma R2 (parity of a side-respecting router)

> **Lemma R2.** Let H be bipartite with parts P, Q, and let S ⊆ H be an A,B-Hamilton router with
> A ⊆ P and B ⊆ Q. Then |V(S) ∩ P| = |V(S) ∩ Q|.

*Proof.* Fix any φ. Every edge of the Hamilton cycle E(P_φ) ∪ M_φ on V(S) joins P and Q: the
edges of P_φ are edges of H, and each (φ(a), a) joins B ⊆ Q to A ⊆ P. Around a cycle whose edges
all join P and Q the sides alternate, so it has equally many vertices in P and in Q. ∎

The hypothesis is sharp: with A and B on the same side, each path of P_φ has one more vertex on
that side, and the imbalance is exactly |A|. The computer check (checks/controls.py) shows
imbalance exactly k in 10 of 10 such embeddings, and balance in 40 of 40 side-respecting ones.

### 5.4 Lemma B4.7 (routers in a bipartite random reservoir)

> **Lemma B4.7.** There are absolute constants c_R in (0,1), K_R >= 1 and n_R such that the
> following holds. Let H be bipartite and d-regular with parts P, Q of size N, n = 2N >= n_R, and
> λ2(H) <= (1-δ)d, 0 < δ <= 1/2. Let 0 < q <= 1/2 with qN an integer, and suppose
> qd >= K_R δ^-2 (log n)^2. Let R_P ⊆ P and R_Q ⊆ Q be independent uniformly random qN-subsets and
> R := R_P ∪ R_Q (so |R| = qn). Then with probability at least 1 - 1/n the following holds for
> every k >= 2 and all disjoint A, B ⊆ V(H) \ R with |A| = |B| = k: if every x in A ∪ B has
> d_H(x, R) >= qd/2, every v in R has d_H(v, A ∪ B) <= c_R δ^2 qd/log n, and
> k <= c_R δ^2 |R|/(log n)^2, then H[A ∪ B ∪ R] contains an A,B-Hamilton router S with
> A ∪ B ⊆ V(S) ⊆ A ∪ B ∪ R.

Compared with Müyesser's Lemma 4.7: R is chosen side by side; his q <= δ/100 is dropped (it fed
only his Lemma 2.2); δ^3 becomes δ^2 in both hypotheses on k and on d_H(v, A ∪ B), and δ^-4
becomes δ^-2 in the degree hypothesis. The proof shows where each power is used.

*Proof.* Let C_L be the constant of Lemma 3.1. Fix σ := 1/(300 C_L), c_R := σ/400 and
K_R := 4·10^5/σ. Write L := log n.

*Random structure.* Let s' := floor(σδ^2 qN/L) and m0 := qN - s'. Split R_P uniformly at random
into C_P (size s') and U (size m0), and R_Q into C_Q (size s') and V (size m0); put C := C_P ∪ C_Q.
Then U and V are independent uniform m0-subsets of P and Q. Put D0 := m0 d/N and D_C := s'd/N.
Since qN >= qd >= K_R δ^-2 L^2, we have σδ^2 qN/L >= 2, so s' >= σδ^2 qN/(2L) and s' <= qN/100.
Hence D0 lies in [0.99qd, qd] and D_C in [σδ^2 qd/(2L), σδ^2 qd/L]; in particular
D0 >= 0.99 K_R δ^-2 L^2 and D_C >= (σK_R/2)L = 2·10^5 L.
With probability at least 1 - 5n^-2 over (R, split):
- (E1) λ2(H[U, V]) <= (1 - δ/2)D0 (Lemma B2.2 with a = 2, which needs D0 >= 192δ^-2 L);
- (E2) d_H(v, V) = (1 ± δ/100)D0 for all v in P, and d_H(v, U) = (1 ± δ/100)D0 for all v in Q
  (hypergeometric Chernoff P(|X - μ| >= εμ) <= 2exp(-ε^2 μ/3) with ε = δ/100; needs
  D0 >= 9·10^4 δ^-2 L);
- (E3) d_H(v, C) = (1 ± 1/10)D_C for every v (needs D_C >= 900L).
Let g(R) be the conditional probability, over the split, that E1-E3 hold. Then
P(g(R) = 0) <= E[1 - g(R)] <= 5n^-2 <= 1/n. Fix R with g(R) > 0 and a split satisfying E1-E3.
Everything below is deterministic and holds for all admissible k, A, B at once.

*The reservoir graph.* J := H[U ∪ V] = H[U, V] (no edges inside U or V). By E1 and E2,
δ(J) >= (1 - δ/100)D0, ∆(J) <= (1 + δ/100)D0 and λ2(J) <= (1 - δ/2)D0. Lemma 2.1 makes J
ρ-cut-dense with ρ := (δ(J) - λ2(J))/(2m0) >= 0.49δD0/(2m0), so ρ|V(J)| >= 0.49δD0 >= (δ/3)∆(J).
So Lemma 3.1 applies to G' := H[A ∪ B ∪ C ∪ U ∪ V] with reservoir U ∪ V (G'[U ∪ V] = J),
γ := δ/3 and ∆ := ∆(J), once its degree conditions are checked.

*Cycles.* H[C] = H[C_P, C_Q] has minimum degree >= 0.9D_C >= 100 and maximum degree
<= 1.1D_C <= 2(0.9D_C) by E3. Lemma 4.6 (with D := 0.9D_C, on 2s' vertices) gives at least
2s'/(100 log(2s')) >= σδ^2 qN/(100L^2) = σδ^2|R|/(200L^2) vertex-disjoint cycles, all even, each
of length at most 3 log(2s') <= 3L. This is at least k, since k <= c_R δ^2|R|/L^2 and
c_R <= σ/200. (This is the first place δ^2 is used: the number of cycles is proportional to
|C| / log n, and |C| is proportional to δ^2.)

*Template and pairs.* Take the basic router of order k (Definition 4.3); it has k - 1
comparators. Give each its own cycle and apply Lemma 4.5 to it: two cycle vertices become inputs,
two become outputs, the rest are paired. Let 𝒟 be the list of pairs:
- every pairing pair of every comparator;
- for each odd comparator (columns i, i+1): (v_(1,i), first input) and (v_(1,i+1), second input),
  where v_(1,j) is the j-th vertex of A in a fixed order;
- for each even comparator (columns i, i+1): (first output, v_(4,i)) and (second output, v_(4,i+1)),
  where v_(4,j) is the j-th vertex of B;
- for each column j, one pair joining its row-2 point (the output of the odd comparator covering
  column j, or v_(1,k) itself when j = k is odd) to its row-3 point (the input of the even
  comparator covering column j, or v_(4,j) itself when j = 1, or when j = k is even). A template
  edge v_(1,k)v_(2,k), v_(3,1)v_(4,1) or v_(3,k)v_(4,k) next to a column path merges with it
  into one connection.
Every vertex of A ∪ B and of every used cycle is an end of exactly one pair, and no end lies in
U ∪ V. Let T ⊆ A ∪ B ∪ C be the set of ends.

*Degree conditions of Lemma 3.1, with β := 1/4.*
- x in A ∪ B: d(x, U ∪ V) = d(x, R) - d(x, C) >= qd/2 - 1.1D_C >= qd/3 >= ∆(J)/4, since
  ∆(J) <= 1.01D0 <= 1.01qd.
- x in C ∩ P: d(x, U ∪ V) = d(x, V) >= 0.99D0 >= 0.98qd >= ∆(J)/4; the same for C ∩ Q.
- v in U ∪ V: d(v, T) <= d(v, C) + d(v, A ∪ B) <= 1.1σδ^2 qd/L + c_R δ^2 qd/L <= 1.2σδ^2 qd/L.
  The required bound is βγ^2∆/(C_L log(2|U ∪ V|)) >= (1/4)(δ^2/9)(0.98qd)/(2C_L L)
  >= δ^2 qd/(74 C_L L), and 1.2σ = 1/(250 C_L) is smaller. (This is the second place δ^2 is
  used: γ^2 = δ^2/9 in Lemma 3.1. A bound cδ^2 qd/L on d(v, A ∪ B) suffices; δ^3 is not needed.)
- Each vertex occurs in at most one pair (Lemma 3.1 allows 10).
Lemma 3.1 gives paths joining all pairs of 𝒟 with pairwise disjoint interiors inside U ∪ V.
Interiors avoid C, A and B, and different pairs have different ends, so the cycles and paths
together form a subgraph S of H[A ∪ B ∪ R].

*S is a router.* Each cycle with its pairing paths is a comparator (Lemma 4.5, any lengths). Its
inputs and outputs are joined to their template positions by connection paths. By R1 at the A and
B ends and R0 for every other connection, S is a basic router (Definition 4.3) with subdivided
connections, so Proposition 4.4 makes it an A,B-Hamilton router. Finally
A ∪ B ⊆ V(S) ⊆ A ∪ B ∪ C ∪ U ∪ V = A ∪ B ∪ R. ∎

### 5.5 Lemma Ch (disjoint cherries)

> **Lemma Ch.** Let H be a graph of maximum degree at most d, F_P and F_Q disjoint vertex sets,
> r >= 0 an integer. Suppose every vertex of F_Q has at least θ >= 2 neighbors in F_P and
> (θ - 1)|F_Q| >= 3rd. Then H contains r vertex-disjoint paths x_j y_j x'_j (1 <= j <= r) with
> y_j in F_Q and x_j, x'_j in F_P.

*Proof.* Greedy. Suppose j < r such paths have been chosen, with vertex set U_j
(2j vertices in F_P, j in F_Q). The number of edges between F_Q \ U_j and F_P \ U_j is at least
θ|F_Q \ U_j| - 2jd. Since j(θ - 1 + 2d) < 3rd <= (θ - 1)|F_Q|, we get
(θ - 1)|F_Q \ U_j| >= (θ - 1)(|F_Q| - j) > 2jd, so that number exceeds |F_Q \ U_j|. Some
y in F_Q \ U_j therefore has two neighbors x, x' in F_P \ U_j; add the path x y x'. ∎

In Section 6 each cherry x_j y_j x'_j (x_j, x'_j in P, y_j in Q) is contracted to a super-vertex
w_j that is entered at x_j and left at x'_j. A super-vertex behaves like a P-vertex in the
alternating layer structure (both neighbors on its path are in Q), and contracting a cherry
removes one vertex from each side. That is the bipartite form of Müyesser's "contracting the
vertices of the short path". In a non-bipartite host one contracts edges instead.

## 6. Proof of Theorem BM

### 6.0 Reductions and constants

*δ <= 1/2.* Prove the theorem for δ <= 1/2 with a constant C'. If δ > 1/2 then λ2 <= d/2, and
d >= 2^5 C' δ^-5 L^3 >= C'(1/2)^-5 L^3 since δ^-5 >= 1, so the case δ' = 1/2 applies. Hence
C_BM := 2^5 C' works for all δ in (0,1). From now on 0 < δ <= 1/2.

*n is large.* d <= N = n/2 and d >= C' L^3 force n >= 2C' (log n)^3, so n exceeds any fixed
threshold once C' is large. All "n large" statements below are of this kind.

*Constants.* Let c_R, K_R, n_R be as in Lemma B4.7. Put c0 := 10^-5, c1 := min(c_R/4, 10^-8),
C_D := 10^7, and C' := max(8C_D/(c0 c1), 4K_R/c0). Assume d >= C' δ^-5 L^3, L := log n.

*Parameters.* Let G have parts P, Q, |P| = |Q| = N, n = 2N.
- q := floor(c0 δ N)/N, so qN is an integer and c0δ/2 <= q <= c0δ.
- k := floor(c1 δ^2 q n/L^2), h := ceil(2qk), m := k - h, D := md/N.
- η := δ/100, α := δ/10, T' := floor((N - qN - k)/m).

*Size facts (n large).* k >= c1δ^2 qn/(2L^2), qk >= 2, so h <= 3qk and
k/2 <= m <= (1 - 2q)k. Then
- D >= kd/(2N) >= c1δ^2 qd/(2L^2) >= c0c1δ^3 d/(4L^2) >= (c0c1C'/4)δ^-2 L >= 2C_D δ^-2 L;
- D <= kd/N <= 2c1δ^2 qd/L^2, so D <= 2·10^-8 qd;
- kd/N <= 2D;
- qD >= (c0δ/2)(2C_D δ^-2 L) >= 100L;
- qd >= (c0/2)C'δ^-4 L^3 >= K_R δ^-2 L^2.

(This is where the exponent comes from: D is proportional to k d/n, k to δ^2 q n/L^2 by
Lemma B4.7, q to δ by Lemma 5.1's perturbation slack, and Lemma B2.2 needs D >= C δ^-2 L. So
d >= C δ^-(2+2+1) L^3 = C δ^-5 L^3. Müyesser's δ^3 in Lemma 4.7 gives δ^-6.)

### 6.1 The random partition

Independently for the two sides, choose uniformly at random partitions
- P = R_P ⊔ A0 ⊔ A1 ⊔ C1 ⊔ C3 ⊔ ... ⊔ C_(2T'-1) ⊔ Z_P,
- Q = R_Q ⊔ B0 ⊔ B1 ⊔ C2 ⊔ C4 ⊔ ... ⊔ C_(2T') ⊔ Z_Q,

with |R_P| = |R_Q| = qN, |A0| = |B0| = |C_i| = m, |A1| = |B1| = h and
|Z_P| = |Z_Q| = N - qN - k - T'm in [0, m). Put A := A0 ∪ A1 ⊆ P, B := B0 ∪ B1 ⊆ Q (both of size
k) and R := R_P ∪ R_Q (|R| = qn). Layers with odd index lie in P, with even index in Q.

### 6.2 Part 1: properties that hold with positive probability

- **(P1) Spectral gaps.** For every pair (X, Y) in
  𝓛 := {(C_i, C_(i+1)) : 1 <= i < 2T'} ∪ {(B0, C1)} ∪ {(C_i, A0) : i even},
  λ2(G[X, Y]) <= (1 - δ/2)D. In each pair one set is a uniform m-subset of P and the other an
  independent uniform m-subset of Q, so Lemma B2.2 with a = 3 applies (it needs D >= 224δ^-2 L).
  Union bound over |𝓛| <= 3n pairs: failure <= 3n^-2.
- **(P2) Degrees.** For every vertex v, with every set below taken on the side opposite to v:
  (a) d(v, X) = (1 ± η)D for X in {A0, B0, C1, ..., C_(2T')};
  (b) d(v, R_P), resp. d(v, R_Q), is (1 ± 1/10)qd;
  (c) d(v, Z_P), d(v, Z_Q) <= 2D;
  (d) d(v, A1), d(v, B1) <= 12qD.
  These are hypergeometric tails: (a) 2exp(-η^2 D/3) <= 2n^-4, as η^2 D/3 >= C_D L/(1.5·10^4);
  (b) 2exp(-qd/300) <= n^-4; (c) the mean is below D, so P(>= 2D) <= e^(-D/3); (d) the mean is
  hd/N <= 3qkd/N <= 6qD, so P(>= 12qD) <= e^(-2qD) <= n^-200. Union over at most n vertices and
  n sets: failure <= n^-2.
- **(P3) Router property.** Lemma B4.7 applies (qd >= K_R δ^-2 L^2, q <= 1/2, qN an integer,
  n >= n_R), so with probability >= 1 - 1/n the set R has its router property.

The failure probabilities sum to less than 1. Fix a partition with (P1)-(P3).

### 6.3 Part 2: building the Hamilton cycle

**Step 1 (router).** For x in A, d(x, R) = d(x, R_Q) >= 0.9qd >= qd/2; likewise for B. For v in
R, d(v, A ∪ B) is d(v, A0) + d(v, A1) or d(v, B0) + d(v, B1), at most (1 + η)D + 12qD <= 2D
<= 4c1δ^2 qd/L^2 <= c_R δ^2 qd/L. And k <= c1δ^2 qn/L^2 <= c_R δ^2 |R|/L^2. By (P3) there is an
A,B-Hamilton router S with A ∪ B ⊆ V(S) ⊆ A ∪ B ∪ R.

**Step 2 (parity).** A ⊆ P and B ⊆ Q, so Lemma R2 gives |V(S) ∩ P| = |V(S) ∩ Q|. Let
M := |P \ V(S)| = |Q \ V(S)|. Since A ⊆ V(S) ∩ P ⊆ R_P ∪ A, we have N - qN - k <= M <= N - k.

**Step 3 (number of layers).** Let τ := floor(M/k) and r := M - τk, so 0 <= r < k. The layers
C1, ..., C_(2τ) will be used; C_(2τ+1), ..., C_(2T') are spare. Let F_P (resp. F_Q) be the union
of the spare layers in P (resp. Q); each is a union of T' - τ layers. Bounds:
- τ >= M/k - 1 >= (N - qN - k)/k - 1 >= N/(2k);
- T' - τ >= (N - qN - k)/m - 1 - (N - k)/k >= [(N - qN - k) - (1-2q)(N - k)]/((1-2q)k) - 1
  = (qN - 2qk)/((1-2q)k) - 1 >= qN/k - 2q - 1 >= qN/(2k), using m <= (1-2q)k;
- T' - τ <= (N - qN - k)(1/m - 1/k) + 1 <= Nh/(mk) + 1 <= 6qN/k + 1 <= 7qN/k, using
  M >= N - qN - k, h <= 3qk and m >= k/2.
So |F_P| = |F_Q| = (T' - τ)m >= qN/4.

**Step 4 (cherries).** By (P2a), every y in F_Q has d(y, F_P) >= (T' - τ)(1 - η)D
>= (qN/(2k))(0.99)(kd/(2N)) >= qd/5 =: θ. Since r < k <= 2c1δ^2 qN/L^2,
(θ - 1)|F_Q| >= (qd/10)(qN/4) = q^2 Nd/40 >= 6c1δ^2 qNd/L^2 >= 3rd,
because q/40 >= c0δ/80 >= 6c1δ^2 (c1 <= c0/480). Lemma Ch gives r vertex-disjoint cherries
x_j y_j x'_j with y_j in F_Q and x_j, x'_j in F_P. They avoid V(S) and C1, ..., C_(2τ).

**Step 5 (items).** Let W_P be (P \ V(S)) \ (C1 ∪ C3 ∪ ... ∪ C_(2τ-1)) with each pair
{x_j, x'_j} replaced by one super-vertex w_j, and W_Q := (Q \ V(S)) \ (C2 ∪ ... ∪ C_(2τ) ∪
{y_1, ..., y_r}). The elements of W_P, W_Q, of the layers, and of A, B are called items. Then
|W_P| = (M - τm) - r = τ(k - m) = τh and |W_Q| = M - τm - r = τh. Each item z has an entry z^-
and an exit z^+: z^- = z^+ = z for an ordinary vertex, and w_j^- = x_j, w_j^+ = x'_j.

**Step 6 (redistribution).** Partition W_P uniformly at random into X1, X3, ..., X_(2τ-1) and
W_Q into X2, X4, ..., X_(2τ), all of size h, and put L_i := C_i ∪ X_i (so |L_i| = k, odd i in P,
even i in Q). *Claim:* with positive probability, for every i in [2τ] and every vertex v on the
side opposite to X_i,
  #{z in X_i : v ~ z^-} <= 72qD and #{z in X_i : v ~ z^+} <= 72qD.   (*)
*Proof.* Distinct items z with v ~ z^- (or with v ~ z^+) give distinct G-neighbors of v in the
pool Π := (V(G) \ V(S)) \ (C1 ∪ ... ∪ C_(2τ)) ⊆ R ∪ Z_P ∪ Z_Q ∪ F_P ∪ F_Q. By (P2) and Step 3,
d(v, Π) <= 1.1qd + 2D + (T' - τ)(1 + η)D <= 1.1qd + 2D + 7.1qd <= 9qd, using
(T' - τ)D <= (7qN/k)(md/N) <= 7qd. X_i is a uniform h-subset of the τh items on its side, so the
count is hypergeometric with mean at most 9qd/τ <= 18qdk/N <= 36qD, and
P(count >= 72qD) <= e^(-12qD) <= n^-1200. Union over at most n vertices, n parts and two signs. ∎
Fix such a partition. Note 72qD <= 72c0δD < δD/200 = αD/20, and by (P2d)
d(v, A1), d(v, B1) <= 12qD < αD/20.

**Step 7 (perfect matchings).** For each of the 2τ + 1 consecutive pairs
(B, L1), (L1, L2), ..., (L_(2τ-1), L_(2τ)), (L_(2τ), A), the two sets lie on opposite sides
(B in Q, L1 in P, ..., L_(2τ) in Q, A in P). Define an auxiliary bipartite graph H on them: an
item z of the first set is joined to an item z' of the second iff z^+ z'^- is an edge of G. Apply
Lemma 5.1 with
- (B, L1): H0 = G[B0, C1], X = B1, Y = X1;
- (L_i, L_(i+1)): H0 = G[C_i, C_(i+1)], X = X_i, Y = X_(i+1);
- (L_(2τ), A): H0 = G[C_(2τ), A0], X = X_(2τ), Y = A1.
Hypotheses. H0 is balanced with sides of size m, contained in H, with all degrees (1 ± η)D by
(P2a) and λ2(H0) <= (1 - δ/2)D by (P1) (the pair is in 𝓛). By Lemma 2.1, H0 is cut-dense with
parameter (δ/2 - η)D/(2m) >= αD/m; take p := αD/m, so Lemma 5.1's α equals pm/D = δ/10 <= 1/2
and η = δ/100 = α/10. Each item of X (resp. Y) has at least (1 - η)D >= D/2 neighbors in the
opposite base set, by (P2a) applied to its exit (resp. entry). Each base vertex has at most
αD/20 neighbors in the opposite perturbation set, by (*) and (P2d). So each H has a perfect
matching.

**Step 8 (path forest).** From each b in B follow the matchings: b, z1 in L1, z2 in L2, ...,
z_(2τ) in L_(2τ), a in A. Each matching is perfect, so the k sequences are disjoint and use every
item of every layer once. Replace each super-vertex w_j by the path x_j y_j x'_j. Consecutive
vertices are adjacent in G: an auxiliary edge zz' is the G-edge z^+ z'^-, and x_j y_j, y_j x'_j
are G-edges. The result is k vertex-disjoint paths, each from B to A with 2τ >= 2 internal items,
whose internal vertices are exactly (C1 ∪ ... ∪ C_(2τ)) ∪ Π = V(G) \ V(S): every pool vertex is
an ordinary item of some X_i or lies on a cherry.

**Step 9 (closing).** Proposition 4.2, applied to S and this forest oriented from B to A, gives a
Hamilton cycle of G. ∎

### 6.4 What the bipartite proof does differently, in one place

- Sides are partitioned independently, and every random set lies in one side (6.1).
- Lemma B2.2 replaces Lemma 2.2 (P1, and E1 inside Lemma B4.7).
- Layers alternate sides; there are 2τ of them, so every forest path has an even number of
  internal vertices, as a B-to-A path in a bipartite graph must (B in Q, A in P).
- Lemma R2 makes the leftover balanced (Step 2); without A ⊆ P, B ⊆ Q it would be off by k.
- The remainder r = M mod k is removed by r cherries (Steps 4-8). [Omitted from this copy.]

## 7. Edge-expansion form (Theorem BM-γ)

*Proof.* Let G be a bipartite d-regular γ-expander. BJ Lemma 3.3 with d' = 0 (for d-regular G,
N(G) = A/d) gives λ2(G) <= (1 - γ^2/32)d. Apply Theorem BM with δ := γ^2/32 in (0, 1): it needs
d >= C_BM (γ^2/32)^-5 (log n)^3 = 32^5 C_BM γ^-10 (log n)^3 = C_γ γ^-10 (log n)^3. ∎

So c' = 2c = 10. The standard Cheeger bound for d-regular graphs, d - λ2 >= h(G)^2/(2d) (Alon;
Hoory-Linial-Wigderson Theorem 2.4, not re-fetched), gives δ = γ^2/2 and the smaller constant
2^5 C_BM; the exponent is the same. If U3 below fails and c = 6, then c' = 12, matching the γ^-12
of Müyesser's Corollary 1.4.

## 8. Corollary BM-2: removing a Hamilton cycle, and the pair

*(a) Spectral.* Theorem BM gives a Hamilton cycle H1 (33C_BM >= C_BM). G' := G - E(H1) is
bipartite with the same parts and (d-2)-regular. The all-ones vector is the top eigenvector of
A(G) and of A(G'), so by Courant-Fischer λ2(G') = max over x ⊥ 1 of x^T A(G')x / x^T x. For x ⊥ 1,
x^T A(G)x <= λ2(G) x^T x and -x^T A(H1)x <= 2x^T x (the spectral radius of a cycle is 2), so
λ2(G') <= λ2(G) + 2 <= (1-δ)d + 2. Now (1-δ)d + 2 <= (1 - δ/2)(d - 2) iff d >= (8 - 2δ)/δ, which
holds since d >= 33C_BM δ^-5 >= 8/δ. So λ2(G') <= (1 - δ/2)(d - 2). Also
d - 2 >= 32C_BM δ^-5 (log n)^3 = C_BM (δ/2)^-5 (log n)^3, using C_BM δ^-5 (log n)^3 >= 2. Theorem
BM gives a Hamilton cycle H2 of G'. H1 and H2 are edge-disjoint and both have vertex set V(G).

*(b) Expansion.* Each vertex has two H1-edges, so e_G'(S, V \ S) >= γd|S| - 2|S| >=
(γ/2)(d - 2)|S| for 1 <= |S| <= 2n/3, provided γd >= 4 (the same step as the spectral lane's
Proposition A). From d >= 2^11 C_γ γ^-10 (log n)^3: γd >= 4, and
d - 2 >= 2^10 C_γ γ^-10 (log n)^3 = C_γ (γ/2)^-10 (log n)^3. So G' is a bipartite (d-2)-regular
(γ/2)-expander satisfying Theorem BM-γ, and H2 exists as before. ∎

*For Erdős 585.* Every bipartite r-regular n-vertex graph with λ2 <= (1-δ)r and
r >= 33C_BM δ^-5 (log n)^3, and every bipartite r-regular γ-expander with
r >= 2^11 C_γ γ^-10 (log n)^3, contains a pair with support V. This is the spectral lane's
Proposition C with γ^-10 in place of γ^-12 and without assuming BM, subject to review of this
report. It does not change the spectral lane's floor (K >= 4 for "apply a (log n)^3 Hamiltonicity
theorem to a regular subgraph", their Corollary 5.2), since that floor depends only on the
(log n)^3 factor.

## 9. Computational checks (rung (b), sanity checks only)

Scripts and output are in `checks/` in this folder; run with `/usr/bin/python3 <script>` from that
folder (`sampling.py` needs `OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1`;
multithreaded BLAS stalled on this machine).
- `combinatorics.py`: Lemma 4.5's pairing (with the corrected M0) gives acyclic M0 ∪ P and M1 ∪ P
  with the required end pairs for every even g in [6, 600]. Proposition 4.4 in the permutation
  model: for k = 2..9 and every φ in S_k some state choice makes φ^-1 τ_e τ_o a k-cycle.
- `router_embed2.py` (output in `router_embed2.out`): 40 random basic routers of orders 2..5
  (24 to 128 vertices) built from Lemma 4.5 comparators on cycles of length 4..10, with every
  connection and pairing edge replaced by a path of random length >= 1, of the parity forced by a random
  2-coloring in which A is in side 0 and B in side 1, and with A, B attached to comparator inputs
  and outputs by paths (Lemma R1). For every bijection φ an exhaustive search finds a partition of
  V(S) into A-B paths closing into a Hamilton cycle with M_φ. Result: 40/40 proper 2-colorings,
  40/40 balanced, 40/40 routers.
- `controls.py`: with B moved to side 0, the imbalance is exactly k in 10/10 cases; deleting one
  degree-3 edge breaks the router property in 10/10 cases.
- `sampling.py`: two-block bipartite 60-regular graphs on 600 vertices with δ = 0.1, 0.27, 0.5;
  side-respecting samples with D = 12, 24, 48. The worst s2(W[U, V])/D over 4 samples moves toward
  1 - δ as D grows (for δ = 0.27: 0.834, 0.760, 0.741) and is below 1 - δ/2 except at the
  smallest D with δ = 0.1 (1.01 at D = 12), far outside the lemma's range D >= 32(a+4)δ^-2 log n.

## 10. Places where I am not certain

- **U1. Lemma 3.1** is used as stated. I re-checked its proof, but it rests on Haxell's theorem as
  quoted from Asadpour-Feige-Saberi (not re-fetched). Not bipartite-specific. Low risk.
- **U2. Proposition 4.4** is from [4] (not fetched). I give an independent proof (Section 4) and
  a check for k <= 9. Low risk.
- **U3. Exponent 5 instead of 6.** Müyesser's Lemma 4.7 assumes k <= cδ^3|R|/(log n)^2 and
  d_H(v, A ∪ B) <= cδ^3 qd/log n. In his proof the number of cycles is Θ(δ^2|R|/(log n)^2), and
  Lemma 3.1 needs d_H(v, T) <= βγ^2∆/(C log) with γ = Θ(δ), that is O(δ^2 qd/log n). I found no
  step that needs the third power of δ, so Lemma B4.7 is stated with δ^2, and then
  k = Θ(δ^2 q n/L^2) and d >= Cδ^-5 L^3. This deviates from the source. If a reviewer finds a
  step that needs δ^3, set k := c1δ^3 qn/L^2 and keep everything else; the proof then gives c = 6
  and c' = 12. Medium risk, but only for the exponent.
- **U4. The divisibility step** [Wording changed in this copy.] (Lemma Ch, super-vertices with distinct entry and exit, Lemma 5.1 on
  auxiliary graphs). New argument. I believe it is complete; the points to check are Step 5's
  counts, Step 6's pool-degree bound (super-vertices counted through entry and exit separately),
  and that Lemma 5.1 is applied to an abstract bipartite graph that contains H0. Medium risk.
- **U5. Lemma R2** and its use in Step 2. Two-line proof, computer check, sharpness check. Low risk.
- **U6. Lemma B2.2.** New short proof modeled on Müyesser's; the one real change is independent
  sampling of U and V. Low to medium risk.
- **U7. Probability bounds and absolute constants.** Hypergeometric tails are quoted in the
  standard Chernoff form (Hoeffding: hypergeometric is dominated by binomial in convex order).
  The constants c0, c1, C_D, C' were chosen to satisfy the listed inequalities but not optimized;
  a slip there would change C_BM, not the exponents. Low risk.
- **U8. Lemma 4.5's typo** (M0). Fixed reading confirmed by the next sentence of the paper, a
  direct proof and a computer check. Low risk.
- **U9. Lemma 4.6** relies on the Alon-Hoory-Linial Moore bound as quoted by Müyesser (not
  re-fetched). Low risk.
- **U10. Matrix Bernstein** as quoted (Tropp 2012, Theorem 1.4; not re-fetched). Low risk.
- **U11. Template wiring in Lemma B4.7.** Müyesser does not spell out how the layers A, B are wired
  to comparator terminals on cycles; I use terminal extension (R1) and subdivision (R0), and the
  column-by-column pairs listed in Section 5.4. The computer check covers this wiring for small
  orders. Low risk.
- **U12. Cheeger constant.** BJ Lemma 3.3 (verified text) gives γ^2/32; the sharper γ^2/2 is
  quoted from memory of Hoory-Linial-Wigderson and only affects constants.

## Log
- Read BRIEF.md and spectral/REPORT.md in full (BM audit table, Section 3.3).
- Fetched arXiv:2609.35766v1 and arXiv:2605.15043v1 with the lane user agent; pdftotext plain and
  -layout. Read Müyesser in full; read BJ Theorem 1.3, Corollary 1.4, Lemma 3.3, Definitions 1.2,
  3.1, 3.2 and the Cheeger remark.
- Confirmed c = max column norm in Lemma 2.4 from the plain text ("∥fj∥2").
- Ran checks/combinatorics.py (Lemma 4.5, Proposition 4.4), checks/router_embed2.py and
  checks/controls.py (bipartite router embeddings, controls), checks/sampling.py (numerics). The
  first run of router_embed.py hit the 240 s timeout without output; router_embed2.py adds
  pruning and smaller instances.
- Wrote Sections 0-11.

## 11. Summary for the lead

**What I tried.** Read Müyesser arXiv:2609.35766v1 in full and the Bradač-Janzer statements and
Section 3.1 (arXiv:2605.15043v1). Went through every lemma for a bipartite host. Wrote new proofs
for the three places that change (subsampling, the router lemma, the main assembly), added the
parity lemma and the subdivision and terminal-extension lemmas, wrote a complete divisibility
argument [Omitted from this copy.], and re-derived the proofs of Lemmas 3.1 and 5.1 and of Proposition 4.4.
Checked the purely combinatorial parts by computer.

**Results by rung.**
- (a) Theorem BM: bipartite d-regular, λ2 <= (1-δ)d, d >= C δ^-5 (log n)^3 implies Hamiltonian
  (c = 6 if U3 is rejected). Written proof, Sections 4-6.
- (a) Theorem BM-γ: bipartite d-regular γ-expander, d >= C γ^-10 (log n)^3 implies Hamiltonian
  (c' = 12 if U3 is rejected). Section 7.
- (a) Corollary BM-2: two edge-disjoint Hamilton cycles, so a pair on V, under
  d >= 33C δ^-5 (log n)^3 or d >= 2^11 C_γ γ^-10 (log n)^3. Section 8.
- (a) Side results: Lemma B2.2 (bipartite subsampling, no bound on p), Lemma R2 (parity of a
  side-respecting router), Lemma Ch and the super-vertex argument (a complete divisibility step [Omitted from this copy.]), a short proof of
  Proposition 4.4, and a proof of Lemma 4.5's pairing.
- (b) Computer checks of Lemma 4.5 (g <= 600), Proposition 4.4 (k <= 9), bipartite router
  embeddings (40 random instances plus negative controls), and small subsampling numerics.
- (c) Typos in the source: Lemma 4.5's M0, and "log log n" in the main proof.
- No obstruction found: the bipartite version follows from Müyesser's method.

**Single most promising next step.** Have an independent reviewer check Sections 5.4, 5.5 and
6.3 (Steps 2-8) against Müyesser's text, and rule on U3 (δ^2 versus δ^3 in Lemma 4.7). If it
passes, the spectral lane's bipartite Proposition C is unconditional, and the remaining gap for
any general exponent K is their ML-R or REL (regular expander extraction), not Hamiltonicity.

**Independent review needed: YES, heavy.** Theorem BM is an unpublished adaptation of a 13-page
proof with a new divisibility argument and a claimed exponent improvement (U3, U4).
