# Rigid cuts in sparse bipartite instances: spanning pairs fail, thin sets, a one-swap repair lemma

Pairs scout lane (Pass 3 wave 3), October 5, 2026. Status: frozen for review (SHA-256 in
`FROZEN.sha256`). Written proofs plus computer certificates. Not reviewed. No Lean, no `check.sh`.
Rungs: Lemmas 1, 2, 7 and Propositions 3, 5 are (a); Examples 4, 8 are (b) counterexamples; Corollary 6
is (a) given the census L5, which is (b). These are small results that steer the C1 step of
CONTINUE.md; none is a pair theorem.

## 0. Results

| Item | Statement | Kind |
|---|---|---|
| Lemma 1 | A smallest W1b counterexample is a sparse E4 or C1 instance with δ ≥ 4 | proof |
| Lemma 2 | A sparse E4 instance has a 4-factor | proof |
| Prop 3 | In a sparse E4 instance a balanced set with ≤ 1 edge leaving one colour class is a (5,1) set, and it is a cut of size ≤ 2 in every 4-factor | proof |
| Example 4 | A sparse E4 instance on 20 vertices with no two edge-disjoint Hamilton cycles (it has a pair) | certificate + proof |
| Prop 5, Cor 6 | In a smallest W1b counterexample every set with g = 10 has a 4-core of ≥ 18 vertices; an E4-type one with a (5,1) set has n ≥ 36 | proof + census L5 |
| Lemma 7 | One-swap repair of a 2-edge cut of a 4-factor, or deficiency concentration (≥ 3 of 4 units) | proof |
| Example 8 | The one-mark CP4 statement of W1-MINIMAL.md §4a is false on 11 vertices | certificate, two methods |

## 1. Setting

A *pair* is two edge-disjoint cycles with the same vertex set. W1b: every bipartite graph with
Δ ≤ 6, n ≥ 2 and e ≥ 3n − 4 has a pair. Bipartite graphs come with colour classes P, Q. For S ⊆ V:
g(S) = 6|S| − 2e(S); D(Z) = Σ_{v∈Z}(6 − deg v); D^S(Z) is the same inside G[S]; S_P = S ∩ P,
S_Q = S ∩ Q; ∂_Q(S) = e(S_Q, P − S) and ∂_P(S) = e(S_P, Q − S). From
`reports/585-next/G110/C1-PAPER.md` §1 (reviewed):

- Identity 1.1: g(S) = 2D^S(S_Q) + 6(|S_P| − |S_Q|) = 2D^S(S_P) + 6(|S_Q| − |S_P|); so if the larger
  class of G[S] exceeds the smaller by j and the smaller has in-S deficiency d, g(S) = 2d + 6j.
- Identity 1.3: g(S − v) = g(S) − 6 + 2deg_{G[S]}(v).
- Lemma 1.4 (flow criterion) and the proof of Lemma 1.5 (E4 reduction).

An *instance* is a bipartite graph with Δ ≤ 6 and e = 3n − 4 (so g(V) = 8). It is *E4* if |P| = |Q|
(then D(P) = D(Q) = 4) and *C1* if the classes have sizes s and s + 1 (then the smaller has deficiency 1
and the larger 7). It is *sparse* if g(S) ≥ 10 whenever 2 ≤ |S| ≤ n − 1. A 4-factor is a spanning
4-regular subgraph; a set T is *balanced* if |T_P| = |T_Q|.

For a 4-factor F and a balanced T, summing F-degrees over T_P and over T_Q gives

    e_F(T_P, Q − T) = e_F(T_Q, P − T),   so   ∂_F(T) = 2·e_F(T_Q, P − T).           (1)

## 2. Smallest counterexamples

**Lemma 1.** Let X be a bipartite graph with Δ ≤ 6, n ≥ 2, e ≥ 3n − 4 and no pair, with n minimal and
then e minimal. Then e = 3n − 4, X is sparse, X is E4 or C1, and δ(X) ≥ 4. (n ≥ 3 since a simple
graph on 2 vertices has ≤ 1 edge; the census F2 of STATE.md, bipartite n ≤ 18, gives n ≥ 19.)

*Proof.* If e > 3n − 4, deleting any edge gives a counterexample with fewer edges. If 2 ≤ |S| ≤ n − 1
and g(S) ≤ 8, then e(S) ≥ 3|S| − 4 and X[S] is a pair-free counterexample on fewer vertices. So X is
sparse. g(V) = 8 = 2d + 6j forces (j, d) = (0, 4) or (1, 1). For v ∈ V, g(V − v) = 2 + 2deg v by
Identity 1.3, and sparsity (|V − v| ≥ 2) gives deg v ≥ 4. ∎

**Lemma 2.** A sparse E4 instance Y with |P| = |Q| = a ≥ 2 has a 4-factor.

*Proof.* Otherwise C1-PAPER Lemma 1.4 gives A ⊆ P, C ⊆ Q with k = |A| − |C| ≥ 1 and
D_A ≥ 2k + 1 + ε, ε = D_C + e(P − A, C); as D_A ≤ 4, k = 1, ε ≤ 1 and D_A ≥ 3 + ε. The pieces
Y[A ∪ C] and Y[(P − A) ∪ (Q − C)] have class sizes differing by one, and their smaller classes (C and
P − A) have in-piece deficiency ε ≤ 1 and (4 − D_A) + ε ≤ 1. So each piece has g ≤ 2 + 6 = 8. Each
piece is nonempty and is the complement of the other, so a piece with ≥ 2 vertices violates sparsity;
if both are single vertices then a = 1. ∎

## 3. Thin sets

**Proposition 3.** Let Y be a sparse E4 instance and T a balanced set with 2 ≤ |T| ≤ n − 2. Then
∂_Q(T) ≥ 1. If ∂_Q(T) = 1 then

    D(T_Q) = 4, D(T_P) = 0, ∂_P(T) = 5, D(P − T) = 4, D(Q − T) = 0, g(T) = g(V − T) = 10,

(a *(5,1) set*); the same holds with P and Q exchanged. If T is a (5,1) set then every 4-factor F has
∂_F(T) ≤ 2, so no 4-factor of Y is Hamilton-decomposable.

*Proof.* Y[T] is balanced, so by Identity 1.1 g(T) = 2D^T(T_Q) = 2(D(T_Q) + ∂_Q(T)), and g(T) ≥ 10
with D(T_Q) ≤ D(Q) = 4 gives ∂_Q(T) ≥ 1, with equality only if D(T_Q) = 4. In that case D(Q − T) = 0.
V − T is balanced and |V − T| ≥ 2, so

    10 ≤ g(V − T) = 2D^{V−T}(Q − T) = 2(D(Q − T) + ∂_P(T)) = 2∂_P(T),
    10 ≤ g(V − T) = 2D^{V−T}(P − T) = 2(D(P − T) + ∂_Q(T)) = 2(D(P − T) + 1) ≤ 10.

Hence g(V − T) = 10, D(P − T) = 4, ∂_P(T) = 5, and D^T(T_P) = D^T(T_Q) reads D(T_P) + 5 = 4 + 1, so
D(T_P) = 0 and g(T) = 10. For the last claim, (1) gives ∂_F(T) = 2e_F(T_Q, P − T) ≤ 2∂_Q(T) = 2, and
the union of two Hamilton cycles crosses every nontrivial cut at least four times. ∎

**Example 4 (R20).** Vertices P = {0, ..., 9}, Q = {10, ..., 19}; T_P = {0..4}, W_P = {5..9},
T_Q = {10..14}, W_Q = {15..19}. Edges: all of T_P × T_Q and W_P × W_Q (two copies of K_{5,5}), the
matching 0–15, 1–16, 2–17, 3–18, 4–19, and the edge 10–5. Then n = 20, e = 56 = 3n − 4, degrees 5^8 6^12,
Δ = 6, and Y is an E4 instance.

- *Sparse.* Checked twice: by the flow method of `ptool.c` (for each edge uv, the minimum of g over sets
  containing u and v, which suffices because an inclusion-minimal set with g ≤ 8 and ≥ 2 vertices has
  internal minimum degree ≥ 4 by Identity 1.3) and by brute force over all 2^20 subsets
  (`brute_sparse.py`): min g over 2 ≤ |S| ≤ 19 is 10.
- *T = T_P ∪ T_Q is a (5,1) set*: ∂_Q(T) = 1 (the edge 10–5). By Proposition 3 no 4-factor of Y is
  Hamilton-decomposable, so Y has no two edge-disjoint Hamilton cycles. The exhaustive search agrees
  (`ptool h`: 1,658,880 Hamilton cycles through vertex 0, none with a Hamiltonian complement).
- *Pair:* K_{4,4} on {0, 1, 2, 3, 10, 11, 12, 13} is two edge-disjoint Hamilton cycles
  (0,10,1,11,2,12,3,13 and 0,11,3,10,2,13,1,12; `pairc w`).

graph6: `data/rigid20.g6`. Consequence: "every sparse instance has two edge-disjoint Hamilton cycles"
and "every sparse E4 instance has a 4-factor with no 2-edge cut" are both false. Every sparse E4
instance on ≤ 18 vertices does have two edge-disjoint Hamilton cycles (census in `SCOUT.md` §2.1), and
a (5,1) side T needs 6t − 5 = e(T) ≤ t², so t ≥ 5 and n ≥ 20: R20 is the smallest possible size.

## 4. Sets with g = 10 in a smallest counterexample

**Census L5** (genbg 2.9.3 + `pairc f`, one method, `SCOUT.md` §2.4): there is no pair-free bipartite
graph with δ ≥ 4, Δ ≤ 6 and e = 3n − 5 on ≤ 17 vertices (classes 5+5, 6+6, 7+7, 8+8, 4+5, 5+6, 6+7,
7+8, 8+9: 1, 13, 819, 229,913, 0, 2, 29, 2,895, 1,237,978 graphs (1,471,650 in all), none pair-free; level −5 forces
class difference ≤ 1 by Identity 1.1).

**Proposition 5.** Let X be as in Lemma 1 and S a set with 2 ≤ |S| ≤ n − 1 and g(S) = 10. Then the
4-core K of X[S] is nonempty, pair-free, e(K) = 3|K| − 5, and (by L5) |K| ≥ 18.

*Proof.* e(S) = 3|S| − 5. Deleting a vertex of degree ≤ 3 does not decrease e − 3n, so if K ≠ ∅ then
e(K) ≥ 3|K| − 5; if K = ∅ then X[S] is 3-degenerate and e(S) ≤ 3|S| − 6. K is a proper subset with
≥ 2 vertices, so sparsity gives e(K) ≤ 3|K| − 5. K is pair-free, bipartite, Δ ≤ 6, δ ≥ 4. ∎

**Corollary 6.** If X (Lemma 1) is of E4 type and has a (5,1) set T, then n ≥ 36.

*Proof.* g(T) = g(V − T) = 10 by Proposition 3; apply Proposition 5 to both. ∎

## 5. One-swap repair

Let F be a 4-factor of a sparse E4 instance Y and H = Y − F. Let D be the digraph with an arc p → q
for every pq ∈ F and an arc q → p for every pq ∈ H (p ∈ P, q ∈ Q). A directed cycle Z of D alternates
F- and H-arcs, so F Δ E(Z) is a 4-factor.

**Lemma 7.** Let T be balanced with 2 ≤ |T| ≤ n − 2 and ∂_F(T) = 2, with F-cut edges e1 = p1q'
(p1 ∈ T_P) and e2 = p'q1 (q1 ∈ T_Q). Let D⁻ = D − {e1, e2}.

(a) If a directed cycle Z of D⁻ contains an arc q → p with q ∈ T_Q, p ∈ P − T, then F' = F Δ E(Z)
is a 4-factor with ∂_{F'}(T) ≥ 4.

(b) Otherwise, for every H-edge qp with q ∈ T_Q, p ∈ P − T, the set X of vertices reachable from p in
D⁻ misses q, and with ε ∈ {0, 1, 2} the number of e_i whose P-end is in X and Q-end is not,

    g(X) = 2j + 2ε + 2D(X_Q),   e_H(X_P, Q − X) = D(X_Q) − D(X_P) − 2j,   j = |X_Q| − |X_P|,
    3D(X_Q) ≥ 11 − 2ε + D(X_P);   so D(X_Q) ≥ 3, and if ε = 0 then D(X_Q) = 4, D(X_P) ≤ 1, j = 1.

*Proof.* (a) The only F-edges crossing ∂T are e1 and e2, which are not in D⁻, so F' contains e2 and the
H-edges of Z from T_Q to P − T: e_{F'}(T_Q, P − T) ≥ 2, and (1) gives ∂_{F'}(T) ≥ 4.

(b) A path from p to q in D⁻ plus the arc q → p would be a cycle as in (a), so q ∉ X. X is closed
under out-arcs of D⁻: every F-edge at a vertex of X_P other than e1, e2 ends in X_Q, and every H-edge at
a vertex of X_Q ends in X_P. Hence e_F(X) = 4|X_P| − ε and e_H(X) = Σ_{X_Q}(deg − 4) = 2|X_Q| − D(X_Q),
which gives g(X). Identity 1.1 gives g(X) = 2D^X(X_P) + 6j with
D^X(X_P) = D(X_P) + ε + e_H(X_P, Q − X), which gives the second identity. X contains p and at least three
F-neighbours of p, and misses q, so g(X) ≥ 10, i.e. j ≥ 5 − ε − D(X_Q). The H-edge qp leaves X from X_P,
so D(X_Q) − D(X_P) − 2j ≥ 1. Substituting the lower bound for j gives 3D(X_Q) ≥ 11 − 2ε + D(X_P) ≥ 7.
If ε = 0 this forces D(X_Q) = 4 (D(Q) = 4), then D(X_P) ≤ 1, and 1 ≤ j ≤ (3 − D(X_P))/2 gives j = 1. ∎

*Remark.* If ε = 0 and D(X_P) = 0, then g(X) = 10, ∂_P(X) = 2, ∂_Q(X) = 4, and for every 4-factor F''
the degree sums give e_{F''}(X_Q, P − X) − e_{F''}(X_P, Q − X) = 4j = 4, so F'' contains the four edges
leaving X_Q and neither edge leaving X_P: X is a one-passage 4-edge cut of every 4-factor. Lemma 7 does
not say that repeated swaps terminate (a swap removes F-edges along Z and can create a new 2-edge cut).

## 6. The one-mark CP4 statement is false

W1-MINIMAL.md §4a states, for graphs Y on m ≤ 11 vertices with Δ ≤ 6 and e = 3m − 3: if ab, cd are
disjoint edges and Y − ab − cd is pair-free, then Y has a pair with ab and cd on different cycles. Its
proof assumes that a pair through the new vertex v of (Y − ab − cd) + v uses v as a–v–b and c–v–d; it
may use a–v–c and b–v–d, or a–v–d and b–v–c (`paper110/certificates/FIXED-MATCHING.json` records this
gap).

**Example 8.** Let Z range over all pair-free graphs with Δ ≤ 6, e(Z) = 3|Z| − 5, |Z| ≤ 11: by peeling,
each is one of the 17 graphs of `reports/585-fable/data/frontier-n{7,8,9,10}-level-5.g6` plus vertices
added with exactly three neighbours (the W1 census for n ≤ 12 and the level −5 census for n ≤ 11 fix the
4-core); `gen_t1.py` lists them up to isomorphism (labelg): 1, 4, 41, 457, 5,122 graphs on 7..11
vertices. Among the 76,975 graphs Y = Z + ab + cd (ab, cd disjoint non-edges of Z, Δ(Y) ≤ 6), exactly 6
have no pair with ab and cd on different cycles, all on 11 vertices with e = 30 (`data/t1_none.txt`,
graph6 and marks a b c d). Checks: `mpair.c` (exhaustive over vertex sets, Hamilton cycles through ab,
then through cd in the complement) and `verify_t1.py` (independent: networkx `simple_cycles` lists all
11,394 to 12,242 cycles of each Y and tests every pair of edge-disjoint cycles on a common vertex set).
The second check also confirms that Z = Y − ab − cd is pair-free and that X = Z + v (12 vertices,
e = 3·12 − 4) has pairs through v only with the two other pairings.

So the statement is false, not only its proof. W1 itself is untouched: X has pairs.

## 7. Not proved here

- No pair theorem: W1b, B6 and B6⁺ are open. Lemma 7 repairs one cut once; whether a 4-factor without
  2-edge cuts exists in every sparse E4 instance without rigid sets, and whether rigid sets other than
  (5,1) sets exist, is open (`SCOUT.md` §4).
- Census L5 (and H22 in `SCOUT.md`) are one-method computations; their trust rests on genbg's
  completeness and on `pairc` (L5) or `ptool` with witness re-checks (H22).
- C1-type instances: Proposition 3 and Lemma 7 are stated for E4 only.
