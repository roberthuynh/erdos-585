# Pairs scout (Pass 3 wave 3, CONTINUE.md step C1): candidate statements, census verdicts, gaps

Lane: pairs scout, October 5, 2026. Log: `LOG.md`. Code and data: this folder (`ptool.c`, `mpair.c`,
`cuts.c`, `data/`). Nothing here is reviewed. No `check.sh`, no Lean. Rungs as in STATE.md.

## 0. Verdict in brief

| # | Statement | Verdict | Rung |
|---|---|---|---|
| A | A smallest W1b counterexample is a *sparse* E4 or C1 instance, n ≥ 19 | proved (§1) | (a) |
| B | A sparse E4 instance has a spanning 4-factor | proved (§1) | (a) |
| SP | Every sparse instance has two edge-disjoint Hamilton cycles (E4), or at every good port y, X − y has them (C1) | **false** at n = 20 (§2.1, `data/rigid20.g6`); true on every instance tested below n = 20 and on 30 built C1 instances at n = 27, 29 | (b) counterexample |
| C | In a sparse E4 instance, a balanced set T with at most one edge leaving one color class is a "(5,1) set": g(T) = g(V − T) = 10 and all deficiency of one color sits on one side; it is a 2-edge cut of every 4-factor | proved (§1) | (a) |
| 2EC | Every sparse E4 instance has a 4-factor with no 2-edge cut | **false** (same example) | (b) |
| H22 | Every connected bipartite 4-regular graph on ≤ 22 vertices with no 2-edge cut is Hamilton-decomposable | census, one method (§2.3) | (b) |
| L5 | No pair-free bipartite graph with δ ≥ 4, Δ ≤ 6 and e = 3n − 5 on ≤ 17 vertices | census, one method (§2.4), 1.47M graphs | (b) |
| A' | A smallest W1b counterexample of E4 type with a (5,1) set has n ≥ 36 | proved from L5 (§1, Cor. 1.5) | (a)+(b) |
| T1 | One-mark CP4, prescribed pairing (W1-MINIMAL.md §4a) | **false** at m = 11, six instances, two independent checks (§3.1) | (b) |
| T2 | X = Z + v (Z pair-free, level −5, deg v = 4): pairs through v realize ≥ 2 of the 3 pairings of N(v) | survives every X on ≤ 12 vertices (66,992 graphs); sharp (82 realize exactly 2) | (b) |
| D | If a 2-edge cut of a 4-factor cannot be repaired by one alternating-cycle swap that keeps the two cut edges, an out-closed set holds ≥ 3 of the 4 units of Q-deficiency | proved (§4) | (a) |
| SP' | Repair of SP: no *rigid* set ⇒ spanning pair | open; the closure attempt (§4) stops here | — |

The strongest candidate the census suggested (SP: sparse ⇒ spanning pair) is false, and the reason is
exactly a rigid cut: a tight 6-edge cut whose six edges split 5 + 1 between the two color classes.
So the B-3 two-step route ("pick a 4-factor with no small cut, then decompose it") cannot work as
stated: in some sparse instances every 4-factor has a 2-edge cut, and the pair must be found on a
proper subset. The repaired route (§4) needs a structure theory of rigid sets (tight sets with skewed
deficiency) plus an HD statement for 4-regular bipartite graphs without 2-edge cuts; H22 gives the HD
statement through 22 vertices, and Lemma D is the first step of the rigid-set theory. No closure.

## 1. Lemmas (rung (a), written here, not reviewed)

Notation as in C1-PAPER §1: g(S) = 6|S| − 2e(S); D(Z) = Σ_{v∈Z}(6 − deg v); D^S(Z) is deficiency
inside G[S]. For a bipartite graph with color classes P, Q and S ⊆ V, Identity 1.1 gives
g(S) = 2D^S(S_Q) + 6(|S_P| − |S_Q|) = 2D^S(S_P) + 6(|S_Q| − |S_P|). An *instance* is bipartite with
Δ ≤ 6 and e = 3n − 4; *sparse* means g(S) ≥ 10 for 2 ≤ |S| ≤ n − 1.

**Lemma 1.1 (smallest counterexample).** Let X be a bipartite graph with Δ ≤ 6, e ≥ 3n − 4, n ≥ 2 and
no pair, with n minimal and then e minimal. Then e = 3n − 4, X is sparse, δ(X) ≥ 4, and X is either
E4 (|P| = |Q|, D(P) = D(Q) = 4) or C1 (|U| = s, |W| = s + 1, D(U) = 1, D(W) = 7). By the F2 census
(STATE.md, bipartite n ≤ 18) n ≥ 19.

*Proof.* Deleting an edge keeps every hypothesis except possibly e ≥ 3n − 4, so e = 3n − 4. If
2 ≤ |S| ≤ n − 1 and g(S) ≤ 8 then e(S) ≥ 3|S| − 4 and X[S] is a smaller counterexample (pair-free
because X is). So X is sparse. g(V) = 8 = 2d + 6j (Identity 1.1, j the side difference, d the
deficiency of the smaller side) gives (j, d) = (0, 4) or (1, 1). g(V − v) = 8 − 6 + 2deg v ≥ 10 gives
deg v ≥ 4. ∎

**Lemma 1.2 (spanning 4-factor).** A sparse E4 instance with a ≥ 2 has a 4-factor.

*Proof.* If not, the proof of C1-PAPER Lemma 1.5 gives a violation (A, C) with k = 1 and two pieces
G[A ∪ C] and G[(P − A) ∪ (Q − C)], each with side difference 1 and smaller-side deficiency ≤ 1, so
g ≤ 2 + 6 = 8 on each. Both pieces are nonempty; a piece with ≥ 2 vertices is proper (the other is
nonempty) and violates sparsity; if both are single vertices then a = 1. ∎

**Lemma 1.3 (thin sets are (5,1) sets).** Let Y be a sparse E4 instance and T a set with
|T_P| = |T_Q| and 2 ≤ |T| ≤ n − 2. Write ∂_Q(T) = e(T_Q, P − T) and ∂_P(T) = e(T_P, Q − T). Then
∂_Q(T) ≥ 1, and ∂_Q(T) = 1 holds only if D(T_Q) = 4, D(T_P) = 0, ∂_P(T) = 5, D(P − T) = 4,
D(Q − T) = 0 and g(T) = g(V − T) = 10. The same with P and Q exchanged. For every 4-factor F,
∂_F(T) = 2·e_F(T_Q, P − T) ≤ 2∂_Q(T); so a (5,1) set is a cut of size ≤ 2 in every 4-factor, and no
4-factor of Y is Hamilton-decomposable (a union of two Hamilton cycles crosses every cut ≥ 4 times).

*Proof.* G[T] is balanced, so g(T) = 2D^T(T_Q) = 2(D(T_Q) + ∂_Q(T)) ≥ 10, and D(T_Q) ≤ D(Q) = 4
gives ∂_Q(T) ≥ 1, with equality only if D(T_Q) = 4. Then D(Q − T) = 0, and V − T is balanced with
g(V − T) = 2D^{V−T}(Q − T) = 2(0 + ∂_P(T)) ≥ 10, so ∂_P(T) ≥ 5; also
g(V − T) = 2D^{V−T}(P − T) = 2(D(P − T) + ∂_Q(T)) = 2(D(P − T) + 1) ≤ 10, so ∂_P(T) = 5,
D(P − T) = 4, g(V − T) = 10, and D^T(T_P) = D^T(T_Q) gives D(T_P) + 5 = 4 + 1, D(T_P) = 0. The
4-factor statement: summing F-degrees over T_P and over T_Q gives e_F(T_P, Q − T) = e_F(T_Q, P − T). ∎

**Lemma 1.4 (a (5,1) set has a large 4-core).** In Lemma 1.1's X, let S be any set with
2 ≤ |S| ≤ n − 1 and g(S) = 10 (for example either side of a (5,1) set). Then the 4-core K of X[S] is
nonempty, pair-free, bipartite, Δ ≤ 6, δ ≥ 4, e(K) = 3|K| − 5, and |K| ≥ 18.

*Proof.* g(S) = 10 means e(S) = 3|S| − 5. Peeling a vertex of degree ≤ 3 does not lower e − 3n, so
e(K) ≥ 3|K| − 5 if K ≠ ∅; K = ∅ would make X[S] 3-degenerate, with e ≤ 3|S| − 6. K ⊆ S is proper with
|K| ≥ 2, so sparsity (Lemma 1.1) gives e(K) ≤ 3|K| − 5; hence equality. K is pair-free because X is,
and census L5 (§2.4: no such graph on ≤ 17 vertices) gives |K| ≥ 18. ∎

**Corollary 1.5.** If a smallest W1b counterexample X is of E4 type and has a (5,1) set T, then both T
and V − T have g = 10 (Lemma 1.3), so both contain ≥ 18 vertices (Lemma 1.4), and n ≥ 36.

**Corollary 1.6.** In a smallest W1b counterexample, every component on ≤ 22 vertices of every
4-regular subgraph has a 2-edge cut (a component without one would be Hamilton-decomposable by H22,
§2.3, which is a pair).

## 2. Census (rung (b); one method each unless said)

Tools: `ptool.c` (sparsity by max flow: for every edge uv, min of g over sets containing u, v; an
inclusion-minimal violator has an internal min degree ≥ 4, so it contains an edge; validated against
brute force on 42 graphs), spanning-pair test (pairc's Hamilton-cycle search, plus a randomized
Warnsdorff first-cycle search used only to *find* witnesses), C1 port test (flow 4-factor, then
spanning pair of X − y). `pairc` from `reports/585-fable/tools/` for general pair tests. Generator: nauty
genbg 2.9.3 at `~/.cache/erdos585/nauty2_9_3/genbg` (genbg keeps color classes, so a graph whose
classes can be swapped may appear twice; this only over-counts).

### 2.1 Spanning pairs in instances

| Class | Command | Graphs | Result |
|---|---|---|---|
| E4, a = 6, 7, 8 | `genbg -q -d4:4 -D6:6 a a 6a-4:6a-4` | 10; 267; 52,295 (52,280 sparse) | all have two edge-disjoint Hamilton cycles |
| E4, a = 9 (n = 18) | same, `r/100`, 100 shards, piped to `ptool H` | 31,662,400 | all have two edge-disjoint Hamilton cycles |
| C1, s = 5..8 | `genbg -q -d5:4 -D6:6 s s+1 6s-1:6s-1` | 1; 8; 518; 182,908 (all sparse) | every port good; every X − y has two edge-disjoint Hamilton cycles |
| built sparse C1, n = 27 (8) and 29 (22) | C1 lane builder `G110/c1checks/c1build.py` (imported read-only) | 30 | 1-2 bad ports each (bad deficiency ≤ 2, as C1-PAPER Lemma 4.4 says); at every good port X − y has two edge-disjoint Hamilton cycles |
| **R20** | two K_{5,5} joined by a (5,1) cut, `build_rigid.py` | 1 | sparse E4 (flow test and brute force: min g = 10), **no** two edge-disjoint Hamilton cycles (exhaustive, 1,658,880 Hamilton cycles through vertex 0), has a pair (K_{4,4} inside a block) |

R20, explicitly: P = TP ∪ WP, Q = TQ ∪ WQ, each part of size 5; edges: TP × TQ, WP × WQ (two K_{5,5}),
a perfect matching TP–WQ, and one edge TQ_0–WP_0. Degrees 5^8 6^12, n = 20, e = 56 = 3n − 4. T = TP ∪ TQ
is a (5,1) set (Lemma 1.3). graph6 in `data/rigid20.g6`.

So SP fails at n = 20, and the census below n = 20 never saw it because a (5,1) side needs
e(T) = 6t − 5 ≤ t², t ≥ 5, so n ≥ 20. Note that R20 is not a W1b counterexample: each block contains
K_{4,4}, and Lemma 1.4 shows that in a smallest counterexample (5,1) sides are far larger.

### 2.2 W1b at n = 19 (not run)

A smallest counterexample at n = 19 is a sparse C1(9) instance. The class `genbg -d5:4 -D6:6 9 10 53:53`
has about 150 million graphs (two 1/1000 slices: 149,488 and 150,429, 59 and 62 s each), so generation
alone is about 17 core-hours. Not run (lane budget).

### 2.3 H22: Hamilton decompositions of bipartite 4-regular graphs

`genbg -q -c -d4:4 -D4:4 a a 4a:4a | ptool H` (24 shards at a = 11), non-decomposable graphs profiled by
`cuts.c` (every T ∋ vertex 0, Gray code):

| a (n = 2a) | 5 | 6 | 7 | 8 | 9 | 10 | 11 |
|---|---|---|---|---|---|---|---|
| connected graphs | 1 | 4 | 16 | 193 | 3,528 | 121,785 | 5,582,592 |
| not HD | 0 | 0 | 0 | 1 | 2 | 17 | 236 |
| not HD and no 2-edge cut | 0 | 0 | 0 | 0 | 0 | 0 | 0 |

Every non-HD one also has a one-passage 4-edge cut. Known boundary (585-RESEARCH-PLAN §4): a
350-vertex 4-connected bipartite 4-regular graph with no Hamilton cycle (Meredith-type, K_{4,3} blocks,
each a one-passage 4-cut). So "no 2-edge cut ⇒ HD" is false in general; H22 is the finite fact.

### 2.4 L5: pair-free bipartite graphs at level −5

`genbg -q -d4:4 -D6:6 a b 3n-5:3n-5 | pairc f`:

| sides | 5,5 | 6,6 | 7,7 | 8,8 | 4,5 | 5,6 | 6,7 | 7,8 | 8,9 |
|---|---|---|---|---|---|---|---|---|---|
| graphs | 1 | 13 | 819 | 229,913 | 0 | 2 | 29 | 2,895 | 1,237,978 |
| pair-free | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |

(sides 8, 9 in 12 shards, `run_l5s8.sh`.) So no pair-free bipartite graph with δ ≥ 4, Δ ≤ 6 and
e = 3n − 5 has ≤ 17 vertices (level −5 forces side difference ≤ 1, so these classes are complete).
Contrast: for general graphs there are 17 such graphs on 7 to 10 vertices (K2 ∨ C5 and relatives).

## 3. General graphs: one-mark statements (part (b) of the brief)

Every pair-free graph Z with Δ ≤ 6, e(Z) = 3|Z| − 5 and |Z| ≤ 11 is one of the 17 cores of
`reports/585-fable/data/frontier-n{7,8,9,10}-level-5.g6` plus vertices added with exactly three
neighbors (peel the 4-core; the level never drops; the W1 census at n ≤ 12 and the level −5 census at
n ≤ 11 fix the core). `gen_t1.py` builds all of them up to isomorphism (labelg): 1, 4, 41, 457, 5,122
graphs at orders 7..11.

### 3.1 T1 is false

T1 (W1-MINIMAL.md §4a, the "free-partner one-mark CP4 statement"): if Y has Δ ≤ 6, e = 3|Y| − 3, and
ab, cd are disjoint edges with Y − ab − cd pair-free, then Y has a pair with ab and cd on different
cycles. §4a's proof assumed that a pair through the new vertex v uses the pairing {ab, cd}; it can use
either of the other two (the gap the octahedron certificate `paper110/certificates/FIXED-MATCHING.json`
already recorded). The statement itself fails:

- `mpair.c` (exhaustive marked pair search) on all 76,975 marked graphs Y = Z + ab + cd (Z from the list
  above, ab, cd disjoint non-edges, Δ(Y) ≤ 6): 6 have no compatible pair, all on 11 vertices
  (`data/t1_none.txt`).
- Independent check (`verify_t1.py`, networkx `simple_cycles`, 11,394 to 12,242 cycles per graph): no
  compatible pair, Z pair-free, and X = Z + v (12 vertices, e = 3n − 4) has pairs through v only with
  the two other pairings, as the W1 census requires.

Example: the first line of `data/t1_none.txt` (marks 0–1 and 4–5; its graph6 string contains a
backtick, so read it from the file, not from a command line).

### 3.2 T2 survives

T2: for X = Z + v with deg v = 4 and Δ(X) ≤ 6, pairs through v realize at least two of the three
pairings of N(v). `gen_t2.py` + `mpair` with a forbidden edge: 66,992 graphs X on ≤ 12 vertices, all
realize ≥ 2; exactly 2 in 82 (4 on 11 vertices, 78 on 12). Use: across a cut contracted to a vertex of
degree 4 or 5, "≥ 2 of 3 on each side" forces a common pairing, so gluing succeeds. T2 implies W1 for
graphs with a degree-4 vertex, so it is a strengthening, but I found no split step that proves T2
from smaller T2: a minimal T2 counterexample X has X − v pair-free at level −5, and splitting another
vertex meets the same compatibility question. Not pursued further.

## 4. Closure attempt: the repaired spanning route, and where it stops

Target (SP', repaired): a sparse E4 instance with no *rigid* set has two edge-disjoint Hamilton cycles,
where T (balanced, 2 ≤ |T| ≤ n − 2) is rigid if every 4-factor F has e_F(T_Q, P − T) ≤ 1. With H22 the
target would follow, for n ≤ 22, from

**Lemma 2EC' (wanted).** A sparse E4 instance with no rigid set has a 4-factor with no 2-edge cut.

and then Lemma 1.1, Corollary 1.5 and H22 would give W1b for E4-type smallest counterexamples with
n ≤ 22, provided rigid sets can also be excluded there (Lemma 1.3 and Corollary 1.5 exclude the thin ones
for n < 36).

**What I proved: Lemma D (one-swap repair).** Let F be a 4-factor of a sparse E4 instance Y, H = Y − F,
and T a balanced 2-edge cut of F with F-cut edges e1 = p1q' (p1 ∈ T_P) and e2 = p'q1 (q1 ∈ T_Q). Orient
F-edges P → Q and H-edges Q → P (digraph D; its directed cycles are the alternating cycles, and
F Δ Z is again a 4-factor) and delete e1, e2 (digraph D⁻). If some H-edge from T_Q to P − T lies on a
directed cycle Z of D⁻, then F Δ Z has ∂(T) ≥ 4. If none does, then for every H-edge qp with q ∈ T_Q,
p ∈ P − T, the set X = Reach_{D⁻}(p) (closed under out-arcs of D⁻) misses q and satisfies

    D(X_Q) ≥ 3,    and if ε = 0:  D(X_Q) = 4, D(X_P) ≤ 1, |X_Q| = |X_P| + 1,

where ε ≤ 2 is the number of the edges e1, e2 whose P-end is in X and whose Q-end is not.

*Proof.* Arcs of D⁻ crossing ∂T are H-arcs only, so a cycle through an H-arc from T_Q gains at least
one F-edge from T_Q to P − T and loses none (e2 is not in D⁻), giving e_{FΔZ}(T_Q, P − T) ≥ 2. If no such
cycle exists, take any H-arc q → p leaving T; then q ∉ X = Reach_{D⁻}(p). X is closed under out-arcs:
F-neighbors of X_P lie in X_Q except along e1, e2, and H-neighbors of X_Q lie in X_P. Hence
e(X) = (4|X_P| − ε) + (2|X_Q| − D(X_Q)), and with j = |X_Q| − |X_P|:

    g(X) = 2j + 2ε + 2D(X_Q),   e_H(X_P, Q − X) = D(X_Q) − D(X_P) − 2j      (from Identity 1.1).

X contains p and its F-neighbors, and misses q, so 2 ≤ |X| ≤ n − 1 and g(X) ≥ 10: j + ε + D(X_Q) ≥ 5.
The H-edge qp leaves X from X_P, so D(X_Q) − D(X_P) − 2j ≥ 1. Eliminating j:
3D(X_Q) ≥ 11 − 2ε + D(X_P) ≥ 7, so D(X_Q) ≥ 3. If ε = 0 the same inequalities give D(X_Q) = 4,
D(X_P) ≤ 1, j = 1. ∎

In the ε = 0, D(X_P) = 0 case, X is a tight set (g = 10) with one more Q- than P-vertex, ∂_Q(X) = 4 and
∂_P(X) = 2, and every 4-factor contains the four edges leaving X_Q and none of the two leaving X_P (the
degree sums force it): a *rigid one-passage 4-cut*. (A check I first got wrong: X minus a vertex q0 ∈ X_Q that carries three of those four edges is
balanced and is a 2-edge cut of every 4-factor, but it is thin on the Q side, so Lemma 1.3 already
covers it. Whether a rigid set can have ≥ 2 edges leaving each color class is open.)

**Exact gap.**
1. *Rigid sets.* Classify the sets T with max over 4-factors of e_F(T_Q, P − T) ≤ 1 in a sparse
   instance (Lemma 1.3 does the thin ones; are there others?). By LP duality for bipartite b-matchings this maximum has a cut certificate; Lemma D says
   the certificates found so far are tight sets with deficiency concentrated on one color (≥ 3 of the
   4 units). The deficiency budget (4 + 4 units) suggests few rigid sets, as in the C1 petal argument,
   but I have no proof that they uncross or that a smallest counterexample has none.
2. *From one cut to all cuts.* Lemma D repairs one 2-edge cut with one swap; the swap removes F-edges
   along Z and can create a new 2-edge cut. A potential that decreases (number of 4-edge-connected
   classes of F) needs control of the removed F-edges, which I do not have.
3. *Beyond 22 vertices.* Even with Lemma 2EC', the HD step is only H22. For all n it would need an HD
   theorem for bipartite 4-regular graphs without 2-edge cuts and without non-rigid one-passage 4-cuts;
   the 350-vertex Meredith-type graph shows one-passage cuts must be excluded, and whether that suffices
   is open (no counterexample known to me, none on ≤ 22 vertices).
4. *C1 type.* At a good port y, Y = X − y has deficiency 5 or 6 per side, so Lemma 1.3 and Lemma D are
   weaker (thin sets need only D(T_Q) ≥ 4 of 5 or 6); not worked out.

Stop condition reached: one closure attempt (Lemma 2EC' via Lemma D), stopped at gap items 1 and 2.

## 5. What this means for the C1 step and what I would do next

- The C1 tools give a clean reduction (Lemma 1.1, 1.2) and a clean obstruction (Lemma 1.3, Lemma D):
  in sparse instances, small cuts of 4-factors are either repairable by one swap or certified by tight
  sets with concentrated deficiency. That is the "rigid cut" structure the brief asked about; it is the
  same deficiency-budget mechanism that closed C1, but here the objects are not yet shown to uncross.
- Highest-value next step: a census of rigid sets (max over 4-factors of e_F(T_Q, P − T), by min-cost
  flow) in sparse E4/C1 instances at n = 20..30 built from tight sets, to see whether every rigid set is
  a (5,1) set or a Lemma D set, and whether two rigid sets can cross. If they cannot, gap items 1-2 may
  close for n ≤ 22, which with H22 and Corollary 1.5 would give W1b for E4-type counterexamples through
  22 vertices without the 17 core-hour C1(9) census.
- The gluing route across a (5,1) set (contract one side to a degree-5 vertex: T + q* has e = 3n − 3)
  needs T2 for bipartite graphs, and by L5 the relevant Z have ≥ 18 vertices, far beyond any census.
- T1 should be retired from the project's list of "true up to 11 vertices" claims (W1-MINIMAL.md §4a,
  585-fable/REPORT.md section E).
- Not tested: whether SP's C1 half (good ports) also fails; R20 is E4. A C1 analog would need a thin
  set in X − y, where the deficiency budget is 5 or 6 per side, so it is likely easier to build.
- The complete pieces are collected with proofs and certificates in `PAPER.md` (frozen,
  `FROZEN.sha256`) for a referee. Numbering: Lemma 1.1 = PAPER Lemma 1, 1.2 = Lemma 2, 1.3 = Prop 3,
  R20 = Example 4, 1.4 = Prop 5, 1.5 = Cor 6, Lemma D = Lemma 7, T1 = Example 8.
- Reproducibility: the large census runs used the binary `ptool`, built from an earlier revision of
  `ptool.c`; the exact search is unchanged in the current file (built as `ptool2`, which adds a step
  budget, a randomized witness search used only for the n = 27, 29 built instances, and mode `w` that
  prints witnesses for `verify_sp.py`). `data/` is about 43 MB of graph lists and outputs.
