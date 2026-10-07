# Rigid sets in sparse bipartite instances: an LP criterion, a classification, and no rigid set below 36 vertices

wave4/theory (Pass 3 wave 4), October 5, 2026. Frozen for review (SHA-256 in `FROZEN.sha256`). Written
proofs plus computer checks. Not reviewed. No Lean, no `check.sh`. Rungs as in STATE.md: the items marked
"proof" in §0 are (a), some of them resting on the censuses named there; the checks of Appendix A are (b).
Lemma B, Conjecture M*, Conjecture M*_1, Lemma 2EC' and (HD-OP) are open in this paper.

## 0. Results

| Item | Statement | Kind |
|---|---|---|
| Lemma 1.1 | the slack s(S) = 4\|S_P\| − 4\|S_Q\| + e(S_Q, P − S) is the out-degree of S in the orientation of Y given by any 4-factor; s = g/2 − j − D(S_Q) | proof |
| Theorem 2.1 | max over 4-factors of \|F ∩ E0\| = min over integer potentials of Σ_t s(S_t) + #(uncut E0 edges) | proof (LP duality) |
| Corollary 2.2 | a balanced T is rigid iff (A) all but at most one edge of E(T_Q, P − T) lie in no 4-factor, or (B) the others lie in E(S_P, Q − S) for one set S with s(S) = 1 | proof |
| Lemma 3.1 | in a sparse E4 instance the sets with s ≤ 1 are of seven explicit types | proof; exhaustive check on 52,557 instances |
| Proposition 4.1 | a sparse E4 instance with a rigid set has a set S with g(S) = g(V − S) = 10, \|S\|, \|V − S\| ≥ 3 | proof |
| Theorem 5.1 | a smallest W1b counterexample of E4 type with n < 36 has no rigid set | proof, from PAPER Prop 5 and census L5 |
| Lemma 6.1 | in a smallest E4-type counterexample with n ≤ 22, every bad set of a 4-factor has both sides ≥ 8 vertices, the smaller side is K_{4,4} − e or a pair-free 5 + 5 graph with 19-21 edges, and a 4-factor has at most one bad pair | proof, from Prop 5, L5 and the 5 + 5 census (App. A) |
| Identity 6.2 | reversing a cycle Z changes c(U) by #HH − #FF runs of Z in U | proof |
| Theorem 6.3 | Conjecture M* plus existence of the repair cycle implies Lemma 2EC' | proof (conditional) |
| Remark 6.4 | the corridor template for a counterexample to M* violates sparsity | proof |
| Proposition 6.6 | n ≤ 22: the shortest one-crossing cycle repairs the bad pair and creates no new bad set | proof |
| Lemma B | n ≤ 22: a one-crossing cycle exists at the bad pair | open here; proved when the small side is K_{4,4} − e and a cycle through an E0 H-arc exists |
| Conjectures M*, M*_1 | the shortest repair cycle creates no new bad set (general n) | open; no violation in 2,727 (M*) and 1,388 (M*_1) tests |
| Corollary 6.5 | 2EC' for smallest E4-type counterexamples with n ≤ 22 implies there are none | proof (conditional), with census H22 |
| Lemma 7.1, Corollary 7.2 | at a port of a smallest C1-type counterexample, s(S) ≥ 2 − [u1 ∈ S] − j(S); no thin set at any port when n ≤ 21 | proof |
| Lemma 7.3 | n ≤ 21: a forced set excluding an edge at a port needs n = 21; for n = 19 no edge at a port is excluded | proof |
| (HD-OP) | connected bipartite 4-regular, no 2-edge cut and no non-trivial one-passage 4-cut implies Hamilton-decomposable | open (implied by H22 for n ≤ 22) |

"PAPER" below is `reports/585-next/wave3/pairs/PAPER.md` (frozen 6fad9b43…, refereed ACCEPT WITH FIXES in
`wave3/pairs/REVIEW.md`). "C1-PAPER" is `reports/585-next/G110/C1-PAPER.md` (refereed twice).

## 1. Setting, and the orientation of a 4-factor

Y is a finite simple bipartite graph with color classes P, Q, Δ(Y) ≤ 6. For S ⊆ V: S_P = S ∩ P,
S_Q = S ∩ Q, e(S) = e(Y[S]), g(S) = 6|S| − 2e(S), j(S) = |S_Q| − |S_P|, D(Z) = Σ_{v∈Z}(6 − deg v),
∂_Q(S) = e(S_Q, P − S), ∂_P(S) = e(S_P, Q − S), ∂(S) = ∂_P(S) + ∂_Q(S). An *instance* has e = 3n − 4;
it is *E4* if |P| = |Q| (then D(P) = D(Q) = 4) and *sparse* if g(S) ≥ 10 for 2 ≤ |S| ≤ n − 1. A sparse
instance has δ ≥ 4 (PAPER Lemma 1) and, if E4, a 4-factor (PAPER Lemma 2). A set T is *balanced* if
|T_P| = |T_Q|. For a 4-factor F and balanced T, c_F(T) = e_F(T_Q, P − T) = e_F(T_P, Q − T) (PAPER (1)),
so ∂_F(T) = 2c_F(T). A cut of at most 2 edges of a 4-regular bipartite graph is balanced (degree sums),
so F has a cut of ≤ 2 edges iff c_F(T) ≤ 1 for some balanced T with 2 ≤ |T| ≤ n − 2; call such T *bad*
for F. T is *rigid* if it is bad for every 4-factor. E0(T) = E(T_Q, P − T), E1(T) = E(T_P, Q − T).

Elementary identities (from Σ_{S_Q} deg = 6|S_Q| − D(S_Q) = e(S) + ∂_Q(S), e(S) = 3|S| − g(S)/2, and
the same over S_P):

    ∂_Q(S) = g(S)/2 + 3j(S) − D(S_Q),    ∂_P(S) = g(S)/2 − 3j(S) − D(S_P),             (1.1)
    g(S) + g(V − S) = g(V) + 2∂(S).                                                    (1.2)

**Lemma 1.1.** Let F be a 4-factor of a balanced Y and H = Y − F. Orient F-edges from P to Q and
H-edges from Q to P; call this digraph D(F). For every S ⊆ V put
s(S) = 4|S_P| − 4|S_Q| + ∂_Q(S). Then

    s(S) = e_H(S_Q, P − S) + e_F(S_P, Q − S) = |δ^+_{D(F)}(S)| = g(S)/2 − j(S) − D(S_Q).

So s ≥ 0, s does not depend on F, and s is submodular.

*Proof.* F-degree sums over S_Q and S_P: 4|S_Q| = e_F(S_Q, S_P) + e_F(S_Q, P − S) and
4|S_P| = e_F(S_P, S_Q) + e_F(S_P, Q − S). Subtracting, 4|S_P| − 4|S_Q| = e_F(S_P, Q − S) −
e_F(S_Q, P − S); add ∂_Q(S) = e_F(S_Q, P − S) + e_H(S_Q, P − S). The arcs of D(F) leaving S are the
F-arcs from S_P and the H-arcs from S_Q. The last form is (1.1). Out-degree functions of digraphs are
submodular. ∎

Reversing a directed cycle of D(F) gives another 4-factor (out-degrees stay 4 on P and h = deg − 4 on
Q), and two 4-factors differ by a disjoint union of directed cycles of D(F).

## 2. LP duality for max |F ∩ E0|

**Theorem 2.1.** Let Y be balanced bipartite with Δ ≤ 6 and a 4-factor, and E0 ⊆ E(Y). Then

    max_F |F ∩ E0| = min over π: V → Z of  Σ_{t ∈ Z} s(S_t) + |{pq ∈ E0 : π(p) ≤ π(q)}|,

where S_t = {v : π(v) ≥ t}, and the maximum is over 4-factors F.

*Proof.* Primal: maximize Σ_{e∈E0} x_e subject to x(δ(v)) = 4 for all v and 0 ≤ x ≤ 1. The constraint
matrix (vertex-edge incidence of a bipartite graph, with an identity block) is totally unimodular, so
the optimum is attained by a 4-factor. Dual: minimize 4Σ_v y_v + Σ_e z_e subject to
y_p + y_q + z_e ≥ [e ∈ E0] for e = pq, z ≥ 0; its matrix is the transpose, so an optimal dual solution
can be taken integral. Put π(p) = y_p, π(q) = −y_q; for fixed π the best z is
z_pq = max(0, [pq ∈ E0] + π(q) − π(p)), so the dual value is

    Φ(π) = 4(Σ_P π − Σ_Q π) + Σ_{pq ∈ E} max(0, [pq ∈ E0] + π(q) − π(p)).

Since |P| = |Q|, Σ_P π − Σ_Q π = Σ_t (|S_t ∩ P| − |S_t ∩ Q|) (only finitely many terms are nonzero:
S_t = V for t ≤ min π and ∅ for t > max π). For an edge pq ∉ E0, max(0, π(q) − π(p)) is the number of
t with q ∈ S_t ∌ p. For pq ∈ E0: if π(p) > π(q) the term is 0 and no t has q ∈ S_t ∌ p; if
π(p) ≤ π(q) the term is 1 plus the number of t with q ∈ S_t ∌ p. Summing,
Φ(π) = Σ_t [4(|S_t ∩ P| − |S_t ∩ Q|) + ∂_Q(S_t)] + |{pq ∈ E0 : π(p) ≤ π(q)}|. ∎

An edge pq ∈ E0 with π(p) > π(q) is *cut* by some level: p ∈ S_t, q ∉ S_t, i.e. pq ∈ ∂_P(S_t)
(as an edge of E(S_P, Q − S)). A set with s(S) = 0 is *forced*: by Lemma 1.1 every 4-factor contains
E(S_Q, P − S) and misses E(S_P, Q − S).

**Corollary 2.2 (rigidity criterion).** Let Ex be the set of edges in no 4-factor.
(i) e ∈ Ex iff e ∈ E(S_P, Q − S) for some forced S.
(ii) A balanced T is rigid iff (A) |E0(T) − Ex| ≤ 1, or (B) there is a set S with s(S) = 1 and
E0(T) − Ex ⊆ E(S_P, Q − S). The same holds with E1(T) in place of E0(T) (apply it to V − T, which is
rigid iff T is, since E0(V − T) = E1(T)).

*Proof.* (i) Theorem 2.1 with E0 = {e}: the maximum is 0 iff some π has Φ(π) = 0, i.e. every level is
forced and e is cut by one of them. Conversely, a forced S misses E(S_P, Q − S) in every 4-factor.
(ii) If (A) holds, |F ∩ E0| ≤ 1 for every F. If (B) holds, |F ∩ E0| = |F ∩ (E0 − Ex)| ≤
e_F(S_P, Q − S) ≤ s(S) = 1 by Lemma 1.1. Conversely, if T is rigid, Theorem 2.1 gives π with
Φ(π) ≤ 1. If every level is forced, at most one E0 edge is uncut and every cut one lies in Ex by (i):
(A). Otherwise exactly one level t has s(S_t) = 1 (a set repeated at two levels counts twice), the
others are forced and no E0 edge is uncut; an edge cut by a forced level lies in Ex, the others lie in
E(S_P, Q − S) for S = S_t: (B). ∎

## 3. Sets with slack at most 1 in a sparse E4 instance

**Lemma 3.1.** Let Y be a sparse E4 instance and 2 ≤ |S| ≤ n − 1. Write j = j(S), d_Q = D(S_Q),
d_P = D(S_P). Then s(S) ≤ 1 exactly in the following cases:

| Type | s | j | d_Q | d_P | g(S) | ∂_Q(S) | ∂_P(S) |
|---|---|---|---|---|---|---|---|
| F1 | 0 | 1 | 4 | any | 10 | 4 | 2 − d_P |
| F2 | 0 | 2 | 4 | 0 | 12 | 8 | 0 |
| U0 | 1 | 0 | 4 | any | 10 | 1 | 5 − d_P |
| U1 | 1 | 1 | 3 | any | 10 | 5 | 2 − d_P |
| U2 | 1 | 1 | 4 | any | 12 | 5 | 3 − d_P |
| U3 | 1 | 2 | 3 | 0 | 12 | 9 | 0 |
| U4 | 1 | 2 | 4 | ≤ 1 | 14 | 9 | 1 − d_P |

*Proof.* By Lemma 1.1, g/2 = s + j + d_Q, and (1.1) gives ∂_P(S) = s + d_Q − 2j − d_P ≥ 0, so
2j ≤ s + d_Q − d_P ≤ s + 4. Sparsity gives g/2 ≥ 5, so j ≥ 5 − s − d_Q ≥ 1 − s. For s = 0: j ∈ {1, 2};
j = 1 forces d_Q = 4 (g/2 = 1 + d_Q ≥ 5), so g = 10, ∂_P = 2 − d_P, ∂_Q = g/2 + 3j − d_Q = 4; j = 2
forces d_Q − d_P ≥ 4, so d_Q = 4, d_P = 0, g = 12, ∂_P = 0, ∂_Q = 8. For s = 1: j ∈ {0, 1, 2}; j = 0
forces d_Q = 4, g = 10, ∂_Q = 1, ∂_P = 5 − d_P; j = 1 forces d_Q ≥ 3, giving U1 (d_Q = 3, g = 10) or
U2 (d_Q = 4, g = 12), with ∂_P = d_Q − d_P − 1 and ∂_Q = g/2 + 3 − d_Q = 5 from (1.1); j = 2
forces d_Q − d_P ≥ 3 and d_Q ≥ 2, so (d_Q, d_P) ∈ {(3, 0), (4, 0), (4, 1)}, giving U3 and U4. Each row
satisfies s = g/2 − j − d_Q, so the list is exact. ∎

Complements follow from (1.2) with g(V) = 8: g(V − S) = 8 + 2∂(S) − g(S). For example an F1 set with
|V − S| ≥ 2 has g(V − S) = 10 − 2d_P ≥ 10, so d_P = 0, ∂_P(S) = 2, g(V − S) = 10. A U0 set with
|S| ≤ n − 2 is a (5,1) set (PAPER Prop 3).

## 4. A rigid set needs a tight 6-edge cut

**Proposition 4.1.** Let Y be a sparse E4 instance with a rigid set. Then Y has a set S with
g(S) = g(V − S) = 10 and |S|, |V − S| ≥ 3.

*Proof.* Trivial sets first: s(∅) = s(V) = 0; s({q}) = deg q − 4 and s({p}) = 4; s(V − p) = deg p − 4
and s(V − q) = 4; and ∂_P vanishes on {q}, V − p, ∅, V. So a set S with s(S) ≤ 1 and ∂_P(S) > 0 has
2 ≤ |S| ≤ n − 2 and appears in Lemma 3.1.

Case 1: Ex ≠ ∅. By Corollary 2.2(i) some forced S has ∂_P(S) > 0; by Lemma 3.1 it is an F1 set, and by
the remark after it d_P = 0 and g(S) = g(V − S) = 10. Both |S| = 2|S_P| + 1 and |V − S| are odd and at
least 2, hence at least 3.

Case 2: Y has a U0 set S. It is a (5,1) set, so g(S) = g(V − S) = 10 (PAPER Prop 3), and |S| ≥ 4: a
balanced 2-set with g = 10 is an edge pq with ∂_Q = deg q − 1 = 1, against δ ≥ 4. Likewise
|V − S| ≥ 4.

Case 3: Ex = ∅ and no U0 set. Let T be rigid. Corollary 2.2 for E0(T): (A) would make T thin
(∂_Q(T) ≤ 1), hence a (5,1) set (PAPER Prop 3), a U0 set (s(T) = ∂_Q(T) for balanced T); so (B) holds
with S of type U1-U4, and |E0(T)| ≤ ∂_P(S) ≤ 3. The same for E1(T) via V − T: |E1(T)| ≤ 3. So
∂(T) ≤ 6 and by (1.2) g(T) + g(V − T) ≤ 20, so g(T) = g(V − T) = 10 and ∂(T) = 6. If |T| = 2 then
T = {p, q} is an edge (g = 10) with ∂_Q(T) + ∂_P(T) = deg p + deg q − 2 = 6, so deg p = deg q = 4;
every edge at a degree-4 vertex is in every 4-factor, so c_F(T) = deg q − 1 = 3 for every F, and T is
not rigid. So |T| ≥ 4 and, by symmetry, |V − T| ≥ 4. ∎

## 5. Smallest counterexamples below 36 vertices

**Theorem 5.1.** Let X be a bipartite graph with Δ ≤ 6, e ≥ 3n − 4 and no pair, with n minimal and
then e minimal (so X is a sparse E4 or C1 instance with δ ≥ 4, PAPER Lemma 1). If X is of E4 type and
n < 36, then X has no rigid set. Moreover no edge of X lies outside every 4-factor and X has no (5,1)
set.

*Proof.* By Proposition 4.1 a rigid set gives S with g(S) = g(V − S) = 10 and both sides of size at
least 3. PAPER Proposition 5 (with the referee's fix |S| ≥ 3) and census L5 give each side a 4-core with
at least 18 vertices, so n ≥ 36. Cases 1 and 2 of the proof of Proposition 4.1 produce the same kind of
set S from an edge in no 4-factor and from a (5,1) set (a U0 set), which gives the last sentence. ∎

The bound 36 comes only from L5 (no pair-free bipartite graph with δ ≥ 4, Δ ≤ 6, e = 3n − 5 on at most
17 vertices). If L5 is extended to m vertices, Theorem 5.1 holds for n < 2(m + 1).

## 6. Lemma 2EC', the repair rule, and the structure below 23 vertices

**Lemma 2EC' (open).** A sparse E4 instance with no rigid set has a 4-factor with no cut of at most
2 edges (equivalently, a connected 4-edge-connected 4-factor).

Only a weaker form is needed below: 2EC' for smallest E4-type W1b counterexamples with n < 36, which
have no rigid set by Theorem 5.1.

### 6.1 Structure of bad sets below 23 vertices

**Lemma 6.1.** Let X be a smallest W1b counterexample of E4 type with n ≤ 22, and F a 4-factor of X.
(a) If T is bad for F, then |T| ≥ 8 and |V − T| ≥ 8, and the side A ∈ {T, V − T} with |A| ≤ 11
induces K_{4,4} − e (|A| = 8) or a pair-free 5 + 5 graph with 19, 20 or 21 edges (|A| = 10).
(b) F has at most one bad pair {T, V − T}.

*Proof.* (a) With H = X − F and h = deg − 4: Σ_{v∈T} h(v) = 2|T| − D(T) = 2e_H(T) + e_H(∂T), and
e_H(∂T) = ∂(T) − ∂_F(T) ≥ ∂(T) − 2 = g(T) − D(T) − 2 (since g = D + ∂ for every set). Hence
g(T) ≤ 2|T| + 2, and likewise g(V − T) ≤ 2|V − T| + 2. Let A be the smaller side; A is balanced and
|A| ≤ 11. |A| = 2 would need g(A) ≤ 6. If g(A) = 10 and |A| ≥ 3, PAPER Prop 5 (with |S| ≥ 3) and L5
give |A| ≥ 18. So g(A) ≥ 12, |A| ≥ 5, and |A| ∈ {6, 8, 10}. |A| = 6 needs e(A) = 18 − g(A)/2 ≥ 11 > 9.
|A| = 8 needs e(A) ≥ 15; K_{4,4} has a pair (PAPER Example 4), so X[A] = K_{4,4} − e. |A| = 10 needs
e(A) ≥ 19, and no 5 + 5 graph with ≥ 22 edges is pair-free (genbg + pairc, Appendix A: pair-free
counts 62, 24, 8, 0, 0, 0, 0 for e = 19, ..., 25). Then |V − A| ≥ |A| ≥ 8.
(b) If F is connected, its bad sets form a crossing family: for crossing bad T1, T2 the sets T1 ∩ T2,
T1 ∪ T2, T1 − T2, T2 − T1 are bad (submodularity and posimodularity of ∂_F, cuts even and ≥ 2). Two
crossing bad pairs would give four disjoint bad sets of ≥ 8 vertices each, so n ≥ 32. Two non-crossing
pairs give, after complementing, bad T1 ⊊ T2; then M = T2 − T1 is balanced with
∂_F(M) ≤ ∂_F(T1) + ∂_F(T2) ≤ 4 (posimodularity), so 2|M| − 2 ≤ e_F(M) ≤ (|M|/2)², which forces
|M| ≥ 8, and n ≥ 8 + 8 + 8. If F is disconnected, each component is 4-regular bipartite, so has ≥ 8
vertices; for n ≤ 22 there are exactly two, C1 and C2. A bad set T other than C1, C2 meets some Ci in a nonempty
proper subset, and then T ∩ Ci and Ci − T are bad sets of F (F[Ci] is connected), of ≥ 8 vertices each,
so n ≥ 24. ∎

So below 23 vertices the 4-factors of X split into classes by their unique bad pair (or none), and
2EC' asks that the classes do not cover everything.

### 6.2 The repair rule and Conjecture M*

Let F be a 4-factor with a bad set. An *atom* is a bad set T that contains no other bad set (in the
family of bad sets and their complements). Let e1, e2 be the F-edges across T (none if c_F(T) = 0),
D⁻ = D(F) − {e1, e2}, and let Z be a shortest directed cycle of D⁻ that uses an H-arc from T_Q to
P − T (PAPER Lemma 7(a); in D⁻ every arc across ∂T is an H-arc). Then F' = F Δ Z is a 4-factor and
c_{F'}(T) = c_F(T) + k, where k ≥ 1 is the number of times Z leaves T.

**Identity 6.2.** For a balanced U and any directed cycle Z of D(F), split Z into maximal runs inside
U; call a run FF (resp. HH) if Z enters and leaves it by F-arcs (resp. H-arcs). Then
c_{F Δ Z}(U) = c_F(U) + #HH − #FF.
*Proof.* c(U) = e_F(P − U, U_Q). An arc of Z enters U either as an F-arc into U_Q or as an H-arc into
U_P, and leaves U either as an F-arc from U_P or as an H-arc from U_Q. Reversing Z turns an F-arc into
U_Q into an H-edge (c drops by 1) and an H-arc out of U_Q into an F-edge (c rises by 1); the other two
kinds do not touch E(U_Q, P − U). Per run the change is [left by an H-arc] − [entered by an F-arc]:
−1 for FF, 0 for FH and HF, +1 for HH. ∎

**Conjecture M*.** With F, T, Z as above: every bad set of F' is bad for F, and
c_{F'}(W) ≥ c_F(W) for every bad set W of F'.

**Theorem 6.3.** Let Y be a sparse E4 instance with no rigid set. If M* holds, and for every 4-factor
with a bad set some atom admits a cycle Z as above, then Y has a 4-factor with no cut of ≤ 2 edges.

*Proof.* Put Φ(F) = Σ (2 − c_F(T)) over bad pairs {T, V − T}. M* gives Φ(F') ≤ Φ(F) − 1 (the term of
T drops by at least 1, no term appears, none grows). Φ is a nonnegative integer, so the rule reaches
Φ = 0. ∎

Evidence (rung (b), wave4/theory): M* had no violation in 2,727 tests (exp9: 1,000 at 4-factors along
the repair dynamics of 135 necklace instances; exp11: 1,727 at 4-factors reached by random
alternating-cycle walks in 204 necklace instances; n = 16 to 50), and no atom ever lacked a cycle Z.
exp8 ran the rule to the end on 362 necklace instances; Φ decreased at every step and every run
reached a 2-cut-free 4-factor. The rigid lane (wave4/rigid/RIGID.md, rounds 1-2, 1,187,256 sparse
instances or good-port instances with n = 11 to 31) found a 2-cut-free 4-factor in all 1,162,095
instances without a rigid set; there its swap dynamics (random and shortest cycles, random and
adversarial starts) always reached one within 10 swaps; every instance with a rigid set also had a
(5,1) set, and no two rigid sets crossed.

The shortest choice matters: FLAW.md F1 gives an explicit instance (n = 40) where a non-shortest cycle
of D⁻ through an E0 H-arc repairs T and creates a new bad set; in all 13 such cases found, the new set
U was disjoint from T, had ∂_F(U) = 4, and Z had one FF-run in U (Identity 6.2).

**Remark 6.4 (sparsity blocks the obvious counterexample to M*).** Let c_F(T) = 1. The natural way to
force the shortest cycle through an FF-run is a corridor: a balanced U ⊆ V − T with c_F(U) = 2 and a
set R1 ⊆ V − T − U, |R1| ≥ 2, such that every H-arc of E0(T) and every H-arc leaving U_Q ends in R1,
no H-arc leaves R1, and exactly two F-arcs leave R1 (e2 and one F-arc into U_Q), so the cycle must
cross U by F-arcs. This cannot happen in a sparse E4 instance. For every set R,
H-in(R) − H-out(R) = h(R_P) − h(R_Q) = D(R_Q) − D(R_P) − 2j(R). Here H-out(R1) = 0 and R1 receives the
E0(T) H-arcs, of which there are ∂_Q(T) − 1 = g(T)/2 − D(T_Q) − 1 ≥ 4 − D(T_Q), and the H-arcs leaving
U_Q, of which there are s(U) − 2 = g(U)/2 − D(U_Q) − 2 ≥ 3 − D(U_Q). So, as R1_Q, T_Q and U_Q are
disjoint subsets of Q, 2j(R1) ≤ D(R1_Q) + D(T_Q) + D(U_Q) − 7 ≤ D(Q) − 7 = −3, while
g(R1) = 2(s(R1) + j(R1) + D(R1_Q)) with s(R1) = 2 and g(R1) ≥ 10 needs D(R1_Q) ≥ 3 − j(R1) ≥ 5 > 4.

### 6.2a One-crossing repair below 23 vertices (proved)

**Proposition 6.6.** Let X be a smallest W1b counterexample of E4 type with n ≤ 22, F a 4-factor of X
with bad pair {T, V − T}, e1, e2 the F-edges across ∂T (if any), and D⁻ = D(F) − {e1, e2}. Suppose D⁻
has a directed cycle with exactly one arc leaving T and one arc entering T (a *one-crossing cycle*;
the arcs are an H-arc a from T_Q to P − T and an H-arc b from Q − T to T_P). Let Z be a shortest
one-crossing cycle and F' = F Δ Z. Then c_{F'}(T) = c_F(T) + 1 and every bad set of F' is T or
V − T. In particular, if c_F(T) = 1 then F' has no cut of at most 2 edges.

*Proof.* Z uses no F-arc across ∂T, and reversing it turns a into an F-edge from T_Q to P − T, so
c_{F'}(T) = c_F(T) + 1. Suppose F' has a bad set W with {W, V − W} ≠ {T, V − T}. By Lemma 6.1(b) for F',
{W, V − W} is the only bad pair of F', so T is not bad for F': c_F(T) = 1 and ∂_{F'}(T) = 4.

W does not cross T. If F' is connected, ∂_{F'}(W ∩ T) + ∂_{F'}(W ∪ T) ≤ ∂_{F'}(W) + ∂_{F'}(T) ≤ 6 with
both terms even and at least 2, so one of W ∩ T, W ∪ T is bad for F', and for crossing W, T neither is
W or V − W: a second bad pair. If F' is disconnected, its two components form its only bad pair
{W, V − W} (proof of Lemma 6.1(b)), and the same inequality with ∂_{F'}(W) = 0 gives a bad set strictly
inside a component.

So, after replacing W by V − W, W ⊊ R for R ∈ {T, V − T}. Put M = R − W. Lemma 6.1(a) for F' and for F
gives |W| ≥ 8 and |V − R| ≥ 8, so M is balanced with 2 ≤ |M| ≤ 6. By posimodularity,
∂_{F'}(M) ≤ ∂_{F'}(R) + ∂_{F'}(W) ≤ 6, so e_{F'}(M) = 2|M| − ∂_{F'}(M)/2 ≥ 2|M| − 3; with |M| = 2t and
e_{F'}(M) ≤ t², either t = 1 (F'[M] is one edge) or t = 3 (F'[M] = K_{3,3}), and ∂_{F'}(M) = 6 in both
cases. From ∂(R) = ∂(W) + ∂(M) − 2e(W, M): e_{F'}(W, M) = 1 + ∂_{F'}(W)/2, so at least
6 − 2 = 4 F'-edges join M to V − R; as only ∂_{F'}(R) = 4 edges cross ∂R, all four F'-edges across ∂T
(namely e1, e2, a, b) have their R-end in M.

Let x ∈ M_P and y ∈ M_Q be the R-ends of the two arcs of Z across ∂T (x = head of b and y = tail of a
if R = T; x = head of a and y = tail of b if R = V − T). The part of Z inside R is a directed path σ
from x to y in D⁻[R], and σ is a shortest x-y path in D⁻[R]: replacing σ by a shorter path inside R
gives a shorter one-crossing cycle. Since F'[M] is an edge or K_{3,3}, xy ∈ F'. If xy ∈ F, then xy ∉ Z
and x → y is an arc of D⁻[R] (xy is not e1 or e2), so σ = (x → y) and xy ∈ Z: contradiction. If
xy ∉ F, then xy ∈ Z as the H-arc y → x; but the arc of Z leaving y is the arc across ∂T. ∎

So for n ≤ 22, 2EC' for X reduces to the existence of one-crossing cycles:

**Lemma B (open).** In the setting of Proposition 6.6, D⁻ has a one-crossing cycle.

In this setting every 4-factor F of X is connected: otherwise its smaller component has 8 or 10
vertices and is K_{4,4} or K_{5,5} minus a perfect matching (the only 4-regular bipartite graphs on 4 + 4
and 5 + 5 vertices), both Hamilton-decomposable, which is a pair. (K_{4,4}: PAPER Example 4. For
K_{5,5} minus {p_i q_i}, indices mod 5: the edges p_i q_{i±1} form the Hamilton cycle
p_0 q_1 p_2 q_3 p_4 q_0 p_1 q_2 p_3 q_4, and the edges p_i q_{i±2} form the Hamilton cycle
p_0 q_2 p_4 q_1 p_3 q_0 p_2 q_4 p_1 q_3.) So c_F(T) = 1, and given Lemma B one application of
Proposition 6.6 gives a 4-factor of X with no cut of at most 2 edges; H22 then gives a pair. Hence **Lemma B implies that no smallest W1b counterexample of E4 type has n ≤ 22.**

Evidence for Lemma B and for the one-crossing rule in general (exp12, sparse E4 necklace instances with
n = 16 to 50, which are not smallest counterexamples): at all 1,388 atoms of 4-factors reached by random
alternating-cycle walks in 199 instances, D⁻ had a one-crossing cycle, and the shortest one-crossing
repair created no new bad set and lowered no c (Conjecture M*_1 below held every time).

Partial proof of Lemma B: if the smaller side A of the bad pair is K_{4,4} − e, then F[A] = X[A] (15
edges), D(F)[A] has only F-arcs, and from every P-vertex of A an F-arc reaches every Q-vertex of A except
for the one missing pair (u, w). Let a cycle of D⁻ through an E0 H-arc cross ∂T 2k ≥ 4 times, and write
it as Z = a_1 π_1 b_1 σ_1 a_2 π_2 b_2 σ_2 ⋯ a_k π_k b_k σ_k, where a_i are the arcs leaving T (H-arcs
from T_Q to P − T), b_i the arcs entering T (H-arcs from Q − T to T_P), π_i the paths in V − T from
head(a_i) to tail(b_i), and σ_i the paths in T from head(b_i) to tail(a_{i+1}) (indices mod k). Among the
passages of Z through A at most one starts at u, so for some i a single F-arc inside A closes a cycle
that crosses ∂T exactly twice: if A = T, the arc head(b_i) → tail(a_i) closes a_i π_i b_i; if A = V − T,
the arc head(a_{i+1}) → tail(b_i) closes b_i σ_i a_{i+1}. So a cycle of D⁻ through an E0 H-arc yields a
one-crossing cycle when A is K_{4,4} − e. Open here: the 5 + 5 case, and the case that no cycle of D⁻
uses an E0 H-arc (PAPER Lemma 7(b)).

**Conjecture M*_1 (general n).** In a sparse E4 instance with no rigid set, for every 4-factor F and
every atom T of F, D⁻ has a one-crossing cycle, and a shortest one creates no new bad set and lowers no c.
By the potential of Theorem 6.3, M*_1 implies 2EC'. Proposition 6.6 is the case n ≤ 22 of the second
half, for smallest counterexamples.

### 6.3 Consequences

**Corollary 6.5.** If 2EC' holds for smallest W1b counterexamples of E4 type with n ≤ 22, then there is
no such counterexample: by Theorem 5.1 it has no rigid set, so it has a 4-factor F with no cut of ≤ 2
edges, and H22 (SCOUT §2.3; one method at n = 22, two for n ≤ 20) makes F Hamilton-decomposable, which
is a pair. With F2 (n ≤ 18), a smallest bipartite W1 counterexample on at most 22 vertices would then be
of C1 type with n ∈ {19, 21}. With a census H_M in place of H22 the same holds for E4 types with
n ≤ min(M, 34). For what this gives for B6 see `N.md`.

## 7. C1 type: the port-deleted instance

Let X be a smallest W1b counterexample of C1 type: classes U (s vertices, D(U) = 1, the vertex u1 of
degree 5) and W (s + 1 vertices, D(W) = 7), sparse, δ ≥ 4 (PAPER Lemma 1). A *port* is a W-vertex of
degree 4 or 5. By C1-PAPER Lemma 4.4 the ports y for which X − y has no 4-factor carry deficiency at
most 2, so good ports exist. The pair would come from a 4-factor of Y = X − y with no cut of ≤ 2 edges
(H_{n−1} for n − 1 ≤ 22). Put Q := U, P := W − y.

**Lemma 7.1.** (i) D_Y(Q) = D_Y(P) = 1 + deg y =: d ∈ {5, 6}, so g(V(Y)) = 2d. (ii) g(S) ≥ 10 for every
S ⊆ V(Y) with |S| ≥ 2. (iii) For every nonempty S ⊊ V(Y),
g(S) ≥ 4 + 2|N(y) ∩ S| = 4 + 2D_Y(S_Q) − 2[u1 ∈ S], hence s(S) ≥ 2 − [u1 ∈ S] − j(S).

*Proof.* (i) Removing y lowers the degrees of its deg y neighbors in U and removes y's deficiency
6 − deg y from W. (ii) Y[S] = X[S] and X is sparse. (iii) g_X(S + y) = g(S) + 6 − 2|N(y) ∩ S| ≥ 10,
and D_Y(q) = [q ∈ N(y)] + [q = u1] on U; then use Lemma 1.1. ∎

**Corollary 7.2 (thin sets at a port).** If T ⊆ V(Y) is balanced with ∂_Q(T) ≤ 1, then u1 ∈ T,
∂_Q(T) = 1, D_Y(T_Q) ≥ 4 and g_X(T + y) = 10. (Thin on the P side is the same statement for V(Y) − T.)
If moreover n ≤ 21, no port has a thin set.

*Proof.* For balanced T, s(T) = ∂_Q(T), so Lemma 7.1(iii) forces u1 ∈ T and equality, i.e.
g_X(T + y) = 10; g(T) = 2D_Y(T_Q) + 2 ≥ 10. If n ≤ 21, PAPER Prop 5 and L5 give |T + y| ≥ 18, so
|V(Y) − T| ≤ 2: V(Y) − T = {p, q} and ∂_Q(T) = deg_Y(p) − [pq ∈ E] ≥ 3. ∎

**Lemma 7.3 (forced sets at a port, n ≤ 21).** Let n ≤ 21 and S ⊆ V(Y) with s(S) = 0 and
∂_P(S) ≥ 1 (so S excludes an edge). Then u1 ∈ S, j(S) = 2, D_Y(S_Q) ≥ 5, and both S and V(Y) − S have
at least 10 vertices; in particular n = 21. So for n = 19 no edge of Y is excluded.

*Proof.* Lemma 7.1(iii) gives j ≥ 2 − [u1 ∈ S] (s = 0), and ∂_P(S) = D(S_Q) − D(S_P) − 2j ≥ 1 (from
(1.1)) gives D(S_Q) ≥ 2j + 1. If u1 ∈ S and j = 1, then g_X(S + y) = 2j + 6 + 2 = 10, so |S| ≥ 17 and
R = V(Y) − S has 1 or 3 vertices with one more P- than Q-vertex; |R| = 1 gives ∂_P(S) = 0, and
R = {p1, p2, q} gives ∂_Q(S) = 4j = 4 < (deg p1 − 1) + (deg p2 − 1). If u1 ∉ S, then j ≥ 2 and
D(S_Q) ≥ 5, while u1 ∈ R gives D(S_Q) ≤ d − 1; so d = 6, D(S_Q) = 5, D(S_P) = 0, j = 2 and
N(y) ⊆ S (D_Y(S_Q) = |N(y) ∩ S| when u1 ∉ S, and deg y = 5). Then g(S) = 2(j + D(S_Q)) = 14 =
4 + 2|N(y) ∩ S|, equality in (iii), so g_X(S + y) = 10 and |S| ≥ 17; R has two more P- than Q-vertices
and contains u1, so |R| ≥ 4 and |V(Y)| ≥ 21 > n − 1. If u1 ∈ S and j = 2: g(S) = 2(2 + D(S_Q)) ∈
{14, 16} and S has two more Q- than P-vertices; with t = |S_P|, e(S) = 3|S| − g(S)/2 ≥ 6t − 2 and
e(S) ≤ t(t + 2) give t = 0 or t ≥ 4, and t = 0 would make S two Q-vertices with g = 12. So |S| ≥ 10.
By (1.2) applied in Y, g(R) = g(V(Y)) + 2∂(S) − g(S) = 2d + 2j − 2D(S_P) ≤ 16, and R has two more P-
than Q-vertices; with r = |R_Q| the same count gives r = 0 or r ≥ 4, and r = 0 would give
∂_P(S) = e(S_P, R_Q) = 0. So |R| ≥ 10 and n − 1 ≥ 20. j ≥ 3 would need D(S_Q) ≥ 7 > d. ∎

What the C1 type still needs: (1) the remaining forced case of Lemma 7.3 at n = 21; (2) the sets with
s = 1 at a port, which can have ∂_P up to 5 (u1 ∈ S, j = 1, D(S_Q) = 6, D(S_P) = 0), so the E4 bound
|E0(T)| ≤ 3 of Proposition 4.1 does not transfer and a rigid-set exclusion at ports needs a new
argument (one may also choose the port); (3) 2EC' for Y, where a component without a cut of ≤ 2 edges
suffices; (4) H_{n−1}. The rigid lane found no rigid set at 975,700 good ports (RIGID.md §3).

## 8. The Hamilton-decomposition statement needed for all n

For n ≤ 22 the HD step is the census H22. For larger n, Theorem 5.1 and 2EC' give a connected
4-edge-connected 4-factor F of X, and what is missing is

**(HD-OP).** A connected bipartite 4-regular graph with no cut of 2 edges and no non-trivial one-passage
4-edge cut is Hamilton-decomposable. (A one-passage 4-edge cut is a set W with |W|, |V − W| ≥ 2 and
||W_P| − |W_Q|| = 1, so ∂_F(W) = 4 with all four edges at the larger class of W; every Hamilton cycle
crosses it exactly twice.)

Why one-passage cuts must be excluded: the 350-vertex Meredith-type graph (K_{4,3} blocks on a
non-Hamiltonian 3-connected cubic bipartite graph with a doubled perfect matching; construction and
argument in `reports/585-plan/report.html`, not re-checked here) is 4-connected, bipartite, 4-regular
and not Hamiltonian; each block is a one-passage 4-cut. Status of (HD-OP): true for n ≤ 22 (implied
by H22, which needs only "no 2-edge cut"); no counterexample known; not tested beyond 22 vertices. In our setting one-passage cuts of F are not forced: a forced one would
be an F1 set (Lemma 3.1), which has g = 10 on both sides and so needs n ≥ 36 in X. So the full route
for n < 36 needs 2EC'' = 2EC' plus "no one-passage 4-cut except at single vertices" for some 4-factor,
and (HD-OP). Whether (HD-OP) is plausible is open; a census of 4-edge-connected bipartite 4-regular
graphs without non-trivial one-passage cuts at 24-26 vertices (H24 costs an estimated 50-100 core-h)
would be the first test.

## 9. Sources

- `reports/585-next/wave3/pairs/PAPER.md` (frozen 6fad9b43…): Lemma 1 (§2), Lemma 2, Prop 3 (§3), Example 4
  (R20), Prop 5 and Cor 6 (§4), Lemma 7 and Remark (§5); identity (1) in §1.
- `reports/585-next/wave3/pairs/REVIEW.md`: verdicts (ACCEPT WITH FIXES; fix F1 = Prop 5 needs |S| ≥ 3).
- `reports/585-next/wave3/pairs/SCOUT.md`: §2.3 H22, §2.4 L5, §4 the exact gap.
- `reports/585-next/G110/C1-PAPER.md`: Identities 1.1-1.3, Lemma 1.4 (flow criterion), Lemma 4.4 (bad ports).
- `reports/585-next/wave4/rigid/RIGID.md` (draft, rounds 1-2): instance families and counts quoted in
  §6.2, §7.
- `reports/585-plan/report.html`: the 350-vertex Meredith-type graph of §8.

## Appendix A. Computer checks

All files are in `wave4/theory/`. Python is `~/.cache/erdos585/venv/bin/python` (networkx, pysat);
genbg is nauty 2.9.3; `pairc` is `reports/585-fable/tools/pairc` (exact pair test over all vertex
subsets).

- `check_lp.py <seed> 8 6`, seeds 11-14 (outputs `check_lp_1{1..4}.out`, re-run identically as
  `check_lp_s3_1{1..4}.out`): Corollary 2.2 against min-cost flow on every balanced T of 24 two-block
  graphs with n = 16 (two copies of K_{4,4} − e joined by two edges, plus 1-6 random extra edges):
  308,832 sets, 20 rigid, 0 mismatches; max_F |F ∩ E0| also equals brute force over all 4-factors (SAT
  enumeration) on every T; Lemma 1.1's identity on random S and F.
- `classify.c`: every S with 2 ≤ |S| ≤ n − 1 and s(S) ≤ 1 (Gray code over all subsets) in all 52,557
  sparse E4 instances with a = 6, 7, 8 (`wave3/pairs/data/e4_a{6,7,8}_sparse.g6`): all of a type in
  Lemma 3.1 (F1 38,802; F2 8,732; U2 132,624; U3 60,140; U4 60,140; no U0, U1 at these sizes). R20 and
  10 block instances at n = 20: all predicted.
- `check_identities.py 7 40` (`check_identities_s3.out`): Identity 6.2, the H-balance of Remark 6.4,
  the arc balance with Lemma 1.1, (1.1) and (1.2), each checked 24,000 times on 40 random sparse E4
  instances (random 4-factors, random directed cycles of D(F), random sets): 0 failures.
- 5 + 5 census for Lemma 6.1(a) (`final_checks.sh`, `census55.out`): `genbg -q 5 5 e:e | pairc f`
  gives 125, 62, 24, 8, 0, 0, 0, 0 pair-free graphs for e = 18, ..., 25 (130, 69, 34, 16, 6, 3, 1, 1
  graphs in all).
- Repair experiments on necklace instances (n = 16 to 50, sparse by the flow test of `tools.py`):
  exp7 (`exp7_*.log`, 115 sparse K_{5,5} necklaces built in `exp7.py`: no rigid set, all with a
  2-cut-free 4-factor); the rest use `gen2.py`: exp8 (`exp8_*.log`, 362 instances: the
  atom-plus-shortest-cycle rule reached a 2-cut-free 4-factor in all, Φ decreasing at every step); exp9 (`exp9_*.log`, 135 instances: 1,000 shortest-cycle
  repairs with no new bad set; 13 of 3,996 random-cycle repairs created one); exp10 (`exp10_*.txt`, the
  profile of those failures); exp11 (`exp11_3{1..6}.log`, 204 instances, 1,727 repairs at 4-factors
  reached by random alternating-cycle walks: no violation of M*); exp12 (`exp12_4{1..6}.log`, 199
  instances, 1,388 atoms: a one-crossing cycle at every atom, no violation of M*_1).
- FLAW.md F1: `find_randfail.py 77 230` found `randfail.txt`; `verify_randfail.py` (networkx only)
  confirms it.
- B6 at N = 20 (for `N.md`): `genbg -q -d6:6 -D6:6 10 10 60:60` gives 121,790 graphs, `pairc f` finds a
  pair in each (`run_b6_20.sh`, `b6_20_part_*.err`).
