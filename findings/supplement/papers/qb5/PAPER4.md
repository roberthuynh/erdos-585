# QB(5), round 4: KL1 holds for every 2-block, hence QB(5)

Author lane qb5, round 4, October 5, 2026. Status: frozen for independent review (SHA-256 in
`FROZEN4.sha256`). Not reviewed. This is rung 1 of the round-4 ladder: a proof of the Key Lemma KL1 of
PAPER3, which by the refereed reduction of PAPER3 (REVIEW3: "KL1 implies QB(5) is a complete reduction")
proves QB(5). No Lean, no `check.sh`, so nothing here is a project-oracle PASS. Rungs: (a) for Theorem 3.1
(KL1) and its lemmas; (a) with a computed finite lemma (PAPER3 Lemma 4.1: two author programs and the referee's own program, with two enumerations)
for Theorem 4.1 (QB(5)); (b) for the checks of §5.

PAPER.md, PAPER2.md and PAPER3.md (frozen: `FROZEN.sha256`, `FROZEN2.sha256`, `FROZEN3.sha256`) are cited by
section and number. Their referee reports REVIEW.md, REVIEW2.md and REVIEW3.md are FINAL with no mathematical
error; the fixes they require are in force (§1.1).

## 0. Results at a glance

QB(5): every finite simple bipartite graph with maximum degree at most 6, n ≥ 3 vertices and at least
3n − 5 edges contains a nonempty 4-regular subgraph.

| Item | Statement | Verdict | Where |
|---|---|---|---|
| Lemmas 2.1, 2.2 | the function θ: identities, supermodularity with a crossing bonus, values and bounds | proved | §2 |
| Lemma 3.2 | merging lemma: two maximal overloaded sets are disjoint, meet in one vertex a with m(a) ≥ 2, or meet in a set with θ* = 2 | proved | §3 |
| Lemma 3.3 | a minimal cover of A by maximal overloaded sets has two members sharing at least 3 vertices | proved | §3 |
| Lemmas 3.4, 3.5 | the shared part K is a hub: every big member contains it, the rest are petals with a boundary budget | proved | §3 |
| **Theorem 3.1** | **KL1: for every 2-block and every 4-set M of cut edges covering L_A, I_X(M) ≠ ∅** | **proved** | §3 |
| **Theorem 4.1** | **QB(5)** | **proved, with PAPER3 Lemma 4.1 (computed)** | §4 |
| §5 | every lemma of §3 checked on 1,753 blocks and all 165,610 multisets m; the proof's structure predicted exactly on the 9,612 multisets that miss an in-degree-3 vertex | computed | §5 |

**Where a referee should attack first.**
1. Lemma 3.3: the identity (3.1), the bound at a shared vertex, and the equality case m(v) = 3.
2. Lemma 3.4(c): a big member meeting the hub in a single vertex.
3. Lemma 3.5(a): that two big members meet in exactly K⁺ as subsets of X.
4. The count in the proof of Theorem 3.1: that the list of petals is complete and the (2/3)-bound holds for
   each, and the final vertex count.
5. That Theorem 3.1 is exactly PAPER3's KL1 (§1.2) and that PAPER3 Corollary 4.3(b) then gives QB(5).

Where the idea comes from (not used in any proof). Join a new vertex z to each a ∈ A by m(a) parallel edges.
X + z has sides C ∪ {z} and A, |A| = |C ∪ {z}| + 1, deficiency 2 on the small side (all at z, of degree 4) and
w(A) = 8 on the large side: it is a C2 instance in the sense of PAPER.md §1, except that it may have parallel
edges at z and may fail sparsity at sets z + S with S tight and containing every end of M. A vertex p ∈ A is in
I_X(M) iff X + z − p has a 4-factor (PAPER3 Theorem 2.1 and PAPER2 Theorem 2.2), so KL1 is the statement of
PAPER.md Theorem 5.1(iii)/(iv) ("some W-vertex not adjacent to u0 is good") for X + z. The proof below
redoes the hub-and-petals count of PAPER.md §5 (iv) in a language where parallel edges and the sparsity
defects cost nothing.

## 1. Setting

### 1.1 Corrections in force

F1 to F7 (REVIEW.md §2), as listed in PAPER2 §1.3; G1 to G3 (REVIEW2.md §2), as listed in PAPER3 §1.2;
H1 (REVIEW3.md §2: the planted search of PAPER3 §6.2 and A.5 had 1,600 starts, not about 1,300) and the
optional items of REVIEW3.md §2, of which one is used: PAPER3 Corollary 4.3(b) reads "both blocks of some
2-block decomposition of every minimal counterexample". This paper uses PAPER.md Identities 1.2 (with the
coefficient of F1; only the g-form is used) and 1.3, Lemma 2.1, Theorem 7.1; PAPER2 (B1), (B2) of §1.2;
PAPER3 §1.1, Theorem 2.1, §5.1, Lemma 4.1, Theorem 4.2, Corollary 4.3.

### 1.2 Hypotheses

G is a sparse E5 instance without a 4-factor with a fixed 2-block decomposition (PAPER3 §1.1). Let X = A ∪ C
be one of its 2-blocks (for Y read D, B for A, C). Then:

(H1) |A| = |C| + 2 ≥ 6; every c ∈ C has exactly 6 neighbors, all in A;
(H2) g(S) := 6|S| − 2e(S) ≥ 12 for every S ⊆ X with |S| ≥ 3 (S is a proper subset of V(G); for S = X,
     g(X) = 12);
(H3) for a ∈ A, d_a := deg_X(a) ≥ 3 (PAPER2 (B1)); δ_a := 6 − d_a ∈ {0, 1, 2, 3}; Σ_A δ = 6|A| − 6|C| = 12.

M is a 4-set of cut edges and m(a) the number of its edges at a ∈ A, so m(A) = 4 and m(a) ≤ c_a ≤ δ_a
(δ_a = c_a + def(a), PAPER3 §1.1). M **covers** L_A = {a : d_a = 3} if m(a) ≥ 1 on L_A. Put
w(a) := δ_a − m(a) and U := {a : m(a) ≥ 1}. Then w(A) = 12 − 4 = 8, w ≥ 0, and if M covers L_A then
w(a) ≤ 2 for every a (PAPER3 §5.1). Theorem 3.1 uses only (H1) to (H3), m(A) = 4, 0 ≤ m ≤ δ, and w ≤ 2.

PAPER3's notation (§1.1): dem_X(A1) = 4|A1| − Σ_c min(4, e(c, A1)); A1 is under-supplied if
m(A1) < dem_X(A1); I_X(M) is the intersection of all under-supplied sets; T ⊆ A is overloaded if A − T is
under-supplied, i.e. θ(T) := m(T) − ρ(T) ≥ 1 with ρ(T) = 4|T| − 4 − Σ_c (e(c, T) − 2)^+; and
I_X(M) = A − ⋃{T : T overloaded}.

**KL1 (PAPER3 §0).** If M covers L_A, then I_X(M) ≠ ∅.

## 2. The function θ on subsets of X

For S ⊆ X: S_A = S ∩ A, S_C = S ∩ C, κ(S) = |S_A| − |S_C|, e(S) the number of edges inside S,
∂_A(S) = e(S_A, C − S_C), ∂_C(S) = e(S_C, A − S_A), h(S) = w(S_A) + ∂_A(S) ≥ 0, and

    θ(S) := m(S_A) + 4 − κ(S) − g(S)/2.

**Lemma 2.1.** For all S, S' ⊆ X and c ∈ C − S:
(a) θ(S) = 4 + 2κ(S) − h(S);
(b) θ(S) = m(S_A) + 4 − 4κ(S) − ∂_C(S);
(c) θ(S ∪ S') + θ(S ∩ S') = θ(S) + θ(S') + e(S − S', S' − S);
(d) θ(S + c) = θ(S) + e(c, S_A) − 2.

*Proof.* (a) e(S) = Σ_{a∈S_A} d_a − ∂_A(S) = 6|S_A| − δ(S_A) − ∂_A(S), so g(S)/2 = 3|S| − e(S) =
−3κ(S) + δ(S_A) + ∂_A(S); substitute and use δ − m = w. (b) Every c has all 6 neighbors in A, so
e(S) = 6|S_C| − ∂_C(S) and g(S)/2 = 3κ(S) + ∂_C(S). (c) m and κ are modular, and
g(S ∪ S') + g(S ∩ S') = g(S) + g(S') − 2e(S − S', S' − S) (PAPER.md Identity 1.2). (d) κ drops by 1 and g
grows by 6 − 2e(c, S_A) (PAPER.md Identity 1.3). ∎

For T ⊆ A put θ*(T) := max{θ(S) : S_A = T}. By Lemma 2.1(d) the maximum is attained at
X'(T) := T ∪ C'(T), C'(T) = {c : e(c, T) ≥ 3}, and θ*(T) = m(T) + 4 − 4|T| + Σ_c (e(c, T) − 2)^+, which is
PAPER3's θ(T). So **T is overloaded iff θ*(T) ≥ 1, and I_X(M) = A − ⋃{T : θ*(T) ≥ 1}.** From Lemma 2.1(c)
with S = X'(T), S' = X'(T'):

    θ*(T ∪ T') + θ*(T ∩ T') ≥ θ*(T) + θ*(T') + e(X'(T) − X'(T'), X'(T') − X'(T)).        (2.1)

**Lemma 2.2.**
(a) θ(∅) = 4; θ*({a}) = m(a); θ*(T) = m(T) − 4 ≤ 0 if |T| = 2.
(b) If S ⊆ X and |S| ≥ 3, then θ(S) ≤ m(S_A) − 2 − κ(S) and 3θ(S) ≤ 2m(S_A) − w(S_A) − ∂_A(S), each with
    equality iff g(S) = 12; and θ(S) ≤ 2.
(c) If |T| ≥ 3 and θ*(T) ≥ 1, then C'(T) ≠ ∅ (so |X'(T)| ≥ 4) and −1 ≤ κ(X'(T)) ≤ m(T) − 3; in particular
    m(T) ≥ 2. The same bounds on κ hold for every S with |S| ≥ 3 and θ(S) ≥ 1.
(d) For a ∈ A and J ⊆ C: θ({a} ∪ J) = m(a) − 2|J| + e(a, J) ≤ m(a) − |J|.

*Proof.* (a) g(∅) = 0. If |T| ≤ 2 no c has 3 neighbors in T, so θ*(T) = m(T) + 4 − 4|T|.
(b) The first inequality is (H2). By Lemma 2.1(a), 2κ(S) = θ(S) − 4 + h(S); inserting this into the first
gives 3θ(S) ≤ 2m(S_A) − h(S). Also θ ≤ 4 + 2κ, so θ ≤ 2 if κ ≤ −1, and θ ≤ m(S_A) − 2 ≤ 2 if κ ≥ 0.
(c) If C'(T) = ∅ then θ*(T) = m(T) + 4 − 4|T| < 1. For S with θ(S) ≥ 1: (b) gives κ ≤ m − 3 and Lemma
2.1(a) gives 2κ ≥ θ − 4 ≥ −3. (d) κ = 1 − |J| and g = 6 + 6|J| − 2e(a, J); e(a, J) ≤ |J|. ∎

## 3. Proof of KL1

**Theorem 3.1 (KL1).** Under §1.2, if M covers L_A then some vertex of A lies in no overloaded set, that is,
I_X(M) ≠ ∅.

**Lemma 3.2 (merging).** Let T, T' ⊆ A be overloaded with θ*(T ∪ T') ≤ 0, and S = X'(T), S' = X'(T'). Then
θ(S ∩ S') ≥ θ*(T) + θ*(T') + e(S − S', S' − S) ≥ 2, and one of the following holds:
(N0) T ∩ T' = ∅;
(N1) T ∩ T' = {a}, m(a) ≥ θ*(T) + θ*(T') ≥ 2, and |C'(T) ∩ C'(T')| ≤ m(a) − 2;
(N3) |T ∩ T'| ≥ 3, θ*(T ∩ T') = 2 and θ*(T) = θ*(T') = 1.

*Proof.* Lemma 2.1(c) and θ(S ∪ S') ≤ θ*(T ∪ T') ≤ 0 give the first claim. Since (S ∩ S')_A = T ∩ T',
θ*(T ∩ T') ≥ 2, so |T ∩ T'| ≠ 2 (Lemma 2.2(a)). If |T ∩ T'| ≥ 3, Lemma 2.2(b) gives θ*(T ∩ T') ≤ 2, which
forces (N3). If T ∩ T' = {a}, then S ∩ S' = {a} ∪ J with J = C'(T) ∩ C'(T'), and Lemma 2.2(a), (d) give
m(a) ≥ θ(S ∩ S') ≥ θ*(T) + θ*(T') and m(a) − |J| ≥ 2. ∎

**Setup for the proof of Theorem 3.1.** Suppose M covers L_A and every vertex of A lies in an overloaded set
(for u ∈ U, {u} is overloaded by Lemma 2.2(a)). Let 𝒯 be the family of inclusion-maximal overloaded sets.
It covers A, and two distinct members T, T' satisfy θ*(T ∪ T') ≤ 0 (T ∪ T' strictly contains T), so Lemma 3.2
applies to every pair. Fix a subfamily 𝒯' ⊆ 𝒯 that covers A and is minimal with this property; every member
has a *private* vertex, in no other member. By Lemma 2.2(a) a member is *big* (|T| ≥ 3) or a *singleton* {u}
with u ∈ U; a singleton member lies in no other overloaded set. Since |U| ≤ 4 < |A|, 𝒯' has a big member.

**Lemma 3.3.** Two members of 𝒯' share at least 3 vertices.

*Proof.* Suppose not. By Lemma 3.2, two members are disjoint or share exactly one vertex v, and then
m(v) ≥ 2. Let mult(v) be the number of members containing v and H = {v : mult(v) ≥ 2}. For v ∈ H the members
containing v are big (a singleton {v} would lie in another member) and pairwise meet exactly in {v}. Since
Σ_A (2m − w) = 8 − 8 = 0,

    Σ_{T∈𝒯'} (2m(T) − w(T)) = Σ_{v∈A} (2m(v) − w(v)) mult(v) = Σ_{v∈H} (2m(v) − w(v)) (mult(v) − 1).    (3.1)

Lower bounds on the left: for a big member, Lemma 2.2(b) with S = X'(T) gives
2m(T) − w(T) ≥ 3θ*(T) + ∂_A(X'(T)) ≥ 3 + ∂_A(X'(T)); for a singleton, 2m(u) − w(u) = 3m(u) − δ_u ≥ 0.
Fix v ∈ H with members T_1, ..., T_k (k = mult(v)). ∂_A(X'(T_i)) ≥ e(v, C − C'(T_i)) = d_v − e(v, C'(T_i)).
A neighbor c of v lies in at most two of the C'(T_i) (three would give c at least 3 neighbors in each of three
sets that pairwise share only v, at least 7 neighbors), and in two only if m(v) = 3 (Lemma 3.2(N1)). With
p_v the number of neighbors of v lying in two of them (p_v = 0 if m(v) = 2, p_v ≤ d_v if m(v) = 3),
Σ_i ∂_A(X'(T_i)) ≥ (k − 1)d_v − p_v. Edges at different vertices of H are different, so (3.1) gives

    3·#big + Σ_singletons (3m(u) − δ_u) + Σ_{v∈H} [(mult(v) − 1)d_v − p_v] ≤ Σ_{v∈H} (2m(v) − w(v))(mult(v) − 1).

Since d_v = 6 − m(v) − w(v), 2m(v) − w(v) − d_v = 3m(v) − 6, and

    3·#big + Σ_singletons (3m(u) − δ_u) ≤ Σ_{v∈H, m(v)=3} [3(mult(v) − 1) + p_v].                      (3.2)

If no v ∈ H has m(v) = 3, the right side is 0 and the left side is at least 3. Otherwise let m(v) = 3: then
δ_v = 3, d_v = 3, w(v) = 0 and U = {v, b} with m(b) = 1. Every big member has m ≥ 2 (Lemma 2.2(c)), so it
contains v; thus #big = mult(v) =: k and H = {v}. (3.2) gives 3k ≤ 3(k − 1) + p_v, so p_v = 3 = d_v and every
inequality used is an equality. In particular 2m(T) − w(T) = 3θ*(T) + ∂_A(X'(T)) for every big member, so
X'(T) is tight (Lemma 2.2(b)), and then 12 ≤ g(X'(T) − v) = 6 + 2e(v, C'(T)) (PAPER.md Identity 1.3;
|X'(T) − v| ≥ 3) puts all three neighbors of v into C'(T). As p_v > 0 there are two big members T, T', both
containing v, so |C'(T) ∩ C'(T')| ≥ 3 > m(v) − 2, against Lemma 3.2(N1). ∎

**Lemma 3.4 (hub).** Let T_1, T_2 ∈ 𝒯' share at least 3 vertices and put K := T_1 ∩ T_2 and
K⁺ := K ∪ {c ∈ C : e(c, K) ≥ 2}. Then:
(a) θ*(K) = 2, no set strictly containing K has θ* ≥ 2, and m(K) ≥ 3;
(b) θ(K⁺) = 2, and either
    (β) κ(K⁺) = −1, w(K) = 0, ∂_A(K⁺) = 0, and ∂(K⁺) = m(K) + 6; or
    (δ) κ(K⁺) = 0, m(K) = 4, g(K⁺) = 12, and ∂(K⁺) = 8 − w(K),
    where ∂(K⁺) = ∂_A(K⁺) + ∂_C(K⁺) is the number of edges leaving K⁺;
(c) every big member of 𝒯' contains K, every big member T has θ*(T) = 1, and two big members meet exactly in K;
(d) every other member is a singleton {u} with u ∉ K and m(u) = 1; there is at most one, and none if m(K) = 4.

*Proof.* (a) θ*(K) = 2 by Lemma 3.2(N3). Let K* ⊇ K be inclusion-maximal with θ*(K*) ≥ 2. Since
|T_1 ∩ K*| ≥ 3, θ*(T_1 ∩ K*) ≤ 2 and (2.1) gives θ*(T_1 ∪ K*) ≥ 1 + 2 − 2 = 1, so T_1 ∪ K* is overloaded
and equals T_1 by maximality: K* ⊆ T_1. Likewise K* ⊆ T_2, so K* = K. By Lemma 2.2(b), 2 ≤ m(K) − 2 − κ and
by Lemma 2.1(a), 2 ≤ 4 + 2κ, for κ = κ(X'(K)); so m(K) ≥ 3.
(b) θ(K⁺) = θ*(K) by Lemma 2.1(d), since the added C-vertices have e(c, K) = 2. |K⁺| ≥ 3. Lemma 2.2(b) gives
κ(K⁺) ≤ m(K) − 4 ≤ 0 and Lemma 2.1(a) gives h(K⁺) = 2 + 2κ(K⁺) ≥ 0, so κ(K⁺) ∈ {−1, 0}. If κ(K⁺) = −1 then
h(K⁺) = 0, that is w(K) = 0 and ∂_A(K⁺) = 0. If κ(K⁺) = 0 then m(K) = 4 and g(K⁺) = 12 (equality in Lemma
2.2(b)), and ∂_A(K⁺) = h(K⁺) − w(K) = 2 − w(K). In both cases Lemma 2.1(b) gives
∂_C(K⁺) = m(K) + 2 − 4κ(K⁺).
(c) Let T be a big member; m(T) ≥ 2 (Lemma 2.2(c)). If T ∩ K = ∅ then m(T) ≤ 4 − m(K) ≤ 1, impossible. If
|T ∩ K| ≥ 2 then θ*(T ∩ K) ≤ 2 (Lemma 2.2(a), (b)) and (2.1) gives θ*(T ∪ K) ≥ 1, so K ⊆ T by maximality.
Suppose T ∩ K = {a}. T ∪ K strictly contains T, so θ*(T ∪ K) ≤ 0 and (2.1) gives m(a) = θ*({a}) ≥ 3: m(a) = 3,
d_a = 3. All neighbors of a lie in K⁺_C: in case (β) because ∂_A(K⁺) = 0; in case (δ) because K⁺ is tight and
|K⁺ − a| ≥ 3, so 12 ≤ g(K⁺ − a) = 6 + 2e(a, K⁺_C). Lemma 2.1(c) for X'(T) and K⁺ gives
θ(X'(T) ∩ K⁺) ≥ θ*(T) + θ(K⁺) − θ*(T ∪ K) ≥ 3; as X'(T) ∩ K⁺ = {a} ∪ J with J = C'(T) ∩ K⁺_C, Lemma
2.2(d) gives J = ∅. So a has no neighbor in C'(T), and 12 ≤ g(X'(T) − a) = g(X'(T)) − 6 (|X'(T)| ≥ 4), while
by the definition of θ and Lemma 2.2(c), g(X'(T)) = 2(m(T) + 4 − κ(X'(T)) − θ*(T)) ≤ 2(4 + 4 + 1 − 1) = 16.
This contradiction shows K ⊆ T. Two big members T, T' both contain K, so (N3) holds for them: θ*(T) = 1, and
T ∩ T' ⊇ K has θ* = 2, so T ∩ T' = K by (a).
(d) A member that is not big is a singleton {u} with m(u) ≥ 1, and u lies in no big member, so u ∉ K. Since
m(K) ≥ 3 and m(A) = 4, there is at most one such u, with m(u) = 1, and none if m(K) = 4. ∎

**Lemma 3.5 (petals).** In the setting of Lemma 3.4 let T_1, ..., T_r (r ≥ 2) be the big members of 𝒯', and
S_i := X'(T_i) ∪ K⁺, P_i := S_i − K⁺, Q_i := T_i − K = (P_i)_A, E_i := e(K⁺, P_i). Then:
(a) θ(S_i) = 1, the sets P_i are pairwise disjoint, and Q_i ≠ ∅;
(b) θ(P_i) = 3 − E_i and Σ_i E_i ≤ ∂(K⁺);
(c) w(K) + w(Q_i) ≤ 3 + 2κ(S_i) and −1 ≤ κ(S_i) ≤ m(T_i) − 3;
(d) if |P_i| ≥ 3 then E_i ≥ 5 − m(Q_i) + κ(P_i); if |P_i| ≤ 2 then P_i = {y} with E_i = 3 − m(y), or
    P_i = {y, c} with E_i = 5 − m(y) − e(y, c), or P_i = {y, y'} with E_i = 7 − m(y) − m(y').

*Proof.* (a) Every c ∈ K⁺_C − C'(T_i) has e(c, T_i) ≤ 2 and e(c, T_i) ≥ e(c, K) ≥ 2, so by Lemma 2.1(d)
θ(S_i) = θ*(T_i) = 1 (Lemma 3.4(c)). For i ≠ j, θ(S_i ∪ S_j) ≤ θ*(T_i ∪ T_j) ≤ 0, so θ(S_i ∩ S_j) ≥ 2 by
Lemma 2.1(c). S_i ∩ S_j has A-part K and contains K⁺; every further C-vertex c has e(c, K) ≤ 1 and by Lemma
2.1(d) lowers θ below θ(K⁺) = 2. So S_i ∩ S_j = K⁺. Q_i contains the private vertex of T_i.
(b) K⁺ ∩ P_i = ∅, so Lemma 2.1(c) gives 1 = θ(S_i) = θ(K⁺) + θ(P_i) + E_i − θ(∅) = θ(P_i) + E_i − 2. The P_i
are disjoint and outside K⁺, so the E_i count different edges leaving K⁺.
(c) Lemma 2.1(a) gives h(S_i) = 3 + 2κ(S_i), and h(S_i) ≥ w(T_i) = w(K) + w(Q_i). The bounds on κ are Lemma
2.2(c) for S_i (|S_i| ≥ 3, θ(S_i) = 1).
(d) For |P_i| ≥ 3 use θ(P_i) ≤ m(Q_i) − 2 − κ(P_i) (Lemma 2.2(b)) in (b). For |P_i| ≤ 2 (Q_i ≠ ∅):
θ({y}) = m(y), θ({y, c}) = m(y) − 2 + e(y, c), θ({y, y'}) = m(y) + m(y') − 4. ∎

*Proof of Theorem 3.1.* Suppose KL1 fails. By Lemma 3.3 two members of 𝒯' share at least 3 vertices; take
the setting of Lemmas 3.4 and 3.5. A is the disjoint union of K, Q_1, ..., Q_r and the singleton members
(Lemma 3.4(c), (d)), so

    8 = w(A) = w(K) + Σ_i w(Q_i) + w(singleton members).                                              (3.3)

*Case (β):* κ(K⁺) = −1 and w(K) = 0. Then κ(P_i) = κ(S_i) + 1 ∈ [0, m(T_i) − 2], so κ(P_i) ≤ 2, and
w(Q_i) ≤ 1 + 2κ(P_i) by Lemma 3.5(c). We claim w(Q_i) ≤ (2/3)(E_i + m(Q_i)) for every petal, except that a
petal with |P_i| ≥ 3 and κ(P_i) = 2 may exceed this by 1/3:
- P_i = {y}: w(y) ≤ 2 (M covers L_A) and E_i + m(y) = 3;
- P_i = {y, c}: κ(P_i) = 0, so w(y) ≤ 1, while E_i + m(y) ≥ 4;
- P_i = {y, y'}: w(Q_i) ≤ 4 and E_i + m(Q_i) = 7;
- |P_i| ≥ 3: E_i + m(Q_i) ≥ 5 + κ(P_i), and 1 + 2κ ≤ (2/3)(5 + κ) for κ ≤ 1, while 5 = (2/3)·7 + 1/3.
Summing, with Σ E_i ≤ m(K) + 6 (Lemmas 3.4(b), 3.5(b)) and Σ m(Q_i) = 4 − m(K) − m(singletons):

    Σ_i w(Q_i) ≤ (2/3)(10 − m(singletons)) + n_2/3,

where n_2 counts the petals with |P_i| ≥ 3 and κ(P_i) = 2.
If there is no singleton member, (3.3) gives 8 ≤ 20/3 + n_2/3, so n_2 ≥ 4; each such petal has
E_i ≥ 7 − m(Q_i), so Σ E_i ≥ 28 − 1 > 10 ≥ m(K) + 6. Contradiction.
If there is a singleton member {u}, then m(u) = 1, m(K) = 3, every m(Q_i) = 0, so κ(P_i) ≤ 1 and n_2 = 0; and
w(u) ≤ 2. (3.3) gives 6 ≤ 8 − w(u) = Σ_i w(Q_i) ≤ 6. So every inequality is tight: Σ E_i = 9 and every
petal satisfies w(Q_i) = (2/3)E_i, which among the four cases (with κ(P_i) ≤ 1 and m(Q_i) = 0) only
P_i = {y} with w(y) = 2 does. So r = 3, the petals are single vertices y_1, y_2, y_3, and
A = K ∪ {y_1, y_2, y_3, u}. As κ(K⁺) = −1, |K⁺_C| = |K| + 1, so C − K⁺_C has |C| − |K| − 1 = |A| − 3 − |K| = 1
vertex c_0. Its six neighbors avoid K (∂_A(K⁺) = 0), so they lie in {y_1, y_2, y_3, u}. Contradiction.

*Case (δ):* κ(K⁺) = 0 and m(K) = 4. There is no singleton member, every m(Q_i) = 0, and by Lemma 3.5(c)
κ(P_i) = κ(S_i) ∈ {−1, 0, 1} and w(Q_i) ≤ 3 + 2κ(P_i) − w(K). Every petal has w(Q_i) < E_i: for {y},
w(y) ≤ 2 < 3 = E_i; for {y, c}, w(y) ≤ 2 < 4 ≤ E_i; {y, y'} has κ = 2 and does not occur; for |P_i| ≥ 3,
w(Q_i) ≤ 3 + 2κ(P_i) < 5 + κ(P_i) ≤ E_i. With (3.3) and Lemma 3.4(b):
8 − w(K) = Σ_i w(Q_i) < Σ_i E_i ≤ 8 − w(K). Contradiction. ∎

Where the hypothesis that M covers L_A is used: only through w ≤ 2 for the single-vertex petals {y} (both
cases) and the pair petals {y, y'} (case (β)); Lemmas 3.2 to 3.5 do not use it, and the singleton member has
w(u) ≤ 3 − m(u) ≤ 2 anyway. Without it the conclusion fails (PAPER3 §6.1); §5 shows that every failure then
has exactly the shape where the proof uses it.

Theorem 3.1 supersedes PAPER3 Propositions 5.2 and 5.3 and the referee observation of REVIEW3 §6 (s = 3).

## 4. QB(5)

**Theorem 4.1.** QB(5) holds: every finite simple bipartite graph with maximum degree at most 6, n ≥ 3
vertices and at least 3n − 5 edges contains a nonempty 4-regular subgraph.

*Proof.* Let G be a counterexample with n minimal, then e minimal. By PAPER.md Lemma 2.1 and Theorem 7.1, G is
a sparse E5 instance without a 4-factor, with a 2-block decomposition X = A ∪ C, Y = B ∪ D (PAPER.md Theorem
6.1), in which no G − p − q has a 4-factor. Each block satisfies §1.2 for every 4-set M of cut edges (PAPER3
§1.1, PAPER2 (B1), (B2)), so Theorem 3.1 gives KL1 for X and for Y. PAPER3 Theorem 4.2 (with the refined
covering Lemma 4.1, computed) then gives p ∈ A, q ∈ D with a 4-factor in G − p − q, which is a nonempty
4-regular subgraph of G. This is PAPER3 Corollary 4.3(b) with the wording fix of §1.1. ∎

What the proof rests on: PAPER.md (Theorems 5.1, 6.1, 7.1; REVIEW.md FINAL), PAPER2 Theorem 2.2 and
Corollary 2.3 (REVIEW2.md FINAL), PAPER3 Theorems 2.1, 4.2 and Lemma 3.4 (REVIEW3.md FINAL), the finite Lemma
4.1 of PAPER3 (checked by `code/refined_cover.py`, `code/refined_cover2.c` and by REVIEW3's own program
(`review3/code/lemma41.c`, two enumerations: 142 classes and 22,792 matrices), 0 failures), and Theorem 3.1 here (not yet refereed).

## 5. Computations

`code/r4/merge_check.c` (new, C, shares no code with earlier rounds; built with `/usr/bin/clang -O3`) reads
blocks as lines "na nc mask_1 ... mask_nc" and, for every multiset m on A with m(A) = 4 and
m(a) ≤ min(3, δ_a), covering L_A or not, computes θ*(T) for all T ⊆ A (θ*(T) = m(T) + 4 − 4|T| +
Σ_c (e(c, T) − 2)^+), the maximal overloaded sets (by a superset closure) and the maximal sets with θ* ≥ 2,
and checks: F1 the values of Lemma 2.2(a), (b) (θ* ≤ 2 on |T| ≥ 3); F2 Lemma 3.2 on every pair of maximal
overloaded sets; F3 Lemma 3.4(a), (c) on every pair sharing at least 3 vertices; F4 KL1 for covering m; F5
for every m with I_X(M) = ∅ (possible only when m misses L_A), over all minimal subcovers by maximal
overloaded sets: none has pairwise intersections of size at most 1 (Lemma 3.3 does not use covering), and
each has a pair sharing at least 3 vertices and a one-vertex petal y with w(y) = 3 (a place where the proof
of Theorem 3.1 uses covering).

| Input | Result (`code/r4/merge_check.out`) |
|---|---|
| `code/r4/blocks_r4.txt`: the 1,750 blocks of PAPER3 A.3 (REVIEW3's file `review3/data/blocks1750_all.blk`), REVIEW3's two SAT blocks with case (b) (`review3/data/caseb_sat.blk`, \|X\| = 20, 22) and the PAPER3 §6.1 block (`code/example_b.py`): 1,753 blocks | 165,610 multisets (89,438 covering); pairs of maximal overloaded sets: 332,806 disjoint, 9,612 sharing ≥ 3 vertices, none sharing 1 or 2; F1 to F4: 0 violations; I_X(M) = ∅ for 9,612 non-covering m and 0 covering m; F5: 9,612 minimal subcovers, 0 hub-free, 0 without a weight-3 one-vertex petal. Run time 1 s |

The data do not exercise (N1) (no two maximal overloaded sets share exactly one vertex in any of these
blocks), so Lemma 3.3's multiplicity cases rest on the proof alone. Compute this round: under 2
core-minutes.

## Appendix A. Sources (paths relative to the repository root)

- `reports/585-next/wave4/qb5/PAPER.md` (frozen): §1 (g, Identities 1.2, 1.3), Lemma 2.1, §5 (Theorem 5.1,
  proof of (iv): the model for §3), Theorem 6.1, Theorem 7.1.
- `reports/585-next/wave4/qb5/PAPER2.md` (frozen): §1.2 (B1), (B2), §1.3 (F1 to F7), Theorem 2.2, Corollary 2.3.
- `reports/585-next/wave4/qb5/PAPER3.md` (frozen): §0 (KL1), §1.1, §1.2 (G1 to G3), Theorem 2.1, Lemma 4.1,
  Theorem 4.2, Corollary 4.3, §5.1, §6.1.
- `reports/585-next/wave4/qb5/REVIEW.md`, `REVIEW2.md`, `REVIEW3.md` (FINAL): fixes F1 to F7, G1 to G3, H1,
  REVIEW3 optional items and §6.
- `reports/585-next/wave4/qb5/review3/data/blocks1750_all.blk`, `review3/data/caseb_sat.blk` (data only).
