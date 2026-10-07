# REVIEW4: QB(5) round 4, KL1 for every 2-block, hence QB(5) (wave4/qb5/PAPER4.md)

Independent adversarial referee, October 5, 2026. Status: FINAL.
Object: `PAPER4.md` as frozen in `FROZEN4.sha256` (`shasum -a 256 -c FROZEN4.sha256`: all 16 entries OK at the
start and at the end of this review). Working files, log and code: `review4/` (`review4/LOG.md`, `review4/code/`,
`review4/data/`). Nothing here is a project-oracle PASS: no Lean, no `check.sh`.

Method. Every step of PAPER4 §2 to §4 was re-derived by hand, and so were the cited steps of PAPER.md, PAPER2.md
and PAPER3.md that lie on the QB(5) path (the interfaces in full; PAPER.md Theorem 5.1(iii), (iv) again). All
computations were redone with code written from scratch in `review4/code/`. Nothing in `qb5/code/` was run,
imported or read; the author's block list `code/r4/blocks_r4.txt` was only compared, as a list, with my own
assembly of the same inputs (identical, in order). The PAPER3 §6.1 block was rebuilt from the text of PAPER3.
Compute used: about 20 core-minutes, at most 2 processes at a time.

## 1. Verdicts (FINAL)

| Claim | Verdict | Short reason |
|---|---|---|
| §0, the X + z heuristic ("KL1 is PAPER.md Theorem 5.1(iii)/(iv) for X + z") | **not used; correct as a remark, one omission** (optional J2) | No step of §2 to §4 applies Theorem 5.1 to X + z: §3 is a direct proof from (H1) to (H3). Theorem 5.1 would *not* apply literally (§3.1 below). The equivalence p ∈ I_X(M) iff X + z − p has a 4-factor holds on all 4,912 sampled triples (own max flow). |
| Lemma 2.1 (identities for θ) | ACCEPT | (a) to (d) re-derived; also asserted on random S, S' in every block I ran (0 failures). |
| Lemma 2.2 (values and bounds of θ, θ*) | ACCEPT | Re-derived. θ* ≤ 2 on \|T\| ≥ 3, C'(T) ≠ ∅, −1 ≤ κ(X'(T)) ≤ m(T) − 3 and both equality cases asserted for every big overloaded T met (0 failures). |
| **Lemma 3.2** (merging: N0, N1 or N3) | **ACCEPT** | Re-derived. I characterized (N1) completely (§3.2): it forces m(a) = 3, θ* = (1, 1), m(T) = 3, m(T') = 4, κ = (−1, −1), C'(T) ∩ C'(T') = {c*} with a ~ c*. Built 397 sparse blocks with an (N1) pair (\|A\| = 15 to 19), and the search below found 4,909 more: every one has exactly this shape. |
| **Lemma 3.3** (a minimal cover has two members sharing ≥ 3) | **ACCEPT** | The weight identity (3.1), the bound at a shared vertex (a neighbor of v in at most two C'(T_i), in two only if m(v) = 3) and the m(v) = 3 equality case (all big X'(T) tight, then \|C'(T) ∩ C'(T')\| ≥ 3 > 1) re-derived. Covering is not used. 0 hub-free covering families in 80.5 million multisets. |
| **Lemma 3.4** (the hub K) | **ACCEPT** | (a) to (d) re-derived, including (c) for T ∩ K = {a} (m(a) = 3, all of N(a) in K⁺_C, J = ∅, then g(X'(T)) ≥ 18 > 16). Note: (c) and (d) hold for the whole family of maximal overloaded sets, not only for 𝒯'; checked in that form. |
| **Lemma 3.5** (petals) | **ACCEPT** | Re-derived, including S_i ∩ S_j = K⁺ in (a). The shapes {y, c} and {y, y'} of (d) cannot occur (§3.4), so the list is a harmless superset. |
| **Theorem 3.1 (KL1)** | **ACCEPT** | Both cases re-derived: (β) the (2/3)-bound per petal, the n_2 ≥ 4 contradiction, the singleton case down to the vertex c_0 with six neighbors in four vertices; (δ) w(Q_i) < E_i per petal against Σ E_i ≤ 8 − w(K). Covering is used only through w(y) ≤ 2 at single-vertex petals. No counterexample: 0 covering m with I_X(M) = ∅ in 66.2 million covering multisets, 717,812 of them with a hub. |
| **Theorem 4.1 (QB(5))** | **ACCEPT** | The chain of §5 is complete. It uses no census input and not the n ≥ 40 bound. Its one computed input, PAPER3 Lemma 4.1, re-verified by my own program (0 failures). |
| §5 computations | **ACCEPT WITH FIX** (J1) | Every count of `code/r4/merge_check.out` reproduced exactly by own code. But §0 line 27 says "every lemma of §3 checked"; F1 to F5 do not test Lemma 3.5 or Lemma 3.4(b), (d), and in these 1,753 blocks no hub ever occurs under a covering m, so the count of Theorem 3.1 is never exercised by the author's data. |

No REJECT. I found no mathematical error. **KL1 holds for every 2-block of every sparse E5 instance without a
4-factor, and with PAPER, PAPER2 and PAPER3 as refereed, QB(5) is proved** (written proof with one computed finite
lemma; rung (a) with a computed lemma, not a Lean result).

## 2. Fixes, with locations

Required (wording only; the mathematics is unaffected):
- **J1** (§0 table, line 27; and §5, lines 283-292). "every lemma of §3 checked on 1,753 blocks" overstates
  F1 to F5: they test Lemma 2.2(a), (b), Lemma 3.2, Lemma 3.4(a), (c), KL1, and Lemma 3.3 through F5 on the
  9,612 non-covering failures; Lemma 3.5 and Lemma 3.4(b), (d) are not tested, and no hub occurs under a covering
  m in these blocks (own count: 0 of 9,612 hub multisets are covering), so the covering half of the count in
  Theorem 3.1 has no data behind it. Say which lemmas F1 to F5 test, or cite this review's checks (§4), which
  exercise every lemma of §3, the hub under covering m (both cases), big petals, singleton members and (N1).

Optional, editorial:
- **J2** (§0, lines 39-41). X + z fails sparsity not only at z + S with S tight and containing every end of M,
  but also at {z, a, c} with m(a) = 3 and c ∈ N(a) (three parallel z-a edges plus ac, so g = 18 − 8 = 10); 156
  such sets in my sample (§4). Also,
  M covers L_A exactly when X + z has minimum degree at least 4, which is where the analogy with Theorem 5.1
  (δ ≥ 4 from sparsity) breaks for non-covering M. Nothing depends on this paragraph.
- **J3** (lines 211, 234-235, 253, 257-259). Petals P_i = {y, c} and P_i = {y, y'} cannot occur (§3.4), so the
  sentence on where covering is used reduces to the single-vertex petals {y} (in case (δ) the {y, c} bullet's
  w(y) ≤ 2 would in any case follow from Lemma 3.5(c): w(y) ≤ 3 − w(K) < 4).
- **J4** (lines 298-300). "(N1) is not exercised": it is now (§4), and §3.2 shows that an (N1) pair forces
  \|I_X(M)\| ≥ 4 directly, so Lemma 3.3's multiplicity cases do not rest on the proof alone.

## 3. Proof notes (re-derivation, adversarial points)

### 3.1 The "above all" question: does PAPER.md Theorem 5.1 still apply to X + z?

It does not need to. PAPER4 never applies Theorem 5.1 to X + z: §0 marks the construction "not used in any
proof", and §2 and §3 work on X only, from (H1) to (H3), m(A) = 4, 0 ≤ m ≤ δ and w ≤ 2. Theorem 5.1 enters only
through PAPER.md Theorem 7.1, for the C2 case of a minimal counterexample, on the simple sparse graph G itself.

Had PAPER4 cited Theorem 5.1 for X + z, that would be a gap. X + z has parallel z-a edges whenever some m(a) ≥ 2,
and it fails sparsity (i) at z + S with S tight and m(S_A) = 4 (including S = {a, a'} with m(a) + m(a') = 4) and
(ii) at {z, a, c} with m(a) = 3, a ~ c. The proof of Theorem 5.1 uses sparsity at every petal (PAPER.md Lemma 3.2,
\|Q\| ≥ 3 ⇒ g(Q) ≥ 12), Fact F and δ ≥ 4, and "neighbor" counts at u0 that parallel edges change. For non-covering M
the uncovered L-vertex has degree 3 in X + z, and KL1 really fails there (9,612 data cases), which shows the
hypotheses are not cosmetic. §3 of PAPER4 redoes the hub-and-petal count with θ, where none of this matters; I
checked that every inequality in §2 and §3 is derived from (H1) to (H3) and the M-bounds alone.

### 3.2 Lemma 3.2 and the one-vertex case (N1): complete description

For a big overloaded T and a ∈ T, g(X'(T) − a) ≥ 12 and g(X'(T)) = 2(m(T) + 4 − κ − θ*) give
e(a, C'(T)) ≥ 5 − m(T) + κ(X'(T)) + θ*(T). Let T ∩ T' = {a} with T, T' maximal, J = C'(T) ∩ C'(T'). Then
e(a, C'(T)) + e(a, C'(T')) ≤ d_a + e(a, J), θ*(T) + θ*(T') ≤ m(a) − 2\|J\| + e(a, J), and h(X'(T)) = 4 + 2κ − θ*
bounds the neighbors of a outside C'(T). Case analysis:
- m(a) = 2: J = ∅ and the bounds force κ = κ' = −1, θ* = 1, m(T) + m(T') = 6, then h = 1 forces m(T), m(T') ≥ 4.
  Impossible.
- m(a) = 3 (d_a = 3, U = {a, b}): if b lies in neither set, both T − a and T' − a are saturated and c* would
  need 3 + 3 + 1 > 6 neighbors; if a ≁ c* or J = ∅, the outside budgets h = 1, 1 cannot hold three neighbors
  of a; (κ, κ') = (0, −1) fails the h-budget of T'; (−1, 0) again needs deg c* ≥ 7.
What remains is rigid: m(a) = 3, b ∈ T' only, θ* = (1, 1), κ(X'(T)) = κ(X'(T')) = −1, J = {c*} with a ~ c*,
N(a) = {c*, c1, c2} with c1 ∈ C'(T) − c*, c2 ∈ C'(T') − c*, T − a saturated into C'(T), T' − a saturated into
C'(T') except deg_X(b) = 5, and c* has exactly 3 neighbors in T − a and 2 in T' − a.
Consequence: a third big maximal set would contain a (it needs m ≥ 2) and meet T and T' only in a (two shared
vertices are excluded by Lemma 3.2, three or more would give a hub K that every big maximal set contains, Lemma
3.4(c), while T ∩ T' = {a}), so it would be in (N1) pairs with both, hence contain b, which already lies in T'. As a
and b lie in T ∪ T', there is no singleton member either. So the maximal family is {T, T'}, and
\|C\| ≥ \|C'(T) ∪ C'(T')\| = \|T\| + \|T'\| + 1 gives \|A − T − T'\| ≥ 4. **Every M with an (N1) pair has
\|I_X(M)\| ≥ 4.** This agrees with Lemma 3.3 and confirms it independently on the configurations the data lacked.
Degree counts at c* and in C'(T), C'(T') force \|T − a\|, \|T' − a\| ≥ 5, so an (N1) pair needs \|A\| ≥ 15
(\|X\| ≥ 28); the data blocks have \|X\| ≤ 22, which is why the author never saw one. The shape does occur in sparse
blocks: §4.

### 3.3 Lemmas 3.3 and 3.4

- (3.1): Σ_T (2m(T) − w(T)) = Σ_v (2m(v) − w(v)) mult(v), and Σ_A (2m − w) = 0. Big member: Lemma 2.2(b) on
  X'(T); singleton: 3m(u) − δ_u ≥ 0. At v ∈ H: Σ_i e(v, C'(T_i)) ≤ d_v + p_v, so
  Σ_i ∂_A(X'(T_i)) ≥ (k − 1)d_v − p_v; with 2m − w − d = 3m − 6 this is (3.2). m(v) = 2 gives right side 0.
  m(v) = 3: every big member contains v, H = {v}, p_v ≥ 3 + Σ_sing forces equality everywhere, so each X'(T) is
  tight, N(v) ⊆ C'(T) for every big T, and two big members give \|C'(T) ∩ C'(T')\| ≥ 3 > m(v) − 2. Correct.
- Lemma 3.4(a): K* maximal with θ* ≥ 2 above K lies in T_1 and T_2 by (2.1). m(K) ≥ 3 from θ = 2 ≤ m − 2 − κ and
  κ ≥ −1. (b): κ(K⁺) ∈ {−1, 0} from Lemma 2.2(b) and h ≥ 0; ∂_C(K⁺) = m(K) + 2 − 4κ. (c) T ∩ K = {a}:
  θ*({a}) ≥ 1 + 2 − 0 = 3, so m(a) = 3, d_a = 3; N(a) ⊆ K⁺_C (β: ∂_A = 0; δ: tightness, \|K⁺\| ≥ 6);
  θ(X'(T) ∩ K⁺) ≥ 3 forces J = ∅; then g(X'(T)) ≥ 18 against ≤ 16. Correct. The argument never uses that T is a
  member of 𝒯', only that it is a big maximal overloaded set; I checked (c), (d) in that stronger form.

### 3.4 Lemma 3.5 and the count of Theorem 3.1

- (a): c ∈ K⁺_C − C'(T_i) has e(c, T_i) = 2, so θ(S_i) = θ*(T_i) = 1; extra C-vertices of S_i ∩ S_j have
  e(c, K) ≤ 1 and each lowers θ below 2, so S_i ∩ S_j = K⁺. (b): Lemma 2.1(c) for the disjoint K⁺, P_i.
- Petal shapes. A C-vertex c of P_i lies in C'(T_i) with e(c, K) ≤ 1, so e(c, Q_i) ≥ 2 and \|Q_i\| ≥ 2: no
  P_i = {y, c}. For y ∈ Q_i, θ*(K + y) ≥ m(y) − 2 + e(y, K⁺_C) and Lemma 3.4(a) give e(y, K⁺_C) ≤ 3 − m(y); a
  petal {y, y'} would need E_i = 7 − m(y) − m(y') > 6 − m(y) − m(y'): impossible. In case (β) a petal's C-vertices
  have no neighbor in K (∂_A(K⁺) = 0). So petals are {y} or have \|P_i\| ≥ 3 (J3).
- Case (β): κ(P_i) = κ(S_i) + 1 ∈ [0, m(T_i) − 2], w(Q_i) ≤ 1 + 2κ(P_i); per petal
  3w(Q_i) ≤ 2(E_i + m(Q_i)) (+1 if \|P_i\| ≥ 3, κ(P_i) = 2). No singleton: 24 ≤ 20 + n_2, so n_2 ≥ 4 and
  Σ E_i ≥ 27 > 10. Singleton u: m(K) = 3, all m(Q_i) = 0, n_2 = 0, Σ w(Q_i) = 6 forces r = 3 petals {y} with
  w = 2, and the unique c_0 ∉ K⁺_C (\|C\| = \|K\| + 2, \|K⁺_C\| = \|K\| + 1) has its 6 neighbors in
  {y_1, y_2, y_3, u}. Correct.
- Case (δ): m(Q_i) = 0, κ(P_i) ≤ 1, w(Q_i) < E_i for {y} (2 < 3) and for \|P_i\| ≥ 3 (3 + 2κ < 5 + κ), against
  Σ w(Q_i) = 8 − w(K) = ∂(K⁺) ≥ Σ E_i. Correct.
- Theorem 3.1 is exactly PAPER3's KL1: same L_A = {d_a = 3}, same I_X(M), M any 4-set of cut edges covering L_A,
  hypotheses (H1) to (H3) true for both blocks of every 2-block decomposition (sparsity of G on X ⊊ V, PAPER2
  (B1), Σδ = 6\|A\| − 6\|C\| = 12, \|A\| ≥ 6 from PAPER.md Theorem 6.1).

## 4. Computations (own code, `review4/code/`)

| Check | Code and input | Result |
|---|---|---|
| Author's data, redone | `kl1rev.c` (block validation incl. sparsity in the form Σ_c (e(c,T) − 3)^+ ≤ 3\|T\| − 6 for \|T\| ≥ 3; all m; θ*, maximal sets, I_X; Lemmas 2.1 (random S), 2.2(b)(c), 3.2, 3.3 (hub-free family never covers; all minimal subcovers), 3.4, 3.5 on the whole maximal family, per-petal bounds of Thm 3.1, KL1) on the 1,750 + 2 + 1 blocks (`data/data1753.blk`, §6.1 block rebuilt from PAPER3's text; list identical to `code/r4/blocks_r4.txt`) | 165,610 multisets (89,438 covering); pairs 332,806 disjoint, 0 one-vertex, 0 two-vertex, 9,612 sharing ≥ 3; I_X empty: 0 covering, 9,612 non-covering, each with exactly one minimal subcover, never hub-free, always with a one-vertex petal of weight 3. Every number equals `merge_check.out`. 0 violations. **0 of the 9,612 hubs are under a covering m** (J1) |
| (N1), planted | `gen_n1.py` (the rigid shape of §3.2, random completion), sizes \|A\| = 15 to 19 | 520 blocks, 397 block-sparse; 397 (N1) pairs, all of the predicted shape, I_X = A − T − T' (4 vertices or more), 0 violations |
| Hubs under covering m, planted | `gen_hub.py` (K⁺ = K_{4,5}, K_{5,6} − 3 edges, K_{5,5} − 1 edge, single-vertex petals), \|A\| = 11 to 13 | 1,909 blocks, 1,806 sparse; 3,704 covering hub multisets (β 3,108, δ 596), 8,556 petals {y}; covering hubs with a singleton member: 2,198; 0 violations, I_X never empty |
| Big petal | `gen_big.py` (K_{4,5} hub, a {y} petal and a tight κ = 0 petal K_{5,5} − e, E = 5), \|A\| = 16 to 18 | 300 blocks, 300 petals with \|P_i\| = 10 under covering m; 0 violations |
| Search for a KL1 counterexample | `sa_kl1.c` (simulated annealing on blocks, energy 10·min over covering m of \|I_X\| minus coverage by big overloaded sets; 45 runs × 300,000 moves from planted and data starts), every visited block with a covering hub, an (N1) pair or I_X = ∅ dumped and re-checked by `kl1rev` | 717,372 distinct blocks (\|A\| = 12, 13, 15), 79.9 million multisets (65.6 million covering); 713,808 covering hub multisets (β 713,666, δ 142), 1,428,811 petals {y}; 4,909 (N1) pairs, all of the predicted shape; 54,759 non-covering m with I_X = ∅, all with a weight-3 one-vertex petal; **0 covering m with I_X = ∅**; 0 violations of any check |
| §0 heuristic | `zcheck.py` (own Edmonds-Karp; I_X by brute force over A1 ⊆ A − p) on 151 blocks | p ∈ I_X(M) iff X + z − p has a 4-factor: 4,912 triples, 0 disagreements; small sparsity failures of X + z: 106 of type z + S, S "tight" with every end, 156 of type {z, a, c}, m(a) = 3 (J2) |
| PAPER3 Lemma 4.1 (the computed lemma on the QB(5) path) | `lem41.c` (all 0/1 matrices with non-increasing row and column sums in {1, 2, 3}, 7 ones; literal subset search for rigid K) | 22,792 matrices, 15,342,638 labellings: refined 0 failures, loose (size condition dropped) 338,494, plain 0; equal to PAPER3 A.2b and REVIEW3 |

Not reached by any instance: a petal with \|P_i\| ≥ 3 and κ(P_i) = 2 under covering m (the n_2 term of case (β));
that step is checked by hand only.

Reproduction (from `review4/`): `/usr/bin/clang -O2 -o code/kl1rev code/kl1rev.c` (likewise `sa_kl1.c` with `-lm`,
`lem41.c`), then `./code/kl1rev < data/data1753.blk`; planted families `code/run_n1.sh`, `code/run_hub.sh`,
`code/run_hub2.sh`, `python3 code/gen_big.py nW 100 3` (nW = 4, 5, 6); the search `code/run_sa.sh` (fixed seeds),
its dumps in `data/sa/dump_1.blk.gz`, `dump_2.blk.gz` (`gunzip -c ... | ./code/kl1rev`); `./code/lem41`;
`python3 code/zcheck.py data/data1753.blk 150 4 3`. Outputs are next to the inputs in `data/`.

## 5. The full chain, PAPER → PAPER2 → PAPER3 → PAPER4

1. Minimal counterexample G (n, then e minimal): e = 3n − 5, sparse, δ ≥ 4, E5 or C2 (PAPER.md Lemma 2.1;
   REVIEW.md ACCEPT).
2. C2 is impossible: every sparse C2 instance has a good W-vertex (PAPER.md Theorem 5.1; REVIEW.md ACCEPT; I
   re-derived (iii) and (iv) again, the u0 cases that the §0 analogy points to). In G every W-vertex is bad.
3. E5: no 4-factor, and the 2-block decomposition with 7 cut edges (PAPER.md Theorem 6.1); no G − p − q has a
   4-factor (a 4-factor of it is a nonempty 4-regular subgraph of G).
4. M-form: (p, q) good iff p ∈ I_X(M), q ∈ I_Y(M) for one 4-set M of cut edges (PAPER3 Theorem 2.1, via PAPER2
   Theorem 2.2 and Corollary 2.3 and PAPER.md Lemma 1.5; REVIEW2, REVIEW3 ACCEPT). Only the "if" direction is used.
5. PAPER3 Lemma 4.1 (computed; author's two programs, REVIEW3's two enumerations, and §4 here) gives one M with at
   most one uncovered L-vertex per side and no rigid set next to it; PAPER3 Lemma 3.4 puts an uncovered L-vertex
   into I(M); **PAPER4 Theorem 3.1** puts a vertex into I(M) when L is covered; on both sides (PAPER3 Theorem 4.2,
   Corollary 4.3(b) with REVIEW3's wording fix).
6. Step 4 then gives a good pair: contradiction with step 3. QB(5) holds.

Census inputs and n ≥ 40: none is used. The census (F1 for n ≤ 18, REVIEW.md F6 and its second method for
2-blocks with c = 6, 7, 8) enters only PAPER.md Lemma 6.4 and the clause "n ≥ 40" of Theorem 7.1, which no step
above needs; the only size facts used are \|C\|, \|B\| ≥ 4 (so \|A\|, \|D\| ≥ 6) from Theorem 6.1, on paper. Since
QB(5) now holds, no minimal counterexample exists and the n ≥ 40 clause is vacuous. The fixes F1 to F7, G1 to G3,
H1 and REVIEW3's optional wording fix of Corollary 4.3(b) are in force as PAPER4 §1.1 says; none of them touches a
step above except G1 (pairs taken in P × Q), which step 4 respects.

## 6. Overall verdict

**"QB(5) is proved": ACCEPT WITH FIXES.** The fix list is J1 (required, wording of the computational claim on
line 27 and in §5) and J2 to J4 (optional, editorial). No mathematical error was found in PAPER4 or on the QB(5)
path through PAPER, PAPER2 and PAPER3. QB(5) rests on written proofs, refereed in REVIEW to REVIEW4, plus one
finite computed lemma (PAPER3 Lemma 4.1), now confirmed by four programs (five enumerations). It is not a Lean
result and not a `check.sh` PASS.
