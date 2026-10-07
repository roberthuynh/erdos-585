# C1-REVIEW: independent referee report on C1-PAPER.md (lane M3-R)

Referee lane M3-R, October 5, 2026. Status: FINAL.

Paper: `reports/585-next/G110/C1-PAPER.md`, SHA-256
`3c67d183d93b8bb512dba6e46656dc6e11991bb5e29f2b22ff3f37e5dd960cf8`.
- Start of review: hash matches `C1-FROZEN.sha256`.
- End of review (02:51 EDT): hash recomputed, still matches. The paper was not edited.

Method: every step re-derived by hand before reading the author's checks (`c1checks/`, `M3-LOG.md`).
Own code only, in `reports/585-next/G110/review-c1/`. The minimality steps (Lemma 2.1, and its uses
in Lemmas 3.2, 4.1, 4.2) can only be checked on paper: they say a minimal counterexample would
contain a smaller one, and there is no counterexample to run them on.

## Overall verdict

**Theorem 4.3 (C1 holds): ACCEPT.** I found no mathematical error. Every step of §2 to §4 was
re-derived by hand: the minimality setup is well founded, Lemma 2.1 covers every case, the C0 case
is excluded by valid hypotheses only, and the arithmetic of Lemmas 3.1, 3.2, 4.1 and 4.2 and the
final count are all correct. Every identity the proofs use was recomputed by my own code with 0
mismatches. The minimality-free core (Lemma 4.4) holds on every sparse instance I could build,
including 420 with two or three distinct members of 𝒫. A census of all QB(4)-type graphs with
n ≤ 16 (all graphs with e = 3n − 4 exactly, which suffices by the edge-deletion step of Corollary
5.3) finds a quartic subgraph in every one.

**Corollaries.** 5.1 (C0, G110-quartic): ACCEPT. 5.2 (E4, E3): ACCEPT. 5.3 (QB(4), and QB(4) ⟺ C1):
ACCEPT; the remark right after it (line 242) needs fix R1. 5.4 (P_2, via §5.4 = REPORT.md Theorem 5
with c = 2): ACCEPT. 0.1 (P_2 for n ≤ 2M + 2): ACCEPT.

**No fatal gap.** One required fix (R1, a dropped word "bipartite" in a remark; no statement or proof
changes). As the paper says itself, nothing here is a project-oracle PASS: there is no Lean and no
`check.sh` run, and the minimality steps can only be checked on paper. This review checked them on
paper.

## Verdicts

| Item | Verdict | Note |
|---|---|---|
| Identity 1.1 | ACCEPT | hand re-derivation |
| Identity 1.2 | ACCEPT | hand re-derivation |
| Identity 1.3 | ACCEPT | hand re-derivation |
| Lemma 1.4 | ACCEPT | same as PAPER.md Lemma 0.1 (reviewed); re-derived |
| Lemma 1.5 | ACCEPT | re-derived; matches QUARTIC-REVIEW.md E4 step |
| (M) | ACCEPT | well founded: C1 below s, E4 up to s via Lemma 1.5 |
| Lemma 2.1 | ACCEPT | re-derived, all cases of (j, d) |
| Basic counts | ACCEPT | |
| Lemma 3.1 | ACCEPT | re-derived two ways (direct, and via the cut identity) |
| Lemma 3.2 | ACCEPT | re-derived |
| Lemma 4.1 | ACCEPT | re-derived |
| Lemma 4.2 | ACCEPT | re-derived |
| Theorem 4.3 | ACCEPT | re-derived; attack note 5 |
| Lemma 4.4 | ACCEPT | minimality-free; tested directly (below) |
| Cor 0.1 | ACCEPT | table matches PAPER.md Thms 3.3, 3.5, REVIEW.md, CORRECTIONS.md |
| Cor 5.1 | ACCEPT | |
| Cor 5.2 | ACCEPT | |
| Cor 5.3 (QB(4), and QB(4) ⟺ C1) | ACCEPT | statement and proof correct; fix R1 applies to the remark after it (line 242) |
| Cor 5.4 (P_2) and §5.4 | ACCEPT | budget identity and c = 2 case re-derived from Tutte's form |
| §6 hints | ACCEPT | not load-bearing; H1 to H9 re-derived as paraphrased in §6 (the brief's original hint wording is not on disk, so this covers the paraphrase); H10 is the route of §3-§4 |

### Required fix

**R1 (C1-PAPER.md line 242).** "So F2(N) (CORRECTIONS.md table: δ ≥ 4, Δ ≤ 6, e ≥ 3n − 4 implies a
4-regular subgraph, n ≤ N) holds for every N". The CORRECTIONS.md row for F2 reads "same with
e ≥ 3n − 4" under F1's "bipartite, δ ≥ 4, Δ ≤ 6": F2 is a bipartite statement. The paraphrase drops
"bipartite", and read literally it asserts P_4 restricted to δ ≥ 4 for all graphs, which is open
(the paper's own §7 says P_3 and P_4 stay open). Replace with: "So F2(N) (CORRECTIONS.md table:
bipartite, δ ≥ 4, Δ ≤ 6, e ≥ 3n − 4 implies a 4-regular subgraph, n ≤ N) holds for every N". With
"bipartite" restored, it follows from Corollary 5.3 directly (δ ≥ 4 is an extra hypothesis).

### Optional notes (no change needed)

- N1. §5.4 says w(C) ≥ 3 for a component with |C| ≥ 2. The sharp bound is w(C) ≥ 4
  (QUARTIC-REVIEW.md item 2: w ≥ 2c + 2 when e(C, S) is even, w ≥ 2c when odd, c = 2). Either
  bound exceeds the budget 2, so nothing changes.
- N2. Lemma 3.1 does not use that y is a port: the derivation holds for any y ∈ W − A. One
  consequence the paper could state: in a sparse instance, a member Q of 𝒫 containing a W-vertex y
  has V − Q as a slack −1 cut of G − y (κ(Q) = 1 gives k = 2, and g(Q) = 10 with u1 ∈ Q gives σ = −1).
  So the bad ports are exactly the ports lying in some member of 𝒫. I tested this (below).
- N3. Appendix A.5 says Lemma 4.2 was never exercised on two distinct petals. That is a coverage gap
  in the computation, not in the proof, which I re-derived by hand. My own tests (below) address it
  as far as I could.
- N4 (a strengthening, referee's own, proved here). **In a sparse C1 instance with D_U = 1, 𝒫 is a
  chain under inclusion.** Proof: let Q, Q' ∈ 𝒫 be incomparable, X = Q − Q', Y = Q' − Q (nonempty,
  disjoint), Q0 = Q ∩ Q'. By Lemma 4.2 all four sets lie in 𝒫, so Identity 1.2 gives
  20 = 20 − 2e(X, Y), that is e(X, Y) = 0, and κ(X) = κ(Q) − κ(Q0) = 0, so |X| ≥ 2 and, by sparsity,
  g(X) ≥ 10. Identity 1.2 for the disjoint pair (Q0, X) gives g(X) = 2e(Q0, X), so e(Q0, X) ≥ 5;
  likewise e(Q0, Y) ≥ 5. But S0 = V − Q0 = A0 ∪ C0 has g(S0) = 2D^{S0}(C0) + 12 = 12 + 2ε0 with
  ε0 = e(C0, Q0_W) (D(C0) = 0 as u1 ∈ Q0), so e(Q0, S0) = (g(Q0) + g(S0) − g(V))/2 = 7 + ε0, and
  D(A0) = 5 + ε0 ≤ D_W = 7 gives ε0 ≤ 2. Then 10 ≤ e(Q0, X) + e(Q0, Y) ≤ e(Q0, S0) ≤ 9, a
  contradiction. ∎ Consequence for review: the incomparable case of Lemma 4.2(c) can never occur in a
  sparse instance, so no computation on sparse instances can exercise it. Lemma 4.2 stands on its
  hand proof, which I checked twice, and on Identity 1.2, which I recomputed. The chain property
  itself is tested below (0 incomparable pairs, as predicted).

## Referee notes on the attack list

**1. Minimality setup, (M), Lemma 2.1.** Well founded. s is the least size of a quartic-free C1
instance, with the class orientation-free: the smaller side carries deficiency ≤ 1, and since the
sides differ in size by one the smaller side is determined. (M) uses C1 at sizes ≤ s − 1 (minimality)
and E4 at sizes ≤ s; Lemma 1.5 reduces E4(a) to a C1 piece of size between 1 and a − 1 (at least one
of the two pieces has positive size because E4(1) is empty, each vertex having degree ≤ 1). So E4(s)
rests on C1 below s and nothing is circular. Lemma 2.1: g(S) = 2d + 6j (checked from both sides of
Identity 1.1), so g ≤ 8 forces j ≤ 1. j = 0: G[S] ∈ E4(|S|/2), 1 ≤ |S|/2 ≤ s, both sides in-S
deficiency d ≤ 4; |S|/2 = s only for |S| = 2s, and balance forces S = V − w with w ∈ W, covered by
E4(s) in (M). j = 1: smaller side of size (|S| − 1)/2 with |S| odd, 3 ≤ |S| ≤ 2s − 1, so the size is
between 1 and s − 1, deficiency d ≤ 1, a C1 instance in whichever orientation. Simplicity and Δ ≤ 6
are inherited by induced subgraphs, and the bipartition is inherited. g is even. Every case of
(j, d) with g ≤ 8 is one of these (also checked on 74 sets with g ≤ 8, `rc_ident.py`).

**2. The C0 case (D_U = 0).** Excluded inside Lemma 3.2: ports exist (D_W = 6), G − y has no 4-factor
(else G has a quartic subgraph), so a violation exists; then g(Q) ≥ 10 turns into D_U ≥ 1 + D(C) ≥ 1.
Uses only Lemma 2.1 (valid for the minimal counterexample whatever D_U is) and Lemma 3.1 (pure
algebra). Equivalently, with D_U = 0: k ≤ 2 (D_A ≤ 6 − 1 = 5), σ ≤ −1, D(C) = 0, so
g(Q) = 6 + 2k + 2σ ≤ 8, against Lemma 2.1. Correct.

**3. Lemma 3.2.** D_A ≤ D_W − def(y) ≤ (6 + D_U) − 1 ≤ 6, since A ⊆ W − y and all deficiencies are
≥ 0; so 2k + 1 + ε ≤ 6 and k ≤ 2. Q ∋ y, U − C ≠ ∅ (|A| = |C| + k ≤ |W − y| = s forces |C| ≤ s − 1),
A ≠ ∅, so 2 ≤ |Q| ≤ n − 1 and Lemma 2.1 applies. Then k + σ ≥ 2 − D_U + D(C), σ ≤ −1 and k ≤ 2 give
D_U = 1, D(C) = 0, k = 2, then σ ≥ −1, so σ = −1, D_A = 5 + ε, ε ≤ 1, g(Q) = 10, κ(Q) = 1. Every
W-vertex has degree ≥ 5 − D_U ≥ 4 (Identity 1.3 on V − w); this is not needed by Lemma 3.2 itself.
Correct.

**4. Lemma 4.1(3), Lemma 4.2.** 4.1(3): Q − u1 has |Q| − 1 ≥ 2 vertices (|Q| ≥ 3 by 4.1(1)) and is
proper, and g(Q − u1) = 4 + 2deg_Q(u1) ≥ 10. 4.2(a): disjoint Q − u1 and Q' − u1 would give
deg(u1) ≥ 6. 4.2(b): Q ∪ Q' = V gives κ(Q ∩ Q') = 3, so g(Q ∩ Q') ≥ 18 by Identity 1.1, against
g(Q ∩ Q') ≤ 20 − g(V) = 12. This step uses no sparsity at all. 4.2(c): both sets are proper with at
least 2 vertices, so each has g ≥ 10, the sum is ≤ 20, so both are 10; κ is modular with sum 2, and
g = 10 forces κ ≤ 1 (6κ = g − 2D^S(S_W) ≤ 10), so both have κ = 1. Correct.

**5. Theorem 4.3's count.** D_W = 7, each W-vertex has deficiency ≤ 2 (degree ≥ 4), so the patterns
are 1^7, 2·1^5, 2^2·1^3, 2^3·1 (4 to 7 ports). The proof does not need the pattern: the union R_p of
all port petals is in 𝒫 (Lemma 4.2, induction on i), contains every port, so D((R_p)_W) = 7 (non-ports
have deficiency 0), while Lemma 4.1(2) bounds it by 2. Under N4 the union is simply the largest port
petal. Any set of ports with total deficiency ≥ 3 already gives the contradiction (for example three
degree-5 ports, or two degree-4 ports). Correct.

**6. Corollaries.** QB(4): delete edges down to e = 3n − 4 (keeps n, Δ ≤ 6, bipartite, and any
quartic subgraph of the result is one of H); g(V) = 8 = 2d + 6j gives j = 0, d = 4 (E4(n/2)) or j = 1,
d = 1 (C1((n − 1)/2)), sizes ≥ 1 from n ≥ 2 (j = 1 needs n odd, so n ≥ 3); j ≥ 2 would need g ≥ 12.
Converse: n = 2s + 1, e = 6s − D_U ≥ 6s − 1 = 3n − 4. P_2: Corollary 0.1 with C0 at every size
(Corollary 5.1). I re-derived the c = 2 case of REPORT.md Theorem 5 from Tutte's form
δ = f(S) + 4|T| − e(S, T) − q: (*) and (**) as in REPORT.md Lemma 2, 2(*) + (**) gives the budget
identity 3δ + 2D = 2e(S) + 4e(T) + 4D_T + Σ w(C) (checked term by term after substituting
D_S = D − D_T − ΣD_C), parity of q via f(C) + e(C, T) ≡ e(C, S); D = 4 and δ ≤ −2 even give δ = −2 and
budget 2; components with |C| ≥ 2 have w ≥ 4 (Lemma 4, applied to a barrier, so S ≠ ∅ and C is
proper), singletons w = 12 − a − 3[a odd] ≥ 4; so R = ∅, e(S) = 1, e(T) = D_T = 0, and (**) gives
|S| = |T| + 1. B = G − f is C0(|T|) with |T| ≥ 1. Correct. Corollary 5.1: B − o is C0(m) with m ≥ 5
(the side of o keeps degree 6, the other side has one more vertex); gadgets are exactly these graphs.
Corollary 5.2: immediate.

## Recomputed (own code, `review-c1/`, all runs under `timeout 240`)

Outputs are the `out_*.json` and `log_*.txt` files beside each script. The two s = 7 `rc_lattice.py`
runs (C1 and C0) share the name `out_lattice_g6_s7.json`; their separate outputs are
`log_lat_g6_s7.txt` and `log_lat_g6_c0s7.txt`.

| What | Script | Scope | Result |
|---|---|---|---|
| Identities 1.1 (incl. g = 2d + 6j, larger side d + 6j), 1.2, 1.3 | `rc_ident.py` seeds 101-606 | 1,195 random C1 (s = 5..8, D_U in {0,1}, W-min-degree 2..4) and 300 E4 instances; 418,500 sets, 1,250,080 vertex deletions, 418,500 pairs | 0 failures |
| Lemma 1.4 slack = 2k - D_A + ε; ε of Lemma 3.1 equals ε computed inside G - y | `rc_ident.py` | 17,190,232 cuts (all 2^{2s} cuts for s ≤ 6, 3,000 random per port above) | 0 failures |
| Lemma 1.4: min slack over all cuts = maxflow(G - y) - 4s (own Dinic) | `rc_ident.py` | 2,878 ports, exhaustive cuts | 0 failures |
| Lemma 3.1: g(Q) = 6 + 2D_U + 2k + 2σ - 2D(C), κ(Q) = k - 1 | `rc_ident.py` | 17,190,232 cuts | 0 failures |
| Basic counts e = 6s - D_U, D_W = 6 + D_U, g(V), g(V - w) | `rc_ident.py` | 1,195 instances, 8,992 W-vertices | 0 failures |
| Lemma 3.2 (localized, no minimality): every violation has k ≤ 2; if g(Q) ≥ 10 then D_U = 1, k = 2, σ = -1, u1 ∉ C, D_A = 5 + ε, g(Q) = 10, κ(Q) = 1 | `rc_ident.py` | 421 violations, 91 with g(Q) ≥ 10 | 0 failures. Profile (k, σ, g(Q), D(C)): (1,-1,6,0) 102, (1,-1,8,0) 186, (2,-1,10,0) 91, (1,-2,6,0) 12, (2,-1,8,0) 22, (2,-2,8,0) 7, (1,-2,4,0) 1 |
| Lemma 1.5: E4 violations have k = 1, ε ≤ 1, piece deficiencies ε and ≤ 1, sizes sum a - 1 | `rc_ident.py` | 10 random violations (see the exhaustive row below) | 0 failures |
| QB(4) census: every bipartite graph with Δ ≤ 6, e ≥ 3n - 4 has a quartic subgraph | `rc_census.py` (own graph6 decoder, own CNF, every witness validated) | genbg, e = 3n - 4 exactly: C1(5) 1, C1(6) 28, C1(7) 1,053, E4(6) 16, E4(7) 420, E4(8) 65,340 (n = 11..16); geng -b -D6, all e ≥ 3n - 4, no bipartition fixed: n = 11, 12, 13, 14: 2, 18, 39, 297 | all have one |
| Lemma 1.5 on every violation of every exhaustive E4(6), E4(7) graph (e = 6a − 4), both orientations | `rc_e4.py` | 16 + 420 graphs, 12 + 356 violations, 872 orientations for min slack = maxflow − 4a | 0 failures |
| Lemmas 4.1, 4.2, 4.4 by brute force over ALL vertex subsets (𝒫 enumerated completely) | `rc_lattice.py` | genbg C1 with W-degree ≥ 4, s = 6 (8 graphs), s = 7 (518); C0 with W-degree ≥ 5, s = 7 (11); random D_U = 1, s = 8 (1,200, W-degree ≥ 4) and s = 7..8 (800, W-degree ≥ 2: 539 sparse); random C0 gadgets s = 7..8 (400) | 0 failures. Every sparse instance here has 𝒫 = ∅ and no bad port, so these are vacuous for Lemma 4.2 |
| Same, on referee-built sub-case instances (own builder `rc_build.py`, written before reading `c1checks/`) | `rc_built.py` seeds 1-7 | 512 instances, s = 10, 11 (c ∈ {4, 5}, t ∈ {6, 7}, ε ∈ {0, 1}), all exactly sparse (brute force agrees with the flow test on all 512) | 0 failures. Always |𝒫| = 1 (the planted petal); bad-port deficiency 1 (368) or 2 (144); bad ports = ports in a member of 𝒫; maxflow(G − y) = 4s − 1 at every bad port |
| Exact 𝒫 by min-cut enumeration (closures of the residual graph of G − w, all w ∈ W), validated against brute force | `rc_xcheck.py` | 9,200 sparse instances (19 with 𝒫 ≠ ∅) | identical families |
| Lemma 4.2 on distinct members: chain instances S2 → X → Q1 with two planted petals | `rc_chain.py` seeds 1, 11-18 | 890 built, 420 exactly sparse, s = 16..18 (n = 33..37; c2 ∈ {4, 5}, p ∈ {5, 6}, t ∈ {6, 7}); |𝒫| = 2 (411) or 3 (9); 438 pairs | 0 failures: Lemma 4.1 on 849 members, 4.2(a)(b)(c) on 438 pairs, union in 𝒫, bad ports = ports in a member of 𝒫, deficiency ≤ 2, no W-vertex with maxflow ≤ 4s − 2. All 438 pairs nested, as N4 predicts |
| Lemma 4.4 at larger s, flows only; contrapositive "every port bad ⟹ not sparse" | `rc_random_core.py` seeds 41-44 | 16,578 random instances, s = 9..14 (C0 gadgets with W-degree ≥ 5, C1 with D_U = 1 and W-degree ≥ 4); 1,661 sampled for exact sparsity, all sparse | 0 failures, but vacuous: no instance had a bad port. Random instances of this kind are far from counterexamples; only built instances exercise the core lemma |

## Hypotheses shown to be needed (small examples, own code)

- **Sparsity is needed for Lemma 3.2.** In non-sparse random C1 instances the violations at ports
  include (k, σ, g(Q)) = (1, −1, 6), (1, −1, 8), (2, −1, 8), (2, −2, 8), (1, −2, 6) and (1, −2, 4)
  (profile in the table above, `rc_ident.py`). Without Lemma 2.1, k = 1 and σ ≤ −2 both occur, so the
  forced data k = 2, σ = −1 is a consequence of sparsity, not of the cut algebra alone.
- **Sparsity is needed for Lemma 4.2(c).** In non-sparse random C1 instances (D_U = 1, s = 7, 8,
  W-degrees from 2; seeds 21 and 22 of `rc_lattice.py`, 51 failing pairs recorded, at most one per
  first member) there are pairs Q, Q' with g = 10, κ = 1 and u1 ∈ Q ∩ Q' whose union has g = 6,
  so the union is not in 𝒫. Example: `rc_lattice.py rand 21 400 7 8 2 1`, instance 13 (s = 8):
  Q = {0..10, 13..16}, Q' = {0..9, 11, 13..16}, g(Q ∪ Q') = 6, g(Q ∩ Q') = 14. Here Q ∪ Q' = V − w
  for a W-vertex w of degree 2, so the failure is the trivial kind that Lemma 2.1's "every W-vertex
  has degree ≥ 4" removes. Lemma 4.2(b) needs no sparsity: it holds in every C1 instance with
  D_U = 1.
- **D_U ≤ 1 is needed in Lemma 3.2.** With D_U = 2 one has D_W = 8 and D_A can be 7, so k = 3 is no
  longer excluded and g(V) = 10 equals the sparsity threshold; the argument does not start. This
  matches the paper's §7 (C2 and E5 not attempted). Not demonstrated computationally.

## Comparison with the author's checks (read after my derivations)

- `M3-LOG.md` gives the same four-step argument as the paper. Its 02:40 entry reports adversarial
  counts (147,785 and 10,294) that differ from Appendix A.6 (145,753 and 10,168). The log says its
  early timestamps were estimates, and A.6 is a 200-second time-budgeted run, so different counts
  across runs are expected. Appendix A's numbers match the author's `out_*.json` files
  (`out_identities.json`: 159 instances, 6,158,304 cuts, 663 ports, 17 of 100 violations with
  g(Q) ≥ 10; `out_adversarial.json`: 145,753 and 10,168 with the per-s split of A.6;
  `out_core.json`, `out_lattice_pairs_0.json`, `out_sparse_core_0of6.json` as stated). Provenance
  only.
- My checks are independent of `c1checks/`: own generator, own Dinic max flow, own CNF encoding with
  witness validation, own graph6 decoder, and a sub-case builder written before I read `c1build.py`.
- Coverage beyond the paper: Lemma 4.2 on 438 pairs of distinct members of 𝒫 (A.5 had none), exact
  enumeration of 𝒫 (brute force at n ≤ 23, and min-cut closures validated against brute force on
  9,200 instances), Lemma 1.5 on every violation of the exhaustive E4(6) and E4(7) classes, and the
  QB(4) census to n = 16 with a geng -b cross-enumeration to n = 14.
- Agreement: the exhaustive genbg C1 classes with W-degree ≥ 4 at s = 6, 7 (8 and 518 graphs) are
  all sparse with no bad port, as A.2 says; the C0 class with W-degree ≥ 5 at s = 7 has 11 graphs,
  matching A.2's 11 sparse C0 graphs.

## What this review could not check

- The minimality steps (Lemma 2.1, and through it Lemmas 3.2, 4.1, 4.2 inside the minimal
  counterexample) were checked on paper only. No computation can run them, since a counterexample
  would have to exist.
- No Lean formalization exists and `check.sh` was not run (outside this lane's scope), so no result
  here is a project-oracle PASS. On the project's ladder the paper's own labels stand: rung (a) as a
  written proof for Theorem 4.3 and its corollaries, pending formalization.
- §6 is checked against its own paraphrase of the hints, not against the original brief text.
