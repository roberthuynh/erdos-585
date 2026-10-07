# Review: sms-census lane, S10(13) and S10(14)

Status: FINAL (2026-10-04, 05:40). Reviewer: independent subagent; tasks 1 to 4 complete.

Reviewed: `lanes/sms-census/REPORT.md`; `gen585.c` (sha256 prefix 715d011fa1673d37, matches runs.log);
`gen585_run14.c` (e24007ee9dec1fbb; differs from gen585.c only by the sibling pair cache and the STATUS
line); `run_slices.sh`; `runs.log`; the n = 14 state files.

Reviewer's sources and slice logs: `census/programs/replication/` (in this supplement) (durable copy). Binaries and bulk
outputs stayed in the session scratch folder (`scratchpad/review-sms/`, temporary). Nothing in the lane
folder was edited; lane scripts were only run read-only.

## Lemmas

- **Lemma 1 (minimal counterexample): ACCEPT.** (a) to (e) follow as written. The hypothesis "S10(m) for
  2 <= m < n" is vacuous for m <= 5 (3m - 4 > m(m-1)/2) and true for m = 6 (K6 minus at most one edge
  contains K5, which is two edge-disjoint 5-cycles); m = 7..12 are covered by the reruns below.
- **Lemma 2 (edge floors): ACCEPT.** e - floor(2e/j) is nondecreasing for j >= 2, so L_{j-1} is a valid
  floor along any minimum-degree deletion chain. Recomputed L_j for n = 13 and n = 14 by hand; they match
  the report and the bounds the program prints (`k=12 L=30 U=31 cap=5` and so on). U_j = 3j - 5 is (d).
- **Lemma 3 (degree look-ahead): ACCEPT.** Each DP constraint is necessary for a real chain: t <= 6,
  t <= j - 1, t <= delta(G_{j-1}) + 1, t <= floor(2 U_j / j) (min degree <= average degree),
  L_j <= e_j <= U_j, every degree-(t-1) vertex joined, other neighbors of degree t..5, and at j = n
  e = EF with min degree >= MINDF. The memo key is the whole histogram and nothing else enters the
  value; table overflow aborts (exit 6).
- **Lemma 4 (completeness, McKay 1998): ACCEPT.** m(G) is chosen among minimum-degree vertices by an
  isomorphism invariant (neighbor-degree multiset in 3-bit digits, at most 6 per digit so no carry;
  then edges among neighbors, at most 15 in 6 bits), ties broken by the largest canonical label from
  `densenauty`. A child is kept iff v is in the Aut-orbit of m. When Aut(P) is trivial two kept
  siblings cannot be isomorphic (an isomorphism fixing v restricts to an automorphism of P, so it is the
  identity and the neighborhoods coincide); when Aut(P) is not trivial, kept siblings are deduplicated
  by canonical form. Every G in D_j has G - m(G) in D_{j-1}, and the neighborhood that rebuilds G is
  always tried. Independent confirmation: the level-10 set of the n = 13 tree with the look-ahead off
  equals my geng-based set exactly (below). Nit: the report's range for t omits t >= MINDF at j = n,
  which the code also enforces (line 1036); that bound is sound because the final minimum degree is
  at least 4.
- **Lemma 5 (certified rejections): ACCEPT WITH FIX.** True for what it covers: a pair rejection happens
  only after `verify_pair` (or `verify_global` for the sibling cache) has checked two explicit cycles
  against the child's own adjacency, and a sparsity rejection only after a direct recount. The sentence
  "So a search bug could only *miss* pairs" overstates it: rejections by the invariant filter, the orbit
  test, sibling deduplication, the look-ahead and the edge bounds are not certified. Their soundness rests
  on Lemmas 2 to 4 (checked above) and on the cross-checks below. Suggested fix: "So a bug in the pair or
  sparsity test could only make the search keep extra graphs; the other rejections rest on Lemmas 2 to 4."

## Code items (gen585.c)

- **m(G) and acceptance test: ACCEPT.** Lines 867-897 (invariant pre-filter: rejects only if some
  degree-t vertex has a strictly larger invariant), 923-944 (nauty orbit test when ties > 1), 945-954
  (sibling dedup when Aut(P) != 1). v always has minimum degree t, because every degree-(t-1) vertex of P
  is forced into N and no vertex of P has degree < t - 1.
- **Neighborhoods tried per t: ACCEPT.** `extend` (1028-1077): t runs over
  [max(L_j - e, 0, MINDF at j = n), min(U_j - e, 6, j - 1, delta(P) + 1)]; F = all degree-(t-1)
  vertices is forced; the optional set is exactly the vertices of degree t..5; `enum_comp` (1001-1026)
  enumerates every degree composition summing to t - |F| and `enum_class` (979-999) every subset for each
  composition. This is exactly the set of N a minimum-degree deletion chain can produce. The only skip is
  a composition whose child histogram fails `dp_ok`.
- **Memoized look-ahead: ACCEPT.** `dp_ok`/`dp_try` (728-783) and the call in `enum_comp` (1005-1014)
  apply the same transition as Lemma 3; the child histogram is computed correctly (f vertices move from
  t-1 to t, x[d] from d to d+1, new vertex at t). No constraint a real chain can violate.
- **Edge floor and upper bound arithmetic: ACCEPT.** 1130-1142 (Lb, Ub, CAP) and 1034-1041 (tlo, thi).
  `ensure_tight` (798-821) stores only sets that can be violated (b < thi and b < |T|); S = V(H) is
  exempt only at the final level.
- **Pair test: ACCEPT.** `has_pair_through` (533-567): supports are inside the 4-core component of v,
  the whole component is tried first, then every S containing v with min degree >= 4 (`enumS`, complete;
  overflow aborts). Both pair routines return 1 only through `verify_pair` (lines 194, 401), which checks
  each cycle edge by edge in the child, distinct vertices, both vertex sets equal to S, and no shared
  edge; a failure exits. The cache path (898-904) re-verifies with `verify_global`. Missed pairs could
  only enlarge the tree.
- **No line found that could make the search incomplete.** Minor notes: the compile warns that MAXN is
  redefined (both definitions are 32, harmless); `lookahead_ok` (830-848) is sound but only active with
  `-C`; slice resumption is deterministic and the two n = 14 halves cover all 1,303,711 level-10
  subtrees (651,856 + 651,855), with level sums equal to the report's table.

## Controls (rerun by the reviewer, fresh binaries built from the same sources)

- S10 with gen585, `gen585 n 3n-4 5 2 4`: finals 0 for every n = 4..12 (n = 11 in 0.1 s, n = 12 in
  2.4 s). This removes the dependence on the external census for n <= 12.
- Positive control with gen585, `gen585 n 3n-5 6 3 4`: finals 1, 2, 3, 11 at n = 7..10, as reported;
  also 0 at n = 11 and 2 at n = 12. Identical with the look-ahead off (`-L`).
- `test_pair.py 400` (lane script, run in place): 0 disagreements (233 pair, 167 no pair).
- `validate_levels.py` level 8 of the n = 13 tree (lane script, SAT oracle): 4,738 = 4,738, MATCH.
- Level counts with the look-ahead off reproduce the lane's V4/V5 values (level 8: 4,738; level 9: 85,282).
- Not rerun: the n = 13 and n = 14 main runs with the lane's program (a rerun of the same program only shows
  determinism). The n = 14 run log was checked instead: both halves `STATUS complete ... finals=0`, the
  subtree counts cover every level-10 node, and the level sums equal the report's table.

## Independent replication of S10(13): DONE, 0 graphs (rung (b), computation)

Different generator, vertex order, reduction and pair test from the lane. Sources and scripts are in
`census/programs/replication/` (in this supplement); slice logs are copied there as `status.txt` (main run and pos12)
and `status2.txt` (level-12 second pass).

**Pair test (my own C, written without the lane's code).** `rvpair.h` (v1: every cycle through the new
vertex inside the 4-core, bucketed by vertex set, edge-disjointness inside each bucket), `rvpair2.h` (v2:
list candidate supports, then Hamilton cycles of each as edge masks), `rvpair3.h` (v3, used in the runs:
whole 4-core component first, then each support; Hamilton cycle C1 plus a residual search for C2). Every
pair found is re-checked from the two edge masks alone (each a connected 2-regular spanning subgraph of
G[S], all edges present, masks disjoint); a failed check aborts the run.
- Against `tools/brute.py`: 0 disagreements on 1,200 random graphs for v3 (651 pair, 549 no pair) and on
  800 for v1 and v2 (`validate_rvpair.py`, seeds 20261004, 777, 4242).
- Four-way agreement (v1, v2, v3 and the lane's `gen585 -p`) on 379,431 graphs: all 197,867 graphs on 9
  vertices with max degree <= 6; all 140,019 graphs on 10 vertices with degrees 4..6 and 22-25 edges;
  29,673 graphs on 12 vertices and 11,872 on 13 vertices from geng slices. 0 differences.

**Generator.** nauty 2.8.9 `geng` (copied from the lane's build, rebuilt in scratch) with a PRUNE hook
(`rvprune.c`). geng adds vertices 0, 1, 2, ... and deletes a maximum-degree vertex canonically, so every
prefix is an induced subgraph of the output and the parent always passed PRUNE. The hook rejects a prefix
that has a pair through its newest vertex, or a set S containing the newest vertex with |S| >= 2,
S != V(final), and e(S) > 3|S| - 5. So every output is pair-free with every proper set sparse.

**One-stage runs** (`geng -d4 -D6 n (3n-4):(3n-4)` with the hook): S10 gives 0 graphs for n = 7..11
(n = 11 in 30 s with v2). Positive control (`RV_SP=6 RV_SPMIN=3`, 3n - 5 edges): 1, 2, 3, 11, 0 graphs
at n = 7..11, equal to gen585. The cost grew about 20x to 100x per vertex (n = 12 sampled at about
600 CPU-s), so for n = 13 I used the reduction below instead of `geng -d4 -D6 13 35:35`.

**Two-stage run for n = 13.** If H is in D_13 (Lemma 1), let v be a minimum-degree vertex; t = deg v is 4
or 5 (13t <= 70). G = H - v has 12 vertices, 35 - t edges, degrees >= t - 1, max degree <= 6, no pair, and
every S with |S| >= 2 sparse. So a copy of G is output by `geng -d4 -D6 12 30:30` (t = 5) or
`geng -d3 -D6 12 31:31` (t = 4) with the hook. The OUTPROC hook (`rvext.c`) then tries every N with
|N| = t, N containing every degree-(t-1) vertex, every vertex of N of degree <= 5, and keeps H = G + v only
if every proper S containing v is sparse and H has no pair through v.
- Method check on known answers: positive controls n = 7..12 give 1, 2, 3, 11, 0, 2 isomorphism classes
  (labelg); the two n = 12 graphs are canonically identical to gen585's two finals. S10 at n = 11 and
  n = 12 gives 0.
- t = 4 class: 400 res/mod slices, all complete, 3,099 CPU-s; 56,632 graphs G; 392,965 extensions tried,
  3 rejected for sparsity, 392,962 for a verified pair; **0 survivors**.
- t = 5 class: 400 slices, all complete, 4,056 CPU-s; 6,200 graphs G; 12,448 extensions, all rejected
  for a verified pair; **0 survivors**.
- No slice failed or timed out; 4 processes; about 40 minutes of wall time on a shared machine.

Build (from `census/programs/replication/` (in this supplement), with the lane's `nauty2_8_9/` copied next to the sources;
the worker scripts assume the scratch layout, with binaries one level above `runs13/`):

```
clang -O3 -march=native -o rvpairtest rvpairtest.c
clang -O3 -march=native -DWORDSIZE=32 -DMAXN=WORDSIZE -DPRUNE=rvprune -DOUTPROC=rvext -DSUMMARY=rvsummary2 -Inauty2_8_9 -o rvgengx nauty2_8_9/geng.c rvext.c nauty2_8_9/gtools.c nauty2_8_9/nauty.c nauty2_8_9/nautil.c nauty2_8_9/naugraph.c nauty2_8_9/schreier.c nauty2_8_9/naurng.c
RV_SP=5 RV_SPMIN=2 RV_EXT_EF=35 RV_EXT_MINDF=4 timeout 240 ./rvgengx -q -d4 -D6 12 30:30 R/400 > H.g6
RV_SP=5 RV_SPMIN=2 RV_EXT_EF=35 RV_EXT_MINDF=4 timeout 240 ./rvgengx -q -d3 -D6 12 31:31 R/400 > H.g6
```

(R = 0..399; a slice is complete when its stderr has the `rvext: G=...` line; success is an empty H.g6.)
The one-stage hook alone builds with `-DPRUNE=rvprune -DSUMMARY=rvsummary` and `rvprune.c`.

So D_13 is empty, and with Lemma 1, S10(13) holds given S10(m) for m <= 12. That hypothesis is now
covered three ways without the external census: gen585 reruns (n = 4..12), one-stage geng (n = 7..11),
two-stage geng (n = 11, 12); m <= 6 is immediate (Lemma 1 line).

## Cross-checks of the lane's machinery (relevant to n = 14)

- **Level 10 of the n = 13 tree, look-ahead off:** gen585 (`-L -d 10 -S 10`) gives 1,498,684 graphs;
  `geng -D6 10 21:25` with my hook gives 1,498,684; the canonical-form sets are identical (symmetric
  difference 0). This checks the canonical augmentation, the neighborhood enumeration, the edge floors,
  sparsity and the pair test together, one level deeper than the lane's own V5 check.
- **Level 12 of the n = 13 tree, look-ahead on (certified build, 61,983 graphs):** every graph has no pair
  by my test, is fully sparse by direct count, and admits an extension neighborhood. The 31-edge part
  (56,632 graphs) has exactly as many classes as my t = 4 class (56,632). Every member of that class admits
  an extension (degree sum 62 with degrees 3..6 forces f <= 3 vertices of degree 3 and at least 4 - f of
  degree 4 or 5), and the lane's graphs are pairwise non-isomorphic members of the class, so the two sets
  are equal. The 30-edge part (5,351 graphs): a second pass over the t = 5 class (`rvsave.c`, 400 slices,
  all complete) kept the graphs that admit an extension (at most 5 vertices of degree 4) and wrote them
  out: 5,351 graphs, canonical-form set identical to the lane's (symmetric difference 0). The other
  849 of the 6,200 class members have 6 vertices of degree 4 and no extension, as expected. So the
  lane's whole level 12 (61,983 graphs, look-ahead on) equals the independently generated set of
  extendable 12-vertex candidates: the look-ahead dropped nothing that could reach level 13.

## Overall verdict

- **S10(13): ACCEPT.** Independently replicated with a different generator, deletion order, reduction and
  pair test; the lane's lemmas and code also check out.
- **S10(14): ACCEPT WITH CAVEAT.** It rests on one program. I found no line that could make the search
  incomplete; that program's level sets equal independent computations at n = 13 (level 10 with the
  look-ahead off, 1,498,684 graphs; level 12 with it on, 61,983 graphs; both exact); and the n = 14 log
  is consistent. The n = 14 run used the same code path (`gen585_run14.c` lacks only the sibling cache). I did not
  replicate n = 14: the same two-stage method would need 13-vertex classes, roughly 20x to 100x the
  n = 13 cost. Cite it as computed and reviewed, not independently replicated.
- **Corollary 1 (S10(n) implies S4(n+1)): ACCEPT.** S4 at 14 follows from S10(13). S4 at 15 and "no
  6-regular avoider on 15 vertices" inherit the S10(14) caveat.
- **Report fixes:** (1) Lemma 5 wording, above. (2) "This lane's own runs re-derive n <= 11" can now say
  n <= 12: the same program gives S10(12) finals 0 in 2.4 s, and geng confirms it.
