# sms-census lane: S10 at n = 13 and n = 14

> **Saved by the lane lead (2026-10-04).** The harness blocked the subagent's own write of this file,
> so this text is its final report, saved verbatim apart from this note and two lines marked
> [review fix]. Lead check: `runs.log` shows `STATUS complete ... finals=0` for the n = 13 runs
> (first build, look-ahead build, certified build) and for both n = 14 halves (r0 and r1).
>
> **Review status: reviewed** (`SMS-CENSUS-REVIEW.md`, final).
> - S10(13): accepted, and independently replicated with a different generator, deletion order,
>   reduction and pair test (0 graphs).
> - S10(14): accepted with a caveat. It rests on this one program and was not independently
>   replicated, so cite it as computed and reviewed. The reviewer found no line that could make the
>   search incomplete, and this program's level sets at n = 13 equal independent computations.
> - Corollary 1: S4 at 14 is accepted. S4 at 15 and "no 6-regular avoider on 15 vertices" inherit
>   the S10(14) caveat.
> - Fixes applied: the Lemma 5 wording, and the census dependence (the reviewer reran this program
>   for n = 4..12 and a geng route for n = 7..12, so the chain no longer needs the external census).

The code, run log (`runs.log`) and state files are in this folder.

## Bottom line

- **S10 holds at n = 13 and at n = 14.** Every graph on 13 vertices with max degree <= 6 and at
  least 35 edges has a pair, and every graph on 14 vertices with max degree <= 6 and at least 38
  edges has a pair.
  - Rung (b), exhaustive computation.
  - [review fix] It needs S10 for n <= 12. The reviewer's reruns of this program give it for
    n = 4..12 (finals 0), and an independent geng route confirms n = 7..12.
- **Coordinator's implication.** S10(n) implies S4(n+1), and it is included below as Corollary 1.
  Consequences:
  - S4 holds at 14 and 15.
  - No avoider with max degree <= 6 and deficiency <= 4 has <= 15 vertices.
  - **No 6-regular avoider has 15 vertices.**
  - A least-order (3,3)-critical core needs >= 16 vertices.
- **Corollary 2.** For 7 <= k <= 14, the largest avoider with max degree <= 6 on k vertices has
  exactly 3k - 5 edges (least deficiency exactly 10).
- **Not reached:**
  - 6-regular at n = 16: a direct search is estimated at about 8 core-hours.
  - S10 at n = 15: estimated at about 24 core-hours. It would give 6-regular n = 16.
  - Both were measured on 1/2000 samples and not run, under the 3-hour and 2-process limits.

## Results

| target | search space (one graph per isomorphism class) | time (one core) | outcome |
|---|---|---|---|
| S10 control, n = 7..10 | minimal counterexamples (Lemma 1) | < 0.1 s each | none, agrees with the census |
| positive control: "e >= 3n - 5 forces a pair", n = 7..10, sparsity e(S) <= 3\|S\| - 6 on proper S with \|S\| >= 3 | same machinery | < 0.2 s | 1, 2, 3, 11 avoiders; n = 7 is exactly K2 ∨ C5 |
| S10, n = 13 | 13 vertices, 35 edges, degrees 4..6, sparsity e(S) <= 3\|S\| - 5 on proper S with \|S\| >= 2, pair-free; explored through minimum-degree deletion chains. Tree: about 8.0M nodes | first build 463.7 s; look-ahead build 442.3 s; final certified build 79.3 s | none in all three runs |
| S10, n = 14 | same conditions with 38 edges. Tree: 2.40e8 nodes; 4.93e9 candidates tested at level 13 | 3,582.5 core-s (2 processes, about 30 min each) | none |
| 6-regular, n = 15 | Corollary 1 from S10(14) | none | none exists |
| 6-regular, n = 16 (direct, MINDF = 6) | `gen585 16 48 5 2 6 -x 14 ...` | estimate 29,600 core-s | open, not run |
| S10, n = 15 | `gen585 15 41 5 2 4 ...` | estimate 86,600 core-s | open, not run |

Level sizes:

| run | level 9 | level 10 | level 11 | level 12 | level 13 | level 14 |
|---|---|---|---|---|---|---|
| n = 13, final build | 44,572 | 646,323 | 7,228,638 | 61,983 | 0 | n/a |
| n = 14 | 71,786 | 1,303,711 | 22,791,288 | 214,897,612 | 683,461 | 0 |

- **n = 13:** 405,413 children were tested at the final level and none was accepted. The run made
  27,586,946 certificate-checked pair rejections.
- **n = 14:** 4,405,794 children were tested at level 14 and none was accepted. The run made
  83,455,350 certificate-checked pair rejections.
- **Agreement between builds:** the final build and the look-ahead build agree on every n = 13
  level count. The first build used a weaker look-ahead, giving 57,313 / 831,257 / 7,352,173 /
  62,832 / 0.

## Method

Canonical augmentation of graphs with degrees up to 6, written in C (`gen585.c`), with nauty 2.8.9
built locally in `nauty2_8_9/` for canonical labels.

- **Generation.** Vertices are added one at a time, following McKay, "Isomorph-free exhaustive
  generation", J. Algorithms 26 (1998). The canonical deletion vertex is a minimum-degree vertex,
  which keeps intermediate graphs dense.
- **Pruning applied to every intermediate graph:**
  - pair-free, testing only supports through the new vertex;
  - max degree <= 6;
  - the sparsity condition;
  - a per-level edge floor;
  - an exact degree-histogram look-ahead.
- **Pair test.** For each support S that contains the new vertex and has min degree >= 4 in G[S],
  it looks for two edge-disjoint Hamilton cycles of G[S]. Supports are tried with the whole 4-core
  component first. The search enumerates C1 through a fixed edge at a degree-4 vertex, then
  searches the residual graph for C2 with degree-2 forcing.
- **Why not SMS proper or a SAT propagator.** SMS proper needs CMake, which is not installed here.
  pysat's cadical195 does expose `connect_propagator`, but every propagation would call back into
  Python. The CEGAR approach had already stalled at n = 12.
- **Tried and dropped.** A forced-edge pair search was slower. A cache of 4-sets shared between
  sibling candidates got 0 hits; it is harmless and stays in the final source.

## Soundness, one rule at a time

**Lemma 1 (minimal counterexample).** Assume S10(m) for 2 <= m < n. If S10(n) fails, some H on n
vertices has:
- (a) max degree <= 6;
- (b) no pair;
- (c) exactly 3n - 4 edges;
- (d) e(H[S]) <= 3|S| - 5 for every proper S with |S| >= 2;
- (e) min degree >= 4;
- (f) every edge cut with both sides of size >= 2 has >= 6 edges.

*Proof.*
- Delete edges from a counterexample until 3n - 4 remain. A subgraph of an avoider is an avoider,
  so (a) and (b) survive.
- (d): H[S] is an avoider with max degree <= 6 on 2 <= |S| <= n - 1 vertices, so S10(|S|) gives
  e(H[S]) < 3|S| - 4.
- (e): apply (d) to S = V - v, which gives 3n - 4 - deg v <= 3n - 8.
- (f): e(H) <= (3|X| - 5) + (3|Y| - 5) + |cut|. ∎

The program enforces (a) through (e); (f) is implied.

**Lemma 2 (edge floors).** Take the deletion chain: v_n is a minimum-degree vertex of H, v_{n-1} is
a minimum-degree vertex of H - v_n, and so on. Write G_j for the graph induced on v_1..v_j.

Since δ(G_j) <= floor(2e/j), and e - floor(2e/j) is nondecreasing in e (because 2/j <= 1), we get
e(G_j) >= L_j, where L_n = 3n - 4 and L_{j-1} = L_j - floor(2L_j/j):
- n = 13: L_12..L_2 = 30, 25, 21, 17, 14, 11, 8, 6, 4, 2, 1.
- n = 14: L_13..L_2 = 33, 28, 24, 20, 16, 13, 10, 8, 6, 4, 2, 1.

The upper bounds U_j = 3j - 5 come from (d).

**Lemma 3 (degree look-ahead).** v_j has degree t_j = δ(G_j) in G_j. Therefore:
- every vertex of G_{j-1} with degree t_j - 1 is adjacent to v_j;
- no vertex of G_{j-1} has smaller degree;
- the neighbors of v_j have degree <= 5 in G_{j-1}.

So the degree histograms of G_k, ..., G_n form a path of such steps. Every level j satisfies
L_j <= e <= U_j, and the path ends at 3n - 4 edges with min degree >= 4. A memoized search decides
whether such a path exists from a candidate's histogram, and candidates without one are
discarded. The chain of a real counterexample always has such a path. The cruder bound
t_j <= δ(G_k) + (j - k) is implied; the code re-checks it and the counter stayed at 0.

**Lemma 4 (completeness; McKay 1998).**

*How m(G) and acceptance are defined:*
- m(G) is a minimum-degree vertex with the largest isomorphism invariant (the multiset of neighbor
  degrees, then the number of edges among the neighbors).
- Ties are broken by the largest nauty canonical label.
- A candidate P + v is kept iff v is in the Aut-orbit of m.
- When Aut(P) ≠ 1, kept siblings are deduplicated by canonical form.

*Completeness.* Let D_j be the set of graphs on j vertices that satisfy (a), (b), (d), e >= L_j
and Lemma 3. Then:
- If G ∈ D_j, then G - m(G) ∈ D_{j-1}.
- The program tries every neighborhood N of every admissible size t, where
  max(L_j - e(P), 0) <= t <= min(6, j - 1, U_j - e(P), δ(P) + 1).
- Each such N contains all degree-(t - 1) vertices and no degree-6 vertex. Only degree
  compositions infeasible for Lemma 3 are skipped.
- So by induction every isomorphism class of D_j is produced, and D_n contains every graph of
  Lemma 1. ∎

**Lemma 5 (certified rejections).** This applies to the n = 14 run and the final n = 13 run.
- A candidate is dropped for a pair only after a separate routine re-checks two explicit cycles
  against the candidate's own adjacency: same vertex set, no shared edge.
- Sparsity rejections are re-checked by a direct edge count.

[review fix] So a bug in the pair or sparsity test could only make the search keep extra graphs. The
other rejections (invariant filter, orbit test, sibling deduplication, look-ahead, edge bounds) are
not certified; they rest on Lemmas 2 to 4. Kept extra graphs would surface as reported final graphs, which
`validate_finals.py` checks with brute.py and pair_oracle; none was reported. The first and
look-ahead n = 13 builds lacked this certification, which is why the certified rerun exists.

**Theorem.** D_13 and D_14 are empty (computation). With Lemma 1:
- S10(<= 12) (census) implies S10(13).
- S10(<= 13) implies S10(14).

**Corollary 1 (coordinator).** S10(n) implies S4(n+1). For H on n + 1 vertices with max degree
<= 6 and >= 3n + 1 edges, delete a minimum-degree vertex:
- if its degree is t <= 5, at least 3n - 4 edges remain;
- if H is 6-regular, 3n - 3 edges remain.

S10(12) gives S4(13), so S4 holds at every order up to 15: no avoider with max degree <= 6 and
deficiency <= 4 on <= 15 vertices. In particular no 6-regular avoider on 15 vertices.

**Corollary 2.** S10(k) gives at most 3k - 5 edges. For the lower bound, take K2 ∨ C5 plus k - 7
vertices of degree 3, each joined to three vertices of degree <= 5:
- spare degree stays at 10 throughout, so suitable attachment vertices always exist;
- a support has min degree >= 4, so it misses the last added vertex, and induction shows the
  graph is pair-free;
- brute.py and pair_oracle both return NOPAIR for k = 8..14.

## Validation

- **Pair test vs independent deciders:** 0 disagreements with pair_oracle and brute.py on 400
  random graphs (`test_pair.py`).
- **Final pair test vs first version:** 0 differences on 404,609 graphs:
  - all 197,867 graphs on 9 vertices with max degree <= 6;
  - 140,019 graphs on 10 vertices with degrees in [4, 6] and 22-25 edges;
  - 66,723 level-11 avoiders.
- **Generator with look-ahead off vs geng.** Level sets equal geng + oracle + Python sparsity as
  sets of canonical forms:
  - n = 13 tree: level 8 (4,738 graphs) and level 9 (85,282).
  - n = 14 tree: level 9 (110,243), where every survivor is NOPAIR by pair_oracle.
- **Positive control.** The finals equal independent geng enumerations: 2 at n = 8, 3 at n = 9,
  and 11 at n = 10 with the look-ahead on. All 17 control finals are NOPAIR by brute.py and
  pair_oracle.

## Rerun

Run in this folder. Arguments are `gen585 N EF SP SPMIN MINDF`: N vertices, final edge count EF,
sparsity e(S) <= 3|S| - SP for SPMIN <= |S| <= N - 1, final min degree MINDF. Use fresh tags,
because the existing state files resume.

```
cd census/programs/gen585
timeout 240 clang -O3 -march=native -DWORDSIZE=32 -DMAXN=WORDSIZE -Inauty2_8_9 -o gen585 gen585.c nauty2_8_9/nauty.c nauty2_8_9/nautil.c nauty2_8_9/naugraph.c nauty2_8_9/schreier.c nauty2_8_9/naurng.c
./run_slices.sh n13check 10 -- 13 35 5 2 4 -s 9 -A
./run_slices.sh n14check_r0 40 -- 14 38 5 2 4 -s 10 -r 0 -m 2 -A
./run_slices.sh n14check_r1 40 -- 14 38 5 2 4 -s 10 -r 1 -m 2 -A
```

- **Success signal:** runs.log shows `STATUS complete ... finals=0`.
- **If a final appears:** run
  `timeout 240 [temporary path] validate_finals.py runs/finals_<tag>.txt 38 4`
  on it.
- **Controls:**
  - `for n in 7 8 9 10; do ./gen585 $n $((3*n-4)) 5 2 4 | grep STATUS; done` should give finals=0.
  - Changing the arguments to `$((3*n-5)) 6 3 4` should give finals = 1, 2, 3, 11.
  - Then run `validate_levels.py` and `test_pair.py`.
- **Sources:** `gen585.c` (final), `gen585_run14.c` (n = 14 run), `gen585_first.c` (first n = 13
  run), `gen585_dp.c` (n = 13 look-ahead build). runs.log records their sha256 prefixes and the
  nauty tarball hash.

## Scope notes

- n <= 12 was not redone, except the n <= 10 controls and one incidental 0.5 s run at n = 11
  (finals 0).
- To make the chain independent of the census, one n = 12 run of the same program is a
  seconds-long command.

## Next step

Have gen585.c reviewed, focusing on Lemmas 2 to 4. Then run S10 at n = 15 split across 16 or more
cores, about 24 core-hours. The level-10 subtrees are independent (`-r/-m`), and the result would
give S4 at 16 and no 6-regular avoider on 16 vertices.

## Review

Yes. S10(13) and S10(14), and the corollaries that rest on them, come from one program and need
independent review before anyone cites them.
