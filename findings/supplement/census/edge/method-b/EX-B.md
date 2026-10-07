# ex(17), ex(18), ex(19) by a second method (method B)

Lane exb (wave8), 2026-10-06 EDT. ex(n) is the maximum number of edges of a simple bipartite graph on
n vertices with maximum degree at most 6 and no nonempty 4-regular subgraph. Method 1 is
`reports/585-next/wave6/excensus/` (EX.md). Rung (b) throughout: computed exact values, no Lean, no
`check.sh`.

## 1. Answer

The block between the markers is rewritten by `code/collect.py` from the shard files (detached jobs in
`JOBS.md`); the verdict paragraph after it is by hand.

<!-- COLLECT:BEGIN -->
Written 2026-10-06 10:52:51 EDT by `code/collect.py` from the shard files.

| Job | Command | Shards ok / total | Output graphs (no 4-regular subgraph) | Whole class (graphs generated) | CPU s (user) | Status |
|---|---|---|---|---|---|---|
| pr_n17_e44_8x9 | `bin/bipgen 8 9 44:44 4:4 6:6` | 1/1 | 0 | - | 2 | COMPLETE |
| pr_n17_e44_9x8 | `bin/bipgen 9 8 44:44 4:4 6:6` | 1/1 | 0 | - | 2 | COMPLETE |
| pr_n18_e47_8x10 | `bin/bipgen 8 10 47:47 4:4 6:6` | 1/1 | 0 | - | 11 | COMPLETE |
| pr_n18_e47_10x8 | `bin/bipgen 10 8 47:47 4:4 6:6` | 1/1 | 0 | - | 2 | COMPLETE |
| pr_n18_e47_9x9 | `bin/bipgen 9 9 47:47 4:4 6:6 {r}/{mod}` | 4/4 | 0 | - | 58 | COMPLETE |
| pr_n19_e51_9x10_d5 | `bin/bipgen 9 10 51:51 5:5 6:6` | 1/1 | 0 | - | 18 | COMPLETE |
| pr_n19_e51_10x9_d5 | `bin/bipgen 10 9 51:51 5:5 6:6` | 1/1 | 0 | - | 7 | COMPLETE |
| n19_e50_10x9 | `bin/bipgen 10 9 50:50 4:4 6:6 {r}/{mod}` | 50/50 | 0 | - | 855 | COMPLETE |
| n19_e50_9x10 | `bin/bipgen 9 10 50:50 4:4 6:6 {r}/{mod}` | 50/50 | 0 | - | 568 | COMPLETE |
| wh_n17_e44_8x9 | `bin/bipgen -P -q 8 9 44:44 4:4 6:6 \| bin/h4filt` | 1/1 | 0 | 14,087,019 (with H 14,087,019) | 53 | COMPLETE |
| wh_n18_e47_10x8 | `bin/bipgen -P -q 10 8 47:47 4:4 6:6 \| bin/h4filt` | 1/1 | 0 | 8,584,858 (with H 8,584,858) | 21 | COMPLETE |
| wh_n19_e51_10x9_d5 | `bin/bipgen -P -q 10 9 51:51 5:5 6:6 \| bin/h4filt` | 1/1 | 0 | 10,055,368 (with H 10,055,368) | 109 | COMPLETE |
| wh_n18_e47_9x9 | `bin/bipgen -P -q 9 9 47:47 4:4 6:6 {r}/{mod} \| bin/h4filt` | 200/200 | 0 | 1,316,086,566 (with H 1,316,086,566) | 3,447 | COMPLETE |

Total user CPU of the detached jobs: 5,151 s (1.43 core-h).

| n | e | min degree | sides | pruned runs (own generator + decider) | whole class, no pruning (own generator, every graph decided by h4filt) | method 1 class count (plain genbg) | verdict |
|---|---|---|---|---|---|---|---|
| 17 | 44 | >= 4 | 8+9 | pr_n17_e44_8x9: 0 graphs; pr_n17_e44_9x8: 0 graphs | 14,087,019 generated, 0 without H; = method 1: yes | 14,087,019 | EMPTY |
| 18 | 47 | >= 4 | 8+10 | pr_n18_e47_8x10: 0 graphs; pr_n18_e47_10x8: 0 graphs | 8,584,858 generated, 0 without H; = method 1: yes | 8,584,858 | EMPTY |
| 18 | 47 | >= 4 | 9+9 | pr_n18_e47_9x9: 0 graphs | 1,316,086,566 generated, 0 without H | - | EMPTY |
| 19 | 50 | >= 4 | 9+10 | n19_e50_10x9: 0 graphs; n19_e50_9x10: 0 graphs | - | - | EMPTY |
| 19 | 51 | >= 5 | 9+10 | pr_n19_e51_9x10_d5: 0 graphs; pr_n19_e51_10x9_d5: 0 graphs | 10,055,368 generated, 0 without H; = method 1: yes | 10,055,368 | EMPTY |

Chain (rules in EX-B.md section 3; ex(16) = 40 from `data/chain.txt`):
- ex(17) = 43: yes
- ex(18) = 46: yes
- ex(19) = 49: yes
<!-- COLLECT:END -->

**Verdict: the two methods agree.** Method B finds no counted graph at any of the five levels, in
both class orders, and at four of the five it also decides every graph of the whole class without
pruning (1,348,813,811 graphs in all, every one with a 4-regular subgraph). With its own chain
(section 3: ex(16) = 40, built up from n = 8 with no census input) this gives **ex(17) = 43,
ex(18) = 46 and ex(19) = 49**, as method 1 found. All three whole-class counts that method 1 reports
are reproduced exactly. There is no disagreement, so no graph needed a third-way certificate. With
ex(n) = ⌊n²/4⌋ ≤ 3n − 8 for 4 ≤ n ≤ 7 and the chain values for 8 ≤ n ≤ 16, method B alone gives
QB(7) (e ≥ 3n − 7 forces a nonempty 4-regular subgraph) for 4 ≤ n ≤ 19, as method 1 does.

## 2. What method B shares with method 1

| Piece | Method 1 (wave6/excensus) | Method B (this lane) |
|---|---|---|
| Generator | nauty 2.8.9 genbg with a PRUNE1 hook (`genbg_q4`) | own program `code/bipgen.c`: canonical augmentation by class-B vertices with its own canonicity rule (minimum degree, then sum of neighbor degrees, then the last vertex of a nauty canonical labeling) and its own feasibility cuts. It links the nauty 2.9.3 core library (`densenauty`) for automorphism groups and canonical labels only; no genbg or geng code. |
| Decider | `q4core.h` inside the generator; pysat CaDiCaL with `validate_sat.py`'s encoding; glucose4 DRAT | own exhaustive search `code/h4.h` (each positive answer is checked against the subgraph it found); own CNF in `code/deciders.py` on PySAT Minisat 2.2 (Glucose 4 as a second solver on the witnesses); a flow method (a 4-factor test on balanced vertex subsets of the 4-core) |
| Upper-bound argument | Lemma A with the census base c(n') for n' ≤ 16 and census F1(17), F1(18); Lemma B at n = 19 | Lemma B and edge deletion only, chained from ex(7) = 12; every level n = 8 to 19 re-run here; no census input |
| Lower bounds | `code/witness.py` graphs, n = 15 to 20 | method 1's witnesses re-checked three ways, and own witnesses found by bipgen for every n = 8 to 19 |
| In common | nauty (as a library), the machine, the problem statement | |

geng -b was tried first (`code/build.sh` builds `geng_h4`, geng 2.9.3 with h4.h as its PRUNE hook).
It is correct where checked (n = 11 to 14 against the census lane's files, `data/pipecheck/`), but too slow
for these levels: one 1/50 shard of plain `geng -b -d4 -D6 17 44:44` was still running after 194 s of
CPU (method 1 did the whole level in 30 s with genbg), and the hook cut almost nothing before the last
level, because geng adds a vertex of maximum degree last and its intermediate graphs are sparse
(n = 14: 7,823 of its 7,991 cuts at the final level). Hence bipgen, which adds whole class-B
neighborhoods, largest degree first.

## 3. The argument, re-derived

Call G *counted* if it is simple, bipartite, Δ(G) ≤ 6 and has no nonempty 4-regular subgraph. Every
subgraph of a counted graph is counted.

**Lemma B (one deletion).** A counted G on n ≥ 2 vertices with e edges has δ(G) ≥ e − ex(n − 1).
Proof: for a vertex v of minimum degree, G − v is counted, on n − 1 vertices, with e − δ(G) edges, so
e − δ(G) ≤ ex(n − 1). ∎ The proof uses only an upper bound on ex(n − 1).

**Edge deletion.** If no counted graph on n vertices has exactly e edges, none has more: deleting
edges of a counted graph leaves a counted graph on the same vertices. So ex(n) < e.

**Chain step.** Suppose ex(n − 1) ≤ 3n − 11. A counted graph with 3n − 7 edges has δ ≥ 4 (Lemma B). So
if the class (n, e = 3n − 7, δ ≥ 4) has no counted graph, then ex(n) ≤ 3n − 8 by edge deletion, and a
counted witness with 3n − 8 edges gives ex(n) = 3n − 8. This is method 1's Lemma B corollary with one
simplification: its second condition (no counted graph with δ ≥ 5 and e = 3n − 6) follows from the
first by edge deletion, so it is a cross-check, not a requirement (method 1 needs it at n = 20 only
because e = 53 was not run there). Lemma B also gives method 1's other two consequences: e ≥ 3n − 5
forces δ ≥ 6, so G is 6-regular, a union of six perfect matchings (König), four of which form a
4-regular subgraph; e = 3n − 6 forces δ ≥ 5.

**Lemma A (peeling), checked.** For n ≥ 6, ex(n) ≤ max(3n − 9, max over 1 ≤ n' ≤ n of
c(n') + 3(n − n')), where c(n') is the largest edge count of a counted graph on n' vertices with
δ ≥ 4. Proof: delete vertices of degree at most 3 one at a time; each deletion removes at most 3
edges. If n' ≥ 1 vertices remain, they induce a counted graph with δ ≥ 4, so e ≤ c(n') + 3(n − n').
If none remain, in reverse deletion order each vertex has at most 3 neighbors earlier in the order,
and the first six induce a bipartite graph with at most 9 edges, so e ≤ 9 + 3(n − 6) = 3n − 9. ∎
Method 1's statement and proof are correct as written. Method B does not use Lemma A, so it needs
neither the base c(n') ≤ 3n' − 8 nor the census F1(17), F1(18).

**Base.** ex(n) = ⌊n²/4⌋ for n ≤ 7: every bipartite graph on at most 7 vertices has Δ ≤ 6 and no
nonempty 4-regular subgraph (that needs at least 4 vertices on each side). So ex(7) = 12 (K_{3,4}).

**Sides.** With δ ≥ t, each color class S satisfies t|S| ≤ e ≤ 6|S| (every edge has one end in S).
n = 17, e = 44, t = 4: |S| in [8, 11], so 8 + 9 only. n = 18, e = 47: 8 + 10 and 9 + 9. n = 19,
e = 50: |S| in [9, 12], so 9 + 10 only. n = 19, e = 51, t = 5: |S| in [9, 10], so 9 + 10. These
agree with method 1.

**Connected, so colored = uncolored.** In every class above each graph is connected. With δ ≥ 4 a
component has at least 4 vertices on each side, at least 8 vertices, and a component with 8, 9, 10
or 11 vertices has at most 16, 20, 25 or 30 edges (K_{4,4}; K_{4,5}; K_{5,5}; 5 + 6 with Δ ≤ 6). Two
components would carry at most 36 edges at n = 17 (8 + 9), 41 at n = 18 (8 + 10; 9 + 9 gives 40) and
46 at n = 19 (8 + 11; 9 + 10 gives 45), all below 44, 47 and 50; with δ ≥ 5 a component has at least
10 vertices, so n = 19 has one. A connected bipartite graph has one bipartition, so for unequal sides
each uncolored graph has exactly one coloring with the given class order: colored counts (genbg,
bipgen) equal uncolored counts. For 9 + 9, colored = 2U − S, where U is the uncolored count and S
the number of graphs with an automorphism that swaps the sides. The whole-class runs confirm
connectivity directly: h4filt tallies every generated graph by components (`>S ... conn=1`).

## 4. Validation of the tools

| Check | Result | Where |
|---|---|---|
| h4 search (C) against own CNF (PySAT) on 53,654 graphs per seed, two seeds: the census lane's 23,094 graphs at n = 15, 4,000 of them plus one edge, 20,000 random bipartite (some with Δ = 7), 5,000 random general graphs, 1,500 small bipartite graphs (also decided by flow) and 60 tiny ones (also by brute force) | 0 disagreements; graph6 coder identical to networkx | `code/selftest.py`, `logs/selftest_585.txt`, `logs/selftest_20261006.txt` |
| Deciders on members of the real classes: 7,012 sampled graphs (2,000 per level, except 23 at 8 + 10 and 989 at e = 51; every one has a 4-regular subgraph), each peeled by random edge deletion to the first graph without one (7,012 boundary pairs at n = 17 to 19, 39 to 44 edges on average); C and SAT on all, flow on a subset | 0 disagreements | `code/samplecheck.py`, `data/SAMPLECHECK.txt` |
| bipgen against nauty genbg 2.9.3: whole-class counts of 304 small classes (2 ≤ n1 ≤ 7, 1 ≤ n2 ≤ 7, seven degree settings, plus ten δ ≥ 4 or δ ≥ 5 classes up to 16 vertices) | all 304 equal | `code/gencheck.py`, `logs/gencheck_quick.txt` |
| bipgen res/mod shards | each split sums to the unsplit count (3 classes) | same |
| bipgen pruned output against the whole class run through h4filt (5 classes, up to 352,860 graphs) | same multisets of canonical forms (labelg) | same |
| bipgen pruned output against the census lane's genbg_q4 files `q4free_bg_7x7_d4.g6`, `q4free_bg_7x8_d4.g6` | identical multisets of canonical forms (485; 24,231) | `data/census_bg_compare.txt` |
| geng + h4 against the census lane's files at n = 11, 12, 13 (e 28..31), 14 (e 30..33) | same sets (3; 4; 124; 290) | `data/pipecheck/` |
| bipgen whole-class counts at the target levels against method 1's plain genbg counts | 14,087,019; 8,584,858; 10,055,368: all equal | section 5 |

## 5. Per-level results and reconciliation

### 5.1 The chain, n = 8 to 19 (`code/chain.py`, `data/chain.txt`)

At each n the search runs (n, e, δ ≥ e − ex(n − 1)) for e = ex(n − 1) + 1 upward, over every side
split that t|S| ≤ e ≤ 6|S| allows, stopping at the first graph found (`bipgen -1`); the first empty
e gives ex(n) = e − 1, and the graph found at e − 1 is the witness (checked by the PySAT decider).

| n | ex(n) | Empty level (e, δ ≥, splits) | Witness |
|---|---|---|---|
| 8 | 15 | 16, ≥ 4, 4 + 4 | `data/chain_witness_n8_e15.g6` |
| 9 | 18 | 19, ≥ 4, no split possible | `..._n9_e18.g6` |
| 10 | 21 | 22, ≥ 4, 5 + 5 | `..._n10_e21.g6` |
| 11 | 25 | 26, ≥ 5, no split possible | `..._n11_e25.g6` |
| 12 | 28 | 29, ≥ 4, 5 + 7 and 6 + 6 | `..._n12_e28.g6` |
| 13 | 31 | 32, ≥ 4, 6 + 7 | `..._n13_e31.g6` |
| 14 | 34 | 35, ≥ 4, 6 + 8 and 7 + 7 | `..._n14_e34.g6` |
| 15 | 37 | 38, ≥ 4, 7 + 8 | `..._n15_e37.g6` |
| 16 | 40 | 41, ≥ 4, 7 + 9 and 8 + 8 | `..._n16_e40.g6` |
| 17 | 43 | 44, ≥ 4, 8 + 9 | `..._n17_e43.g6` |
| 18 | 46 | 47, ≥ 4, 8 + 10 and 9 + 9 | `..._n18_e46.g6` |
| 19 | 49 | 50, ≥ 4, 9 + 10 (detached jobs) | `..._n19_e49.g6` |

This matches method 1 wherever both say something: its ex(16) ≤ 40 (Lemma A on the census base) and
its c(n') maxima 25, 26, 31, 33, 37 at n' = 11 to 15, which sit at or below these ex values.

### 5.2 Per level, both methods

| Level | Sides | Method 1: counted graphs (genbg_q4) | Method B: counted graphs (bipgen with h4 pruning) | Whole class, bicolored: method 1 plain genbg / method B `bipgen -P` | Method B: whole class decided graph by graph (h4filt) |
|---|---|---|---|---|---|
| n = 17, e = 44, δ ≥ 4 | 8 + 9 | 0, class orders 9 8 and 8 9 | 0, orders 8 9 and 9 8 | 14,087,019 / 14,087,019 | all 14,087,019 have a 4-regular subgraph |
| n = 18, e = 47, δ ≥ 4 | 8 + 10 | 0, both orders | 0, both orders | 8,584,858 / 8,584,858 | all have one |
| n = 18, e = 47, δ ≥ 4 | 9 + 9 | 0 (job A, 40 shards) | 0 (unsplit pilot, and 4 shards) | not counted / 1,316,086,566 | all have one (200 shards) |
| n = 19, e = 50, δ ≥ 4 | 9 + 10 | 0 (job B, order 9 10, 200 shards) | 0, order 9 10 (50 shards) and order 10 9 (50 shards) | not counted by either; of order 10^10 (one 1/2000 shard of order 9 10 holds at least 5.99 × 10^6) | not run |
| n = 19, e = 51, δ ≥ 5 | 9 + 10 | 0, both orders | 0, both orders | 10,055,368 / 10,055,368 (method B in both class orders: job wh_n19_e51_10x9_d5 and `logs/pilot/classcount_pilots.txt`) | all have one |

**Colored versus uncolored.** Both methods count bicolored graphs: an isomorphism must map each
class to itself (genbg's convention; bipgen reproduces genbg's counts, section 4). Every graph at
these levels is connected (section 3), and the whole-class runs confirm it: h4filt tallies all
1,348,813,811 graphs as connected, with the expected sides (`>S ... conn=1` in the shard logs). So
for 8 + 9, 8 + 10 and 9 + 10 the bicolored counts are also the uncolored counts. For 9 + 9 the
bicolored count 1,316,086,566 equals 2U − S, where U is the uncolored count and S the number of
graphs with an automorphism that swaps the sides; U and S were not computed, as method 1 has no
9 + 9 class count to compare. The counted-graph counts are 0 at
every level, colored and uncolored alike. Intermediate node counts are not comparable (different
generators and canonical rules), so only whole-class and output counts are reconciled.

## 6. Lower bounds (witnesses)

`code/witcheck.py`, `data/WITNESS-CHECK.txt`: each graph is checked for n, e = 3n − 8, bipartite
(own 2-coloring), Δ ≤ 6, and decided by h4filt, by the own CNF on Minisat 2.2 and on Glucose 4, and
by the flow method.

| Graph | n | e | Sides | δ, Δ | h4filt | SAT (Minisat 2.2 / Glucose 4) | Flow | Result |
|---|---|---|---|---|---|---|---|---|
| method 1 `wave6/excensus/data/witness_n15.g6` | 15 | 37 | 7 + 8 | 4, 6 | none | UNSAT / UNSAT | none | OK |
| method 1 `wave6/excensus/data/witness_n16.g6` | 16 | 40 | 7 + 9 | 3, 6 | none | UNSAT / UNSAT | none | OK |
| method 1 `wave6/excensus/data/witness_n17.g6` | 17 | 43 | 8 + 9 | 3, 6 | none | UNSAT / UNSAT | none | OK |
| method 1 `wave6/excensus/data/witness_n18.g6` | 18 | 46 | 8 + 10 | 3, 6 | none | UNSAT / UNSAT | none | OK |
| method 1 `wave6/excensus/data/witness_n19.g6` | 19 | 49 | 9 + 10 | 3, 6 | none | UNSAT / UNSAT | none | OK |
| method 1 `wave6/excensus/data/witness_n20.g6` | 20 | 52 | 10 + 10 | 3, 6 | none | UNSAT / UNSAT | none | OK |
| own `data/chain_witness_n17_e43.g6` | 17 | 43 | 8 + 9 | 3, 6 | none | UNSAT / UNSAT | none | OK |
| own `data/chain_witness_n18_e46.g6` | 18 | 46 | 8 + 10 | 3, 6 | none | UNSAT / UNSAT | none | OK |
| own `data/chain_witness_n19_e49.g6` | 19 | 49 | 9 + 10 | 3, 6 | none | UNSAT / UNSAT | none | OK |

The own witnesses were found by bipgen itself (first graph at the level, `-1`); their 4-cores have
13 vertices against 15 for method 1's, so they are different graphs. The lower bounds ex(n) ≥ 3n − 8
for n = 17, 18, 19 therefore have two independent witnesses each.

## 7. Cost

| Item | Core-s |
|---|---|
| Detached jobs (collector sum of user CPU, 313 shards; launched 10:18:16, ended 10:48:31 EDT) | 5,151 |
| Foreground: geng pilot (stopped, 194), bipgen pilots (163), class-count pilots (186), chain twice (141), generator checks twice (100), sample check (79), self-tests (34), witness and census comparisons and collector runs (about 10) | about 900 |
| n = 20, e = 53 pricing pilots (below) | about 290 |
| Total | about 6,300 (1.8 core-h), inside the 10 core-h guide |

Parallelism: at most 4 worker processes before 11:00, and 3 while a foreground check ran, apart from
checks of a few seconds. The whole-class shards are two-process pipelines of about 1.3 cores each;
for about a minute four of them overlapped (about 5 cores) before the cap was set to 3 pipelines
(`data/WORKERS`, logged in `logs/driver.log`). The load average was 46 to 64 on 18 cores.

**Not part of this job, priced only (`logs/price20/`).** With ex(19) = 49, Lemma B leaves n = 20,
e = 53 with δ ≥ 4, sides 9 + 11 or 10 + 10 (method 1, EX.md section 5: over budget, at least 480,000
core-s for 10 + 10 with genbg_q4). bipgen pilot shards, fitted to t = P + W/mod: 10 + 10 took 118.5
and 120.5 s at 0/200 and 100/200, 15.4 and 13.1 s at 0/2000 and 1000/2000, so W is about 23,000
core-s (6.5 core-h, about 6.6 core-h with 200 shards); 9 + 11 in order 11 9 took 0.9 and 2.7 s at
0/200 and 100/200 and 0.6 s at 0/2000, so W is about 300 core-s. The 8 pilot shards (also order 9 11: 18.8 s at 0/2000, the slower order) found no graph
(partial, no conclusion). A run of about 7 core-h would settle ex(20) ∈ {52, 53} with method B's
tools; 10 + 10 has only one class order, so a second method there would need a different split or
generator.

## 8. Files

`code/h4.h` (decider), `code/bipgen.c` (generator), `code/h4filt.c` (decider on graph6 input),
`code/h4prune.c` (geng hook, not used for the results), `code/deciders.py` (graph6 coder, CNF, flow,
brute force), `code/sat4.py`, `code/chain.py`, `code/witcheck.py`, `code/selftest.py`,
`code/gencheck.py`, `code/samplecheck.py`, `code/pipecheck.sh`, `code/build.sh` and `code/BUILD.txt`
(SHA-256), `code/run_exb.sh` (driver), `code/jobs.tsv`, `code/queue.txt`, `code/collect.py`;
`data/` (chain, witnesses, checks, collector output), `logs/` (pilots, shards, driver log), `JOBS.md`,
`RESUME.md`.
