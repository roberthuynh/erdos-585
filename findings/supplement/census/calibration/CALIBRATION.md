# B-1 calibration: what degree 5 says about the degree-6 census

Wave 3 census lane, 2026-10-05 (CONTINUE.md step B4; 585-RESEARCH-PLAN.md §5, B-1). Rung (b),
computed. Nothing here is reviewed. A "pair" is two edge-disjoint cycles on the same vertex set.

Tools: nauty 2.9.3 `geng` (`~/.cache/erdos585/nauty2_9_3/geng`, SHA-256 `588052a8…7fdaca1`),
`pairc` (`reports/585-fable/tools/pairc`, SHA-256 `a8a4af8e…6c611366`, complete enumeration), and
the second decider `pair_oracle.py` (`reports/585-fable-wildcard/tools/`, PySAT; every PAIR answer is
replayed by `crosscheck_oracle.py`). Commands, logs and data are in this folder (LOG.md lists them).

## 1. Results

**R1. No 5-regular graph on at most 14 vertices is pair-free.** Command: `geng -q -d5 -D5 n | pairc f`.

| n | 5-regular graphs | pair-free | pairc run | second method (pair_oracle) |
|---|---|---|---|---|
| 6 | 1 | 0 | `logs/reg5-n6.err` | |
| 8 | 3 | 0 | `logs/reg5-n8.err` | |
| 10 | 60 | 0 | `logs/reg5-n10.err` | |
| 12 | 7,849 | 0 | `logs/reg5-n12.err` | 7,849 PAIR, witnesses replayed (`logs/xc/reg5-n12.oracle.summary.txt`) |
| 14 | 3,459,386 | 0 | 100 shards, 810.6 core-s (`logs/driver_reg5_n14.log`) | see the note below the table |

The n = 12 count is 7,848 connected graphs (`geng -c`) plus 2K6. Odd orders have no 5-regular graph.
The n = 14 second-method run (`run_xc_reg5_n14.sh`, log `logs/driver_xc_reg5_n14.log`) was still
running when this file was written. LOG.md has its final line.

**R2. The Δ ≤ 5 level ladder.** The level of a graph is e − 5n/2, and its deficiency is
5n − 2e = −2·level. The command is `geng -q -d3 -D5 n e:e | pairc f`, with e running down from ⌊5n/2⌋
and stopping at the first e that has a pair-free graph (`run_ladder.sh`). It is enough to search
δ ≥ 3. Deleting a vertex of degree d ≤ 2 raises the level by 5/2 − d ≥ 1/2 and keeps a graph pair-free.
So the maximum over all pair-free graphs with Δ ≤ 5 on at most n vertices, L5(n), is the running
maximum of the δ ≥ 3 column.

| n | max e (δ ≥ 3) | level | deficiency | graphs at that e | pair-free | levels above, all graphs with a pair | L5(n) |
|---|---|---|---|---|---|---|---|
| 4 | 6 | −4.0 | 8 | 1 | 1 (K4) | none exist | −4.0 |
| 5 | 9 | −3.5 | 7 | 1 | 1 | e = 10: 1 | −3.5 |
| 6 | 12 | −3.0 | 6 | 4 | 3 | e = 13, 14, 15: 2, 1, 1 | −3.0 |
| 7 | 15 | −2.5 | 5 | 14 | 8 | e = 16, 17: 5, 1 | −2.5 |
| 8 | 18 | −2.0 | 4 | 68 | 19 | e = 19, 20: 16, 3 | −2.0 |
| 9 | 21 | −1.5 | 3 | 276 | 15 | e = 22: 28 | −1.5 |
| 10 | 23 | −2.0 | 4 | 8,435 | 1,765 | e = 24, 25: 1,188, 60 | −1.5 |
| 11 | 26 | −1.5 | 3 | 56,071 | 1,501 | e = 27: 3,749 | −1.5 |
| 12 | 28 | −2.0 | 4 | 2,830,276 | 344,388 | e = 29, 30: 325,575, 7,849 | −1.5 |

The table comes from `logs/ladder/summary-n*.txt`, and the pair-free graphs are saved in
`data/ladder/n*-e*-pairfree.g6`. Whole orders were cross-checked with pair_oracle. At n = 9, e = 22
and e = 21 give 28 PAIR, then 261 PAIR plus 15 NOPAIR. At n = 11, e = 27 and e = 26 give 3,749 PAIR,
then 54,570 PAIR plus 1,501 NOPAIR. In both orders the NOPAIR set equals pairc's pair-free set, there
were no timeouts, and every witness replayed (`logs/xc/`).

Reading the ladder:
- From n = 4 to 9 the ladder rises by 1/2 per vertex, and this rise is automatic. Add a vertex of degree 3
  joined to three deficient vertices: deficiency drops by 1, and the graph stays pair-free, because a
  vertex of degree 3 lies in no pair. RegularFive's 8-vertex block is exactly this case: the 7-vertex
  double wheel without its hub edge (level −2.5), plus one vertex of degree 3.
- The climb stops at deficiency 3 (n = 9 and 11), and that stop is the first constraint the pair
  condition imposes. All 15 graphs at n = 9 have one vertex of degree 3 and one of degree 4. A
  (1,1,1) pattern would take one more degree-3 vertex and give a pair-free graph with n = 10, e = 24,
  and the census has none.

**R3. 5-regular pair-free graphs exist on 18 vertices.**
- *Cut lemma (FINDINGS.md §4.2 uses the same fact).* Suppose an edge cut has at most 3 edges. A pair
  whose vertex set meets both sides would cross the cut at least twice with each of its two edge-disjoint
  cycles, which takes at least 4 cut edges. So every pair lies on one side, and joining pair-free graphs
  by at most 3 edges gives a pair-free graph. That join adds c to the level.
- *Construction (`glue18.py`).* Take two 9-vertex ladder blocks A and B. In each, call the degree-3
  vertex a1 (b1) and the degree-4 vertex a2 (b2). Join them by a1b1, a1b2 and a2b1. The result is
  5-regular on 18 vertices with 45 edges.
- *Results.* The 225 ordered choices give 120 isomorphism classes (labelg), saved in
  `data/glue18/glue18-classes.g6`. pairc finds all 120 pair-free. pair_oracle without decomposition,
  which does not use the cut lemma, gives NOPAIR for all 120 (`logs/glue18.*`).
- *Uniqueness.* Given the ladder values, these 120 are all the 5-regular pair-free graphs on 18 vertices
  that have an edge cut of at most 3 edges:
  - Each side of a c-edge cut in a 5-regular graph is pair-free with Δ ≤ 5 and level −c/2.
  - c = 3 forces both sides to have 9 vertices, since L5(8) = −2.
  - Each side then has δ ≥ 3 (else deleting a vertex beats L5(8)), so it is one of the 15 graphs. The
    cut edges are then forced.
  - c ≤ 2 forces both sides to have at least 13 vertices, since L5(12) = −1.5.

So **the first order of a 5-regular pair-free graph is 16 or 18.** Previously the smallest in the
project's records was RegularFive on 32 vertices. The literature was not checked. The same argument shows that a 5-regular pair-free graph on 16 vertices, if
one exists, is 4-edge-connected. An unpruned n = 16 census covers about 2.6 billion graphs
(585-RESEARCH-PLAN.md §5 B-1), roughly 170 core-hours at the n = 14 rate, so it was not run. The old
pair-pruned geng filters (`triage/erdos585_geng_filter*.c`) stop at 11 or 12 vertices.

## 2. The degree-6 record it is compared with

At degree 6 the level is e − 3n and the deficiency is 6n − 2e.
- W1 (Δ ≤ 6 and e ≥ 3n − 4 force a pair) holds for n ≤ 14, with n = 13 replicated and n = 14 from one
  reviewed program.
- The least deficiency of a pair-free graph with Δ ≤ 6 is exactly 10 (level −5) for 7 ≤ n ≤ 14,
  attained by K2 ∨ C5 plus vertices of degree 3. Sources: `reports/585-fable-wildcard/REPORT.md` line
  75, and `reports/585-findings/FINDINGS.md` §4.3 lines 187-199 and appendix C lines 960-987.
- No 6-regular graph on at most 15 vertices is pair-free (FINDINGS.md lines 192, 198-199 and 988).
- Adding a vertex of degree 3 leaves e − 3n unchanged, so at degree 6 there is no automatic climb.

| | degree 5 | degree 6 |
|---|---|---|
| Least deficiency of a pair-free graph, small n | 3 for n = 9..12 (L5 = −1.5) | 10 for n = 7..14 (level −5) |
| Regular census | no avoider through n = 14 | no avoider through n = 15 |
| Smallest regular avoider | 18 (R3); none at 14 or below | none known |
| Smallest regular avoider with an edge cut of ≤ 3 edges, predicted from the ladder alone | 18, attained | at least 30 (see below) |
| Bipartite gadget (585-RESEARCH-PLAN.md §5 B-1, "Known already") | appears at 13 vertices | none through 17 vertices |

The degree-6 bound in the last-but-one row follows from W1. Take a 6-regular pair-free graph with an
edge cut of c ≤ 3 edges. Each side is pair-free with Δ ≤ 6 and has e = 3n − c/2 ≥ 3n − 4 edges, so
W1 forces each side to have at least 15 vertices. The bound is written here and has not been reviewed.

## 3. What this means for the degree-6 evidence

1. **The regular-graph census by itself is weak evidence.** At degree 5, checking every regular graph
   through 14 vertices finds no avoider, yet avoiders exist at 18. The plan's second branch applies to
   this part: "if they do not appear by 14, the degree-6 census says little". "Every 6-regular graph
   through 15 vertices has a pair" therefore says little on its own about larger 6-regular graphs.
2. **The level ladder is the informative part, and it worked as a predictor at degree 5.** The degree-5
   ladder reached deficiency 3 at n = 9. Deficiency 3 is the most a block can have and still be joined
   to a copy of itself across a cut that no pair crosses. From the n ≤ 12 ladder alone one predicts the
   smallest glued 5-regular avoider at 18 vertices, and it is there. Both known nonbipartite
   constructions are of this glued type, RegularFive and the 18-vertex graphs. FINDINGS.md §4.2 records
   that the 104-vertex bipartite avoider has no 4-edge-connected subgraph at all.
3. **At degree 6 the plateau is real evidence, against one kind of avoider.**
   - The least deficiency stays at 10 through n = 14, far above 3. So gluing small blocks across small
     cuts cannot reach a 6-regular graph: by the bound in §2, any 6-regular avoider with an edge cut of
     at most 3 edges has both sides of at least 15 vertices.
   - FINDINGS.md §4.2 lines 174-175 already notes that a 6-regular graph always has a 4-edge-connected
     subgraph, so the "no 4-edge-connected subgraph" certificate never exists at degree 6. The
     calibration makes this quantitative for cut-glued constructions.
4. **What the evidence does not cover.** It is silent on 6-regular avoiders that are 4-edge-connected,
   or whose small cuts all have large sides. Degree 5 cannot calibrate this case yet, because it is not
   known whether any 4-edge-connected 5-regular avoider exists. The smallest open instance is n = 16,
   and by R3 any example there is 4-edge-connected. This is the case CONTINUE.md §1 describes as a pure
   Hamilton-decomposition question.

Two measurements would calibrate this case (the lead's call; neither was run):
- the 5-regular census at n = 16 with a pair-pruned generator (new code, since the old filters stop at
  12 vertices);
- the least deficiency of 4-edge-connected pair-free graphs with Δ ≤ 6 at small n.

## 4. Compute

| Item | Core time |
|---|---|
| 5-regular census, n ≤ 14 (pairc) | 0.23 core-h |
| Ladder n ≤ 12 (pairc) | 0.02 core-h |
| pair_oracle cross-checks, n = 9, 11 and 5-regular n = 12 | < 0.05 core-h |
| pair_oracle on 5-regular n = 14 (detached) | about 3 core-h projected (see LOG.md) |
| glue18, control bank, T0 manifests | < 0.05 core-h |
