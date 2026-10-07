# 5-regular pair-free graphs on 16 vertices (reg5n16 lane)

Written by `code/collect.sh` at 2026-10-06 11:42:55 EDT. Rung (b), computed, not reviewed.
A pair is two edge-disjoint cycles on the same vertex set.

## Verdict

NONE AT ALL: the census completed (all 20000 shards) and no 5-regular graph on 16 vertices is pair-free. So the least order of a 5-regular pair-free graph is 18.

## Method

- Generator: nauty 2.9.3 `geng -d5 -D5 16 r/20000`, compiled with `-DPRUNE=pairprune`
  (`code/pairprune.c`, built by `code/build.sh` into `code/geng_pp`). geng adds vertices
  0,1,2,... and calls PRUNE on every intermediate graph only after its induced parent passed, so a
  new pair must contain the newest vertex. PRUNE rejects a graph that has a pair through that vertex.
  Pair-freeness is closed under induced subgraphs, so the output of each shard is exactly the
  pair-free 5-regular graphs of that shard. One counting test is added for the 5-regular target
  (it never fired in the pilots).
- Pair test: every S containing the vertex with min degree >= 4 in G[S] (closure enumeration in
  the 4-core), every perfect matching M of the degree-5 vertices of G[S], and a search for a
  decomposition of the 4-regular G[S] - M into two Hamilton cycles.
- Validation (LOG.md): the standalone decider `code/pairdec` (same pair test) agrees with
  `pairc` graph by graph on all graphs with 3 <= degree <= 5 on 9, 10 and 11 vertices
  (4,018,267 at n = 11), and says NONE on all 120 known 18-vertex pair-free graphs (glue18). The
  pruned geng output equals `geng | pairc f` as canonical sets on 8 parameter sets, and it
  reproduces the B-1 ladder counts 15, 1,765, 1,501 and 0 (n = 9, 10, 11) and 344,388 at
  n = 12, e = 28 (0 at e = 29, 30). `geng_pp -d5 -D5 n` gives 0 at n = 10 and 12.
- Pilot (03:37 EDT): six shards of mod 20000 took 12.3-13.6 s each. Per shard, about 1.04M
  14-vertex graphs pass the pair test and about 2.09M 15-vertex children are generated, 99.99%
  of them with a pair through the new vertex. geng's own generation is about 80% of the time.
  The whole census is about 250k core-seconds, about 4.7 h on 16 workers, so it could not finish
  before 06:10. Five speed-ups were tried and none gave the 2.3x needed (LOG.md).
- Shards: geng res/mod with mod 20000, run in the shuffled order `data/shard_order.txt`
  (seed 585). A shard counts as covered only when geng finished with its >Z line
  (`logs/shards/<r>.done`). The union of all 20000 shards is every 5-regular graph on 16 vertices.

## Coverage and counts

- Shards completed: 20000 of 20000 (100.00%). List: `data/done_shards.txt`.
- Shards killed or failed and not covered (rerun them to cover): 0 (`data/incomplete_shards.txt`).
- Pair-free 5-regular graphs output by completed shards: 0.
- Work in completed shards: cpu_s=292701 outputs=0 , summed shard wall time 308813s.
- level 12: 34958529 graphs reached PRUNE, 12684 rejected for a pair
- level 13: 1523699357 graphs reached PRUNE, 655700 rejected for a pair
- level 14: 20477302506 graphs reached PRUNE, 273656696 rejected for a pair
- level 15: 40908057114 graphs reached PRUNE, 40902952184 rejected for a pair
- level 16: 378597 graphs reached PRUNE, 378597 rejected for a pair

## Structured side results (complete for each named family)

    Complete searches of natural subfamilies (5-regular graphs on 16 vertices), run 04:06-04:09 EDT:
    - Triangle-free (geng -t): 388 graphs (plain geng -t -d5 -D5 16, 3.1 s). pairc: 388 with a pair, 0 pair-free; pairdec: the same. Pruned geng_pp -t: 0 outputs (3.4 s). Files: data/struct/trianglefree-all.g6, logs/struct/trianglefree*.
    - Bipartite (geng -b): 41 graphs. pairc: 41 with a pair. Pruned geng_pp -b: 0 outputs. Files: data/struct/bipartite-all.g6, logs/struct/bipartite-all.err.
    - Square-free (geng -f, no 4-cycle): no 5-regular graph on 16 vertices exists.
    - Small edge cuts: CALIBRATION.md R3 (wave3 census) already shows that a 5-regular pair-free graph on 16 vertices has no edge cut of at most 3 edges (it relies on the B-1 ladder values L5(8) = -2 and L5(12) = -1.5).
    - K4-free (geng -k) was piloted and is too large for tonight: shard 0/2000 ran over 120 s.

## Files

- `code/`: pairprune.c, build.sh, driver.sh, worker.sh, collect.sh, validate_prune.sh.
- `logs/shards/`: per-shard stderr (geng >Z, >S and per-level >L lines) and .done markers.
- `data/out/<r>.g6`: per-shard output (empty when nothing was found).
