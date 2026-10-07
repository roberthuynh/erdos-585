#!/bin/bash
# Collector: writes REG5N16.md from logs/shards/*.done, logs/shards/*.err and data/out/*.g6.
# Usage: bash code/collect.sh [--quick]   (--quick skips the SAT certification of found graphs)
set -u
LANE="$(cd "$(dirname "$0")/.." && pwd)"
cd "$LANE" || exit 1
MOD=20000
QUICK=0; [ "${1:-}" = "--quick" ] && QUICK=1
PAIRC=[local path]
PY="$HOME/.cache/erdos585/venv/bin/python"
ORACLE=[local path]
/bin/ls logs/shards | grep '\.done$' | sed 's/\.done$//' | sort -n > data/done_shards.txt
ND=$(wc -l < data/done_shards.txt | tr -d ' ')
# Incomplete = shards logged as killed or failed that have no .done marker (a rerun may have covered them).
: > data/incomplete_shards.txt
if [ -f logs/incomplete.txt ]; then
  sed -n 's/.*shard=\([0-9]*\) .*/\1/p' logs/incomplete.txt | sort -un | while read -r s; do
    [ -f "logs/shards/$s.done" ] || echo "$s"; done > data/incomplete_shards.txt
fi
NI=$(wc -l < data/incomplete_shards.txt | tr -d ' ')
# Found graphs: only from done shards.
: > data/found.g6
while read -r r; do [ -s "data/out/$r.g6" ] && cat "data/out/$r.g6" >> data/found.g6; done < data/done_shards.txt
NF=$(grep -c . data/found.g6 | tr -d ' ')
# Work totals over done shards (per-level PRUNE calls and rejections; geng >Z cpu).
STATS=$(while read -r r; do cat "logs/shards/$r.err"; done < data/done_shards.txt | awk '
  /^>L /{ split($2,a,"="); split($3,b,"="); split($4,c,"="); n=a[2]; calls[n]+=b[2]; rej[n]+=c[2] }
  /^>Z /{ cpu+=$(NF-1); outs+=$2 }
  END{ printf "cpu_s=%.0f outputs=%d\n", cpu, outs;
       for (n=12;n<=16;n++) if (calls[n]) printf "level %d: %d graphs reached PRUNE, %d rejected for a pair\n", n, calls[n], rej[n] }')
WALL=$(cat logs/shards/*.done 2>/dev/null | sed -n 's/.*wall_s=\([0-9]*\).*/\1/p' | awk '{s+=$1} END{printf "%.0f", s}')
CERT="none needed (no graph found)"
if [ "$NF" -gt 0 ]; then
  "$PAIRC" f < data/found.g6 > data/found.pairc_free.g6 2> logs/found.pairc.err
  "$LANE/code/pairdec" f < data/found.g6 > data/found.pairdec_free.g6 2> logs/found.pairdec.err
  CERT="pairc: $(cat logs/found.pairc.err); pairdec: $(cat logs/found.pairdec.err)"
  if [ "$QUICK" -eq 0 ]; then
    "$PY" "$ORACLE" data/found.g6 --seconds 600 --jobs 2 > logs/found.sat.txt 2>&1
    CERT="$CERT; SAT (pair_oracle, decompose=False): $(grep '^SUMMARY' logs/found.sat.txt)"
    shasum -a 256 data/found.g6 data/found.pairc_free.g6 logs/found.sat.txt code/pairprune.c code/geng_pp > FROZEN.sha256
  else
    CERT="$CERT; SAT not yet run (rerun code/collect.sh without --quick)"
  fi
fi
if [ "$NF" -gt 0 ]; then
  VERDICT="FOUND: $NF pair-free 5-regular graph(s) on 16 vertices in the covered shards (data/found.g6). Certification: $CERT."
elif [ "$ND" -eq "$MOD" ]; then
  VERDICT="NONE AT ALL: the census completed (all $MOD shards) and no 5-regular graph on 16 vertices is pair-free. So the least order of a 5-regular pair-free graph is 18."
else
  VERDICT="NONE IN THE COVERED PART: $ND of $MOD shards completed with no output. The other $((MOD - ND)) shards were not run, so the question at 16 vertices stays open."
fi
cat > REG5N16.md <<MD
# 5-regular pair-free graphs on 16 vertices (reg5n16 lane)

Written by \`code/collect.sh\` at $(date '+%Y-%m-%d %H:%M:%S %Z'). Rung (b), computed, not reviewed.
A pair is two edge-disjoint cycles on the same vertex set.

## Verdict

$VERDICT

## Method

- Generator: nauty 2.9.3 \`geng -d5 -D5 16 r/$MOD\`, compiled with \`-DPRUNE=pairprune\`
  (\`code/pairprune.c\`, built by \`code/build.sh\` into \`code/geng_pp\`). geng adds vertices
  0,1,2,... and calls PRUNE on every intermediate graph only after its induced parent passed, so a
  new pair must contain the newest vertex. PRUNE rejects a graph that has a pair through that vertex.
  Pair-freeness is closed under induced subgraphs, so the output of each shard is exactly the
  pair-free 5-regular graphs of that shard. One counting test is added for the 5-regular target
  (it never fired in the pilots).
- Pair test: every S containing the vertex with min degree >= 4 in G[S] (closure enumeration in
  the 4-core), every perfect matching M of the degree-5 vertices of G[S], and a search for a
  decomposition of the 4-regular G[S] - M into two Hamilton cycles.
- Validation (LOG.md): the standalone decider \`code/pairdec\` (same pair test) agrees with
  \`pairc\` graph by graph on all graphs with 3 <= degree <= 5 on 9, 10 and 11 vertices
  (4,018,267 at n = 11), and says NONE on all 120 known 18-vertex pair-free graphs (glue18). The
  pruned geng output equals \`geng | pairc f\` as canonical sets on 8 parameter sets, and it
  reproduces the B-1 ladder counts 15, 1,765, 1,501 and 0 (n = 9, 10, 11) and 344,388 at
  n = 12, e = 28 (0 at e = 29, 30). \`geng_pp -d5 -D5 n\` gives 0 at n = 10 and 12.
- Pilot (03:37 EDT): six shards of mod 20000 took 12.3-13.6 s each. Per shard, about 1.04M
  14-vertex graphs pass the pair test and about 2.09M 15-vertex children are generated, 99.99%
  of them with a pair through the new vertex. geng's own generation is about 80% of the time.
  The whole census is about 250k core-seconds, about 4.7 h on 16 workers, so it could not finish
  before 06:10. Five speed-ups were tried and none gave the 2.3x needed (LOG.md).
- Shards: geng res/mod with mod $MOD, run in the shuffled order \`data/shard_order.txt\`
  (seed 585). A shard counts as covered only when geng finished with its >Z line
  (\`logs/shards/<r>.done\`). The union of all $MOD shards is every 5-regular graph on 16 vertices.

## Coverage and counts

- Shards completed: $ND of $MOD ($(awk "BEGIN{printf \"%.2f\", 100*$ND/$MOD}")%). List: \`data/done_shards.txt\`.
- Shards killed or failed and not covered (rerun them to cover): $NI (\`data/incomplete_shards.txt\`).
- Pair-free 5-regular graphs output by completed shards: $NF.
- Work in completed shards: $(echo "$STATS" | head -1 | tr '\n' ' '), summed shard wall time ${WALL}s.
$(echo "$STATS" | tail -n +2 | sed 's/^/- /')

## Structured side results (complete for each named family)

$(sed 's/^/    /' data/struct/SUMMARY.txt 2>/dev/null)

## Files

- \`code/\`: pairprune.c, build.sh, driver.sh, worker.sh, collect.sh, validate_prune.sh.
- \`logs/shards/\`: per-shard stderr (geng >Z, >S and per-level >L lines) and .done markers.
- \`data/out/<r>.g6\`: per-shard output (empty when nothing was found).
MD
echo "collect: done=$ND incomplete=$NI found=$NF"
