#!/bin/bash
# B-1 calibration: every 5-regular graph on 14 vertices through pairc (mode f).
# 100 shards (geng res/mod), 5 pipelines at a time (each pipeline is about 1.5 cores).
# Usage: nohup nice -n 15 bash run_reg5_n14.sh > logs/driver_reg5_n14.log 2>&1 &
set -u -o pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
G="$HOME/.cache/erdos585/nauty2_9_3/geng"
P=[local path]
OUT="$HERE/data/reg5-n14"
LOG="$HERE/logs/reg5-n14"
mkdir -p "$OUT" "$LOG"
echo "start $(date '+%Y-%m-%d %H:%M:%S %Z')"
shasum -a 256 "$G" "$P"
export G P OUT LOG
seq 0 99 | xargs -P 5 -I{} /bin/bash -c '
  r={}
  if grep -q "^graphs=" "$LOG/part-$r.err" 2>/dev/null; then exit 0; fi
  { /usr/bin/time -p /bin/bash -c "\"$G\" -q -d5 -D5 14 $r/100 | \"$P\" f > \"$OUT/part-$r.g6\""; } 2> "$LOG/part-$r.err"
'
echo "end $(date '+%Y-%m-%d %H:%M:%S %Z')"
# Sum the shard summaries.
done_n=$(grep -l '^graphs=' "$LOG"/part-*.err | wc -l | tr -d ' ')
awk -F'[= ]' '/^graphs=/{g+=$2; p+=$4; f+=$6} /^user /{u+=$2} END{printf "shards_done=%s graphs=%d with_pair=%d pair_free=%d user_s=%.1f\n", "'"$done_n"'", g, p, f, u}' "$LOG"/part-*.err
cat "$OUT"/part-*.g6 | wc -l | awk '{print "pair_free_lines=" $1}'
