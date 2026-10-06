#!/bin/bash
# L5B superset checks: geng run with a degree flag dropped, the class counted by the exact filter
# (code/superset_filter.py). Sequential, restart-safe (skips outputs that exist).
#   n = 9..15 : geng -b n 3n-5:3n-5            (no degree flags at all)
#   n = 16    : geng -b -D6 ... and geng -b -d4 ...   (one flag dropped each)
#   n = 17    : geng -b -D6 17 46:46, 4 shards  (min-degree flag dropped)
# Run with bash:  nohup nice -n 15 bash code/run_superset.sh > logs/superset.out 2>&1 &
set -u
L5B="$(cd "$(dirname "$0")/.." && pwd)"
G="$HOME/.cache/erdos585/nauty2_9_3/geng"
PY="$HOME/.cache/erdos585/venv/bin/python"
D="$L5B/data/superset"
mkdir -p "$D"
run() {  # name, then geng arguments
  local name=$1
  shift
  [ -s "$D/$name.json" ] && return 0
  local t0
  t0=$(date +%s)
  "$G" "$@" 2> "$D/$name.geng.err" | "$PY" "$L5B/code/superset_filter.py" "$name: geng $*" > "$D/$name.json.tmp"
  local rc=("${PIPESTATUS[@]}")
  if [ "${rc[0]}" = 0 ] && [ "${rc[1]}" = 0 ]; then
    mv "$D/$name.json.tmp" "$D/$name.json"
    echo "$(date '+%Y-%m-%d %H:%M:%S %Z') superset $name done wall=$(( $(date +%s) - t0 ))s" >> "$L5B/logs/shards.log"
  else
    echo "$(date '+%Y-%m-%d %H:%M:%S %Z') superset $name FAIL rc=${rc[*]}" >> "$L5B/logs/shards.log"
  fi
}
for n in 9 10 11 12 13 14 15; do
  e=$((3 * n - 5))
  run "n${n}_noflags" -b "$n" "$e:$e"
done
run n16_D6only -b -D6 16 43:43
for r in 0 1 2 3; do
  run "n17_D6only_r${r}of4" -b -D6 17 46:46 "$r/4"
done
run n16_d4only -b -d4 16 43:43
echo "$(date '+%Y-%m-%d %H:%M:%S %Z') superset script end" >> "$L5B/logs/shards.log"
