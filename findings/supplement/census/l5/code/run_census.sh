#!/bin/bash
# L5B census driver. Run with bash (not zsh):  JOBS=6 nice -n 10 bash code/run_census.sh all
# Per shard: geng -b -d4 -D6 n 3n-5:3n-5 [r/mod] | l5b_sat.py | gzip  ->  verify.py.
# Restart-safe: a shard with a .done file is skipped; partial outputs are written to .tmp and renamed.
# Stage-0 counts (unsplit geng -u) are tasks "count n".
set -u
L5B="$(cd "$(dirname "$0")/.." && pwd)"
G="$HOME/.cache/erdos585/nauty2_9_3/geng"
PY="$HOME/.cache/erdos585/venv/bin/python"
D="$L5B/data/census"
LOGF="$L5B/logs/shards.log"
mkdir -p "$D" "$L5B/logs"

stamp() { date '+%Y-%m-%d %H:%M:%S %Z'; }

one() {
  local n=$1 mod=$2 r=$3
  local e=$((3 * n - 5))
  local base="$D/n${n}_m${mod}_r${r}"
  [ -f "$base.done" ] && return 0
  local t0 t1
  t0=$(date +%s)
  echo "$(stamp) start n=$n $r/$mod" >> "$LOGF"
  local split=()
  [ "$mod" -gt 1 ] && split=("$r/$mod")
  "$G" -b -d4 -D6 "$n" "$e:$e" ${split[@]+"${split[@]}"} 2> "$base.geng.err" \
    | "$PY" "$L5B/code/l5b_sat.py" --solver m22 --label "n$n $r/$mod" --summary "$base.sat.json" \
        2> "$base.sat.err" \
    | gzip -9 > "$base.out.gz.tmp"
  local rc=("${PIPESTATUS[@]}")
  if [ "${rc[0]}" != 0 ] || [ "${rc[1]}" != 0 ] || [ "${rc[2]}" != 0 ]; then
    echo "$(stamp) FAIL n=$n $r/$mod rc=${rc[*]}" >> "$LOGF"
    return 1
  fi
  mv "$base.out.gz.tmp" "$base.out.gz"
  if ! "$PY" "$L5B/code/verify.py" "$base.out.gz" --exceptions "$base.exc" > "$base.verify.json.tmp" \
        2> "$base.verify.err"; then
    echo "$(stamp) VERIFY-FAIL n=$n $r/$mod" >> "$LOGF"
    return 1
  fi
  mv "$base.verify.json.tmp" "$base.verify.json"
  t1=$(date +%s)
  echo "wall_seconds=$((t1 - t0))" > "$base.done"
  echo "$(stamp) done n=$n $r/$mod wall=$((t1 - t0))s" >> "$LOGF"
}

count() {
  local n=$1
  local e=$((3 * n - 5))
  local f="$D/count_n${n}.txt"
  [ -s "$f" ] && return 0
  "$G" -u -b -d4 -D6 "$n" "$e:$e" > "$f.tmp" 2>&1 && mv "$f.tmp" "$f"
  echo "$(stamp) count n=$n: $(cat "$f")" >> "$LOGF"
}

case "${1:-}" in
  one) one "$2" "$3" "$4" ;;
  count) count "$2" ;;
  all)
    JOBS="${JOBS:-6}"
    echo "$(stamp) driver start pid=$$ jobs=$JOBS" >> "$LOGF"
    {
      for r in $(seq 0 63); do echo "one 17 64 $r"; done
      for r in $(seq 0 7); do echo "one 16 8 $r"; done
      for n in 5 6 7 8 9 10 11 12 13 14 15; do echo "one $n 1 0"; done
      for n in 15 16 17; do echo "count $n"; done
    } | xargs -P "$JOBS" -L 1 bash "$0"
    echo "$(stamp) driver end pid=$$" >> "$LOGF"
    ;;
  *) echo "usage: bash run_census.sh all | one n mod r | count n" >&2; exit 2 ;;
esac
