#!/bin/bash
# driver.sh: worker pool over data/order.txt (a fixed random order of the slices 0..9999).
# W workers (default 13). Stops claiming new slices at STOP_EPOCH or when the file STOP exists;
# at KILL_EPOCH it kills whatever is still running (those slices stay without a done marker).
# Resumable: rerun it; slices with a done marker are skipped.
set -u
D="$(cd "$(dirname "$0")/.." && pwd)"
W="${W:-13}"
export STOP_EPOCH="${STOP_EPOCH:-$(date -j -f '%Y-%m-%d %H:%M:%S' '2026-10-06 06:50:00' +%s)}"
KILL_EPOCH="${KILL_EPOCH:-$(date -j -f '%Y-%m-%d %H:%M:%S' '2026-10-06 06:58:00' +%s)}"
echo "$(date '+%F %T') driver start pid=$$ W=$W STOP_EPOCH=$STOP_EPOCH KILL_EPOCH=$KILL_EPOCH"
( while [ "$(date +%s)" -lt "$KILL_EPOCH" ]; do sleep 30; done
  echo "$(date '+%F %T') KILL_EPOCH reached: killing remaining workers"
  touch "$D/STOP"
  pkill -f "$D/code/run_shard.sh"; pkill -f "$D/code/s6n22 "; pkill -f "$D/code/sat_check.py" ) &
WD=$!
xargs -P "$W" -n 1 "$D/code/run_shard.sh" < "$D/data/order.txt"
echo "$(date '+%F %T') xargs finished (exit $?)"
kill "$WD" 2>/dev/null
"$HOME/.cache/erdos585/venv/bin/python" "$D/code/collect.py" > "$D/logs/collect_final.log" 2>&1
echo "$(date '+%F %T') driver done"
