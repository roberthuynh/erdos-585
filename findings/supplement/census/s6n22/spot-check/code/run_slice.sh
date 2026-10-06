#!/bin/bash
# run_slice.sh r mode (wave8/s6spot). Regenerates slice r/10000 with the original's genbg flags
# into data/slices/s<r>.g6, runs e10cut (exact min essential cut of every graph), then
#   mode full:    spantest.py on every E10 graph, all 66 edges (SAT, witnesses verified)
#   mode e10only: spantest.py only on the graphs that are not E10 (the 3 known non-E10 slices)
# and writes the done marker s<r>.done last. A slice with a done marker is skipped.
set -u
D="$(cd "$(dirname "$0")/.." && pwd)"
G="$HOME/.cache/erdos585/nauty2_9_3/genbg"
PY="$HOME/.cache/erdos585/venv/bin/python"
r="$1"; mode="$2"
[ -e "$D/STOP" ] && exit 0
[ "$(date +%s)" -ge "${STOP_EPOCH:-9999999999}" ] && exit 0
P="$D/data/slices/s$r"
[ -e "$P.done" ] && exit 0
fail() { echo "$(date '+%F %T') r=$r mode=$mode FAILED: $1" >> "$D/logs/failed.txt"; exit 1; }
t0=$(date +%s)
"$G" -X-3 -d6:6 -D6:6 11 11 "$r/10000" "$P.g6" 2> "$P.genbg.err" || fail genbg
t1=$(date +%s)
"$D/code/e10cut" -r 6 -b 11 "$P.g6" > "$P.cut" 2> "$P.e10.err" || fail e10cut
t2=$(date +%s)
if [ "$mode" = full ]; then
  "$PY" "$D/code/spantest.py" "$P.g6" "$P.cut" "$P" > "$P.span.log" 2>&1 || fail spantest
else
  "$PY" "$D/code/spantest.py" "$P.g6" "$P.cut" "$P" --only-non-e10 > "$P.span.log" 2>&1 || fail spantest
fi
t3=$(date +%s)
echo "mode=$mode genbg_s=$((t1 - t0)) e10_s=$((t2 - t1)) span_s=$((t3 - t2)) start=$t0 end=$t3" > "$P.done"
echo "$(date '+%F %T') r=$r mode=$mode done genbg_s=$((t1 - t0)) e10_s=$((t2 - t1)) span_s=$((t3 - t2))" >> "$D/logs/progress.log"
