#!/bin/bash
# sat_stalls.sh [jobs]: after the run, decide every stalled AM-sample test (data/stall_frames.txt) by
# SAT (code/sat_check.py), in parallel chunks under nice 10. Writes data/stall_sat/{chunk_*,SUMMARY.txt};
# collect.py then reports the totals in RESULT.md. Expected cost: about 4 ms per line.
set -u
D="$(cd "$(dirname "$0")/.." && pwd)"
J="${1:-8}"
PY="$HOME/.cache/erdos585/venv/bin/python"
"$PY" "$D/code/collect.py" > /dev/null
O="$D/data/stall_sat"
mkdir -p "$O"
awk '{print $2, substr($3,3), substr($4,3)}' "$D/data/stall_frames.txt" > "$O/all.txt"
n=$(wc -l < "$O/all.txt")
per=$(( (n + J - 1) / J ))
[ "$per" -lt 1 ] && per=1
( cd "$O" && split -l "$per" all.txt chunk_ )
for c in "$O"/chunk_??; do
  nice -n 10 "$PY" "$D/code/sat_check.py" "$c" "$c.jsonl" --seconds 600 > "$c.log" 2>&1 &
done
wait
cat "$O"/chunk_??.log | awk '{for (i = 1; i <= NF; i++) {split($i, a, "="); s[a[1]] += a[2]}}
  END {printf "lines=%d SPAN=%d NOSPAN=%d TIMEOUT=%d witness_fail=%d candidate_failure=%d sec=%.1f\n",
       s["lines"], s["SPAN"], s["NOSPAN"], s["TIMEOUT"], s["witness_fail"], s["candidate_failure"], s["sec"]}' > "$O/SUMMARY.txt"
cat "$O/SUMMARY.txt"
"$PY" "$D/code/collect.py"
