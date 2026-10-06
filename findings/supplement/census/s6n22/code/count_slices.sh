#!/bin/bash
# count_slices.sh slice...: genbg -u count and time for each slice r/10000 of -X-3 11+11 (pilot for the class count).
G="$HOME/.cache/erdos585/nauty2_9_3/genbg"
D="$(cd "$(dirname "$0")/.." && pwd)"
for r in "$@"; do
  "$G" -u -X-3 -d6:6 -D6:6 11 11 "$r/10000" > "$D/data/pilot/count/c_$r.txt" 2>&1
done
