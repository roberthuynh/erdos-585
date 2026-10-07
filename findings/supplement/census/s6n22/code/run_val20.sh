#!/bin/bash
# Validation run: every bipartite 6-regular graph on 10+10 (genbg -X-2, shard r of 4) through s6n22.
# Usage: run_val20.sh r
set -u
D="$(cd "$(dirname "$0")/.." && pwd)"
G="$HOME/.cache/erdos585/nauty2_9_3/genbg"
r="$1"
"$G" -q -X-2 -d6:6 -D6:6 10 10 "$r/4" | "$D/code/s6n22" -p "$D/data/val/n20_$r" -s "$r" -q
echo "exit ${PIPESTATUS[*]}"
