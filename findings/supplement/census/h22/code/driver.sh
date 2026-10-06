#!/bin/bash
# usage: driver.sh N MOD PAR OUTDIR -- runs every pending shard 0..MOD-1, PAR at a time; restart-safe.
set -u
N="$1"; MOD="$2"; PAR="$3"; OUT="$4"
D="$(cd "$(dirname "$0")" && pwd)"
mkdir -p "$OUT/done" "$OUT/fail"
echo "$(date '+%F %T') driver start N=$N MOD=$MOD PAR=$PAR pid=$$"
seq 0 $((MOD-1)) | xargs -P "$PAR" -n 1 "$D/run_shard.sh" "$N" "$MOD" "$OUT"
ndone=$(/bin/ls "$OUT/done" | grep -c '^[0-9]*$')
echo "$(date '+%F %T') driver end done=$ndone/$MOD fail=$(/bin/ls "$OUT/fail" | wc -l | tr -d ' ')"
[ "$ndone" = "$MOD" ] && echo "ALL DONE" > "$OUT/ALLDONE"
