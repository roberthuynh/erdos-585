#!/bin/bash
# Pilot: time geng -c -b -d4 -D4 22 44:44 on a few res/2000 slices (count only, -u).
G="$HOME/.cache/erdos585/nauty2_9_3/geng"
OUT="$(dirname "$0")/../data/pilot"
for r in "$@"; do
  ( /usr/bin/time -p nice -n 10 timeout 240 "$G" -c -b -d4 -D4 -u 22 44:44 "$r/2000" > "$OUT/geng_u_$r.txt" 2>&1 ) &
done
wait
