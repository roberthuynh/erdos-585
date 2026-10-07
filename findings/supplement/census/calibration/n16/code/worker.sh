#!/bin/bash
# One shard: geng_pp -q -d5 -D5 16 r/MOD. Skips done shards; takes no new shard at or after STOP_NEW;
# kills its run at HARD. A shard counts as covered only if <r>.done exists.
r="$1"
L="$LANE/logs/shards"; O="$LANE/data/out"
[ -f "$L/$r.done" ] && exit 0
[ -f "$LANE/STOP" ] && exit 0
now=$(date +%s)
[ "$now" -ge "$STOP_NEW" ] && exit 0
left=$((HARD - now))
[ "$left" -le 5 ] && exit 0
BIN="$(cat "$LANE/code/CURRENT_BIN")"
t0=$(date +%s)
timeout "$left" "$BIN" -d5 -D5 16 "$r/$MOD" > "$O/$r.g6.part" 2> "$L/$r.err"
rc=$?
t1=$(date +%s)
if [ "$rc" -eq 0 ] && grep -q '^>Z' "$L/$r.err"; then
  mv "$O/$r.g6.part" "$O/$r.g6"
  echo "shard=$r rc=0 wall_s=$((t1 - t0)) bin=$(basename "$BIN") $(grep '^>Z' "$L/$r.err")" > "$L/$r.done"
else
  echo "$(date '+%H:%M:%S') shard=$r rc=$rc incomplete" >> "$LANE/logs/incomplete.txt"
fi
exit 0
