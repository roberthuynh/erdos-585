#!/bin/bash
# One shard: geng -c -b -d4 -D4 N 2N:2N RES/MOD | hdq -B, restart-safe.
# usage: run_shard.sh N MOD OUTDIR RES
# Writes OUTDIR/s_RES.out.gz (per-graph lines), OUTDIR/s_RES.err (hdq summary),
# OUTDIR/s_RES.gerr (geng summary), and OUTDIR/done/RES (one-line summary) on success only.
set -u
N="$1"; MOD="$2"; OUT="$3"; RES="$4"
G="$HOME/.cache/erdos585/nauty2_9_3/geng"
H="$(cd "$(dirname "$0")" && pwd)/hdq"
mkdir -p "$OUT/done" "$OUT/fail"
[ -f "$OUT/done/$RES" ] && exit 0
rm -f "$OUT/s_$RES.out" "$OUT/s_$RES.out.gz" "$OUT/fail/$RES"
t0=$(date +%s)
timeout 3600 nice -n 10 "$G" -c -b -d4 -D4 "$N" "$((2*N))":"$((2*N))" "$RES/$MOD" 2> "$OUT/s_$RES.gerr" \
  | timeout 3600 nice -n 10 "$H" -B > "$OUT/s_$RES.out" 2> "$OUT/s_$RES.err"
st=("${PIPESTATUS[@]}")
t1=$(date +%s)
gcount=$(sed -n 's/^>Z \([0-9]*\) graphs generated.*/\1/p' "$OUT/s_$RES.gerr")
hcount=$(sed -n 's/.*graphs=\([0-9]*\) .*/\1/p' "$OUT/s_$RES.err")
lines=$(wc -l < "$OUT/s_$RES.out" | tr -d ' ')
if [ "${st[0]}" = 0 ] && [ "${st[1]}" = 0 ] && [ -n "$gcount" ] && [ "$gcount" = "$hcount" ] && [ "$hcount" = "$lines" ]; then
  gzip -f "$OUT/s_$RES.out" || { echo "res=$RES gzip_failed" > "$OUT/fail/$RES"; exit 1; }
  echo "res=$RES geng=$gcount wall=$((t1-t0)) $(cat "$OUT/s_$RES.err")" > "$OUT/done/$RES.tmp" && mv "$OUT/done/$RES.tmp" "$OUT/done/$RES"
else
  echo "res=$RES geng_exit=${st[0]} hdq_exit=${st[1]} geng=$gcount hdq=$hcount lines=$lines" > "$OUT/fail/$RES"
  exit 1
fi
