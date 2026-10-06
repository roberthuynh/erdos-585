#!/bin/bash
# B-1 calibration, the Delta <= 5 level ladder.
# For one order n: e runs from floor(5n/2) down; each level is `geng -q -d3 -D5 n e:e | pairc f`,
# split into K shards (res/mod) run J at a time. Stops after the first e with a pair-free graph
# (that e gives max(e - 5n/2) over pair-free graphs with 3 <= deg <= 5 on n vertices).
# Usage: bash run_ladder.sh n [K shards, default 1] [J parallel, default 1] [e_start] [e_stop]
set -u -o pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
G="$HOME/.cache/erdos585/nauty2_9_3/geng"
P=[local path]
n=$1; K=${2:-1}; J=${3:-1}
e_hi=${4:-$(( 5 * n / 2 ))}
e_lo=${5:-$(( (3 * n + 1) / 2 ))}
OUT="$HERE/data/ladder"; LOG="$HERE/logs/ladder"
mkdir -p "$OUT" "$LOG"
export G P OUT LOG n K
for (( e = e_hi; e >= e_lo; e-- )); do
  export e
  t0=$(date +%s)
  seq 0 $(( K - 1 )) | xargs -P "$J" -I{} /bin/bash -c '
    r={}
    tag="n$n-e$e-$r-$K"
    if grep -q "^graphs=" "$LOG/$tag.err" 2>/dev/null; then exit 0; fi
    { /usr/bin/time -p /bin/bash -c "\"$G\" -q -d3 -D5 $n $e:$e $r/$K | \"$P\" f > \"$OUT/$tag.g6\""; } 2> "$LOG/$tag.err"
  '
  t1=$(date +%s)
  sum=$(awk -F'[= ]' '/^graphs=/{g+=$2; p+=$4; f+=$6; s++} /^user /{u+=$2} END{printf "shards=%d graphs=%d with_pair=%d pair_free=%d user_s=%.1f", s, g, p, f, u}' "$LOG"/n$n-e$e-*-$K.err)
  lev=$(awk -v e="$e" -v n="$n" 'BEGIN{printf "%.1f", e - 2.5 * n}')
  echo "n=$n e=$e level=$lev $sum wall_s=$(( t1 - t0 ))" | tee -a "$LOG/summary-n$n.txt"
  pf=$(echo "$sum" | sed -n 's/.*pair_free=\([0-9]*\).*/\1/p')
  if [ "${pf:-0}" -gt 0 ]; then
    # never overwrite an existing combined file (n = 12 shard .g6 files were moved to ~/.cache/erdos585/ladder-shards)
    [ -s "$OUT/n$n-e$e-pairfree.g6" ] || cat "$OUT"/n$n-e$e-*-$K.g6 > "$OUT/n$n-e$e-pairfree.g6"
    echo "n=$n FIRST pair-free at e=$e level=$lev count=$pf" | tee -a "$LOG/summary-n$n.txt"
    break
  fi
done
