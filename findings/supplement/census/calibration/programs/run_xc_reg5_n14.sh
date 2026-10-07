#!/bin/bash
# Second method for the 5-regular n = 14 census: pair_oracle (SAT, witness replay) on all
# 3,459,386 graphs, 100 geng shards, 6 worker processes. Resumable (skips finished shards).
# Usage: nohup nice -n 15 bash run_xc_reg5_n14.sh > logs/driver_xc_reg5_n14.log 2>&1 &
set -u -o pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
G="$HOME/.cache/erdos585/nauty2_9_3/geng"
V="$HOME/.cache/erdos585/venv/bin/python"
W="$HOME/.cache/erdos585/xc/reg5-n14"; S="$HERE/logs/xc/reg5-n14"
mkdir -p "$W" "$S"; : > "$W/empty.g6"
echo "start $(date '+%Y-%m-%d %H:%M:%S %Z')"
for r in $(seq 0 99); do
  [ -s "$S/part-$r.summary.txt" ] && continue
  "$G" -q -d5 -D5 14 "$r/100" > "$W/part-$r.g6"
  "$V" "$HERE/crosscheck_oracle.py" "$W/part-$r.g6" "$W/empty.g6" "$S/part-$r" --jobs 6 --seconds 120 > /dev/null
  echo "part $r exit=$? $(cat "$S/part-$r.summary.txt") $(date '+%H:%M:%S')"
done
echo "end $(date '+%Y-%m-%d %H:%M:%S %Z')"
cat "$S"/part-*.summary.txt | awk '{for(i=1;i<=NF;i++){split($i,a,"="); if(a[1] ~ /^(graphs|PAIR|NOPAIR|TIMEOUT|bad_witness)$/) t[a[1]]+=a[2]}; if ($0 ~ /agree=True/) ag++; n++} END{printf "shards=%d agree_shards=%d graphs=%d PAIR=%d NOPAIR=%d TIMEOUT=%d bad_witness=%d\n", n, ag, t["graphs"], t["PAIR"], t["NOPAIR"], t["TIMEOUT"], t["bad_witness"]}'
