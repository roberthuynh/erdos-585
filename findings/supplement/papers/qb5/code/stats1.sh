#!/bin/bash
# Round-2 check of conjecture A (pairs with c_p = c_q = 0 are good) over random families (lane qb5).
cd "$(dirname "$0")"
for cfg in "4 5" "5 5" "4 6" "4 7" "5 6"; do for tw in 0 60 90; do for nu in 1 0; do
  set -- $cfg
  f="data/search/st_$1_$2_${tw}_$nu.err"
  timeout 240 ./pairsearch_stats "$1" "$2" 250 $((300+tw+nu)) "$nu" "$tw" > /dev/null 2> "$f"
  tot=$(grep "cp=0 dp=. cq=0" "$f" | sed 's/.*good //' | awk -F/ '{g+=$1; t+=$2} END {print g"/"t}')
  echo "$cfg tw=$tw nu=$nu: $(grep -o 'sparse=[0-9]* minGood=[0-9]*' "$f") zz-pairs good $tot"
done; done; done
