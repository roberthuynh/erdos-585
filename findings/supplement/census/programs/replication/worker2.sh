#!/bin/bash
# second pass: save the extendable 12-vertex graphs. worker2.sh K NW
cd "$(dirname "$0")/.." || exit 1
K="$1"; NW="$2"
jobs=("s13t5save|-d4 -D6 12 30:30|400|1")
for j in "${jobs[@]}"; do
  IFS='|' read -r tag gargs mod step <<< "$j"
  idx=0
  for ((r = 0; r < mod; r += step)); do
    idx=$((idx + 1)); [ $(( (idx - 1) % NW )) -ne "$K" ] && continue
    if grep -q "^DONE $tag $r " runs13/status2.txt 2>/dev/null; then continue; fi
    out="l12/G_${tag}_$r.g6"; err="l12/err_${tag}_$r.txt"
    RV_SP=5 RV_SPMIN=2 RV_EXT_EF=35 RV_EXT_MINDF=4 timeout 240 ./rvgengs -q $gargs "$r/$mod" "$out" 2> "$err"
    rc=$?
    summ=$(grep -h "^rvsave:" "$err")
    if [ "$rc" = 0 ] && [ -n "$summ" ]; then echo "DONE $tag $r $summ" >> runs13/status2.txt
    else echo "FAIL $tag $r rc=$rc" >> runs13/status2.txt; fi
  done
done
echo "WORKER2 $K finished $(date '+%T')" >> runs13/status2.txt
