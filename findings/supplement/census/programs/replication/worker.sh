#!/bin/bash
# worker.sh K NW : process every slice whose index is congruent to K mod NW, job by job.
# A slice is DONE only if geng printed its rvext summary (complete run); otherwise FAIL.
cd "$(dirname "$0")/.." || exit 1
K="$1"; NW="$2"
jobs=(
  "pos12t4|6|3|31|-d3 -D6 11 27:27|40"
  "s13t4|5|2|35|-d3 -D6 12 31:31|400"
  "s13t5|5|2|35|-d4 -D6 12 30:30|400"
)
for j in "${jobs[@]}"; do
  IFS='|' read -r tag sp spmin ef gargs mod <<< "$j"
  for ((r = K; r < mod; r += NW)); do
    if grep -q "^DONE $tag $r " runs13/status.txt 2>/dev/null; then continue; fi
    out="runs13/H_${tag}_$r.g6"; err="runs13/err_${tag}_$r.txt"
    t0=$(date +%s)
    RV_SP="$sp" RV_SPMIN="$spmin" RV_EXT_EF="$ef" RV_EXT_MINDF=4 timeout 240 ./rvgengx -q $gargs "$r/$mod" > "$out" 2> "$err"
    rc=$?; t1=$(date +%s)
    summ=$(grep -h "^rvext: G=" "$err")
    cpu=$(grep -h "^rvsummary" "$err" | sed -E 's/.*cpu=([0-9.]+).*/\1/')
    if [ "$rc" = 0 ] && [ -n "$summ" ]; then
      echo "DONE $tag $r rc=$rc wall=$((t1-t0)) cpu=$cpu Hlines=$(wc -l < "$out" | tr -d ' ') $summ" >> runs13/status.txt
    else
      echo "FAIL $tag $r rc=$rc wall=$((t1-t0))" >> runs13/status.txt
    fi
  done
done
echo "WORKER $K finished $(date '+%T')" >> runs13/status.txt
