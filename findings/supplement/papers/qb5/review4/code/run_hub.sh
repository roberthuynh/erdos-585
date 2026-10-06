#!/bin/bash
# run_hub.sh: planted hubs with single-vertex petals through kl1rev
cd "$(dirname "$0")/.." || exit 1
for cfg in "A45 2 3" "A45 3 3" "A45 3 4" "A45 2 5" "B56 2 3" "B56 3 3" "B56 2 4" "D55 2 3" "D55 2 4" "D55 1 4"; do
  read -r t y r <<< "$cfg"
  f="data/hub_${t}_${y}${r}.blk"
  timeout 100 python3 code/gen_hub.py "$t" "$y" "$r" 150 5 > "$f"
  echo "cfg $t ny=$y nR=$r: $(wc -l < "$f") generated"
  timeout 200 ./code/kl1rev < "$f" > "${f%.blk}.out" 2> "${f%.blk}.err"
  grep -E '^(blocks|pairs|multisets with|petals|I_X)' "${f%.blk}.out" | sed 's/^/  /'
  awk '/^V/{s+=$NF} END{print "  total violations", s}' "${f%.blk}.out"
done
