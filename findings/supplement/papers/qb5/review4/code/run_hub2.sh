#!/bin/bash
# run_hub2.sh: planted hubs, larger rests (W needs >= 6 distinct neighbours in Y u R)
cd "$(dirname "$0")/.." || exit 1
for cfg in "A45 3 5" "A45 3 6" "A45 2 6" "A45 1 7" "B56 2 5" "B56 3 5" "B56 2 6" "B56 1 6" "D55 2 5" "D55 2 6" "D55 1 6" "D55 3 5"; do
  read -r t y r <<< "$cfg"
  f="data/hub_${t}_${y}${r}.blk"
  timeout 100 python3 code/gen_hub.py "$t" "$y" "$r" 150 9 > "$f"
  echo "cfg $t ny=$y nR=$r: $(wc -l < "$f") generated"
  timeout 200 ./code/kl1rev < "$f" > "${f%.blk}.out" 2> "${f%.blk}.err"
  grep -E '^(blocks|multisets with|petals|I_X)' "${f%.blk}.out" | sed 's/^/  /'
  awk '/^V/{s+=$NF} END{print "  total violations", s}' "${f%.blk}.out"
done
