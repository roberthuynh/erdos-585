#!/bin/bash
# run_n1.sh: planted (N1) blocks at several sizes through kl1rev (W nonempty needs |Z| >= 6)
cd "$(dirname "$0")/.." || exit 1
for cfg in "5 5 4" "6 5 4" "5 6 4" "6 6 4" "7 5 4" "5 5 6" "6 6 6" "6 7 4"; do
  read -r p q r <<< "$cfg"
  f="data/n1_${p}${q}${r}.blk"
  timeout 100 python3 code/gen_n1.py "$p" "$q" "$r" 40 11 > "$f"
  echo "cfg p=$p q=$q r=$r (|A| = $((1+p+q+r))): $(wc -l < "$f") generated"
  timeout 200 ./code/kl1rev -v < "$f" > "${f%.blk}.out" 2> "${f%.blk}.err"
  grep -E '^(blocks|pairs|I_X)' "${f%.blk}.out" | sed 's/^/  /'
  awk '/^V/{s+=$NF} END{print "  total violations", s}' "${f%.blk}.out"
  grep '^N1' "${f%.blk}.out" | sed -E 's/line [0-9]+ //; s/ a=[0-9]+//; s/IX=[0-9a-f]+ m=[0-9]+ T=[0-9a-f]+ T.=[0-9a-f]+//' | sort | uniq -c | sed 's/^/  /'
done
