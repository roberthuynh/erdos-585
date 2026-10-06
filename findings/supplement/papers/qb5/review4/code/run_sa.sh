#!/bin/bash
# run_sa.sh WORKER: SA from planted-hub start blocks; dumps go to data/sa/dump_W.blk
cd "$(dirname "$0")/.." || exit 1
W="$1"; shift
out="data/sa/dump_${W}.blk"; log="data/sa/sa_${W}.log"
: > "$log"
i=0
for f in "$@"; do
  for ln in 1 7 13 19; do
    i=$((i+1))
    line=$(sed -n "${ln}p" "$f"); [ -z "$line" ] && continue
    printf '%s\n' "$line" > "data/sa/start_${W}_${i}.blk"
    na=$(printf '%s\n' "$line" | awk '{print $1}')
    timeout 240 ./code/sa_kl1 "$na" "$((1000*W+i))" 300000 2.0 "$out" "data/sa/start_${W}_${i}.blk" 2>> "$log" > /dev/null
    tail -1 "$log"
  done
done
