#!/bin/sh
# E4 a=9 (n=18): every graph tested for a spanning pair; NOSP graphs saved per shard
G=$HOME/.cache/erdos585/nauty2_9_3/genbg
cd "$(dirname "$0")"
seq 0 99 | xargs -P 5 -I{} sh -c "nice -n 10 $G -q -d4:4 -D6:6 9 9 50:50 {}/100 | nice -n 10 ./ptool H > data/e4a9/nosp_{}.g6 2> data/e4a9/err_{}.txt"
echo done > data/e4a9/DONE
