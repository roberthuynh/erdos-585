#!/bin/sh
# connected bipartite 4-regular graphs on 11+11 vertices: non-HD ones saved per shard
G=$HOME/.cache/erdos585/nauty2_9_3/genbg
cd "$(dirname "$0")"
seq 0 23 | xargs -P 3 -I{} sh -c "nice -n 10 $G -q -c -d4:4 -D4:4 11 11 44:44 {}/24 | nice -n 10 ./ptool H > data/q4a11/nonhd_{}.g6 2> data/q4a11/err_{}.txt"
echo done > data/q4a11/DONE
