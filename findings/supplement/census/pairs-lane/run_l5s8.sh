#!/bin/sh
# pair-free bipartite level -5 graphs, sides 8 and 9, min degree 4, max degree 6, e = 46
G=$HOME/.cache/erdos585/nauty2_9_3/genbg
P=../../../585-fable/tools/pairc
cd "$(dirname "$0")"
seq 0 11 | xargs -P 4 -I{} sh -c "nice -n 10 $G -q -d4:4 -D6:6 8 9 46:46 {}/12 | nice -n 10 $P f > data/l5s8/pf_{}.g6 2> data/l5s8/err_{}.txt"
echo done > data/l5s8/DONE
