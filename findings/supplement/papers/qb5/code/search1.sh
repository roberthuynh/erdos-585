#!/bin/bash
# Round-2 random search for counterexamples to the E5 pair statement (lane qb5).
cd "$(dirname "$0")"
run(){ timeout 240 ./pairsearch "$@" > "data/search/ps_$1_$2_$5_$6_$4.out" 2> "data/search/ps_$1_$2_$5_$6_$4.err"; }
for nu in 1 0; do for tw in 0 60; do
  run 4 4 2000 11 $nu $tw &
  run 4 5 2000 12 $nu $tw &
  run 5 5 1500 13 $nu $tw &
  run 4 6 1500 14 $nu $tw &
  wait
  run 4 7 400 15 $nu $tw &
  run 5 6 400 16 $nu $tw &
  wait
done; done
echo DONE > data/search/search1.done
