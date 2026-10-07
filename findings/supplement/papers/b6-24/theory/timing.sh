#!/bin/bash
# Timing slices for N.md (cost estimates only). Run from wave4/theory. Each step is time-limited.
G="$HOME/.cache/erdos585/nauty2_9_3/genbg"
PT="../../wave3/pairs/ptool"
PC="../../../585-fable/tools/pairc"
: > timing.out
# H24: graphs generated in 60 s (one process), then HD-test rate on them
timeout 60 "$G" -q -c -d4:4 -D4:4 12 12 48:48 > h24_sample.g6 2> /dev/null
echo "H24 genbg 60 s: $(wc -l < h24_sample.g6) graphs" >> timing.out
t0=$(date +%s)
head -200000 h24_sample.g6 | timeout 100 "$PT" H > /dev/null 2> h24_pt.err
t1=$(date +%s); echo "H24 ptool H on first 200k: $((t1 - t0)) s; $(tr '\n' ' ' < h24_pt.err)" >> timing.out
# B6 at N = 20: full count, then pairc
t1=$(date +%s)
timeout 100 "$G" -u -d6:6 -D6:6 10 10 60:60 2>> timing.out
t2=$(date +%s); echo "B6 N=20 genbg -u: $((t2 - t1)) s" >> timing.out
timeout 100 "$G" -q -d6:6 -D6:6 10 10 60:60 > b6_20.g6
timeout 100 "$PC" f < b6_20.g6 > b6_20_pairfree.g6 2> b6_20_pairc.err
t3=$(date +%s); echo "B6 N=20 graphs $(wc -l < b6_20.g6), pairc f: $((t3 - t2)) s, pair-free $(wc -l < b6_20_pairfree.g6); $(tr '\n' ' ' < b6_20_pairc.err)" >> timing.out
# B6 at N = 22: graphs generated in 60 s
timeout 60 "$G" -q -d6:6 -D6:6 11 11 66:66 > b6_22_sample.g6 2> /dev/null
echo "B6 N=22 genbg 60 s: $(wc -l < b6_22_sample.g6) graphs" >> timing.out
