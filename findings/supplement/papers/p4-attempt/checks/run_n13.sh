#!/bin/bash
# Minimal-counterexample search for P_4 at n = 13 (e = 35): geng_sp35q4, 48 shards, 6 workers.
cd "$(dirname "$0")"
seq 1 47 | xargs -P 6 -I{} sh -c 'nice -n 10 ./geng_sp35q4 -q -d4 -D6 13 35:35 {}/48 > data/spq4_n13_{}.g6 2> data/spq4_n13_{}.err'
echo done > data/spq4_n13.done
