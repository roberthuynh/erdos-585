#!/bin/bash
# Pair-free bipartite graphs with parts (t, r) and e edges, for the s <= 1 set sizes of Lemma 3.1 inside a side B.
cd "$(dirname "$0")"
G="$HOME/.cache/erdos585/nauty2_9_3/genbg"
PC="../../../585-fable/tools/pairc"
: > census_side.out
run() { t=$1; r=$2; e=$3
  f="cs_${t}_${r}_e${e}"
  timeout 240 "$G" -q "$t" "$r" "$e:$e" > "$f.g6"
  timeout 240 "$PC" f < "$f.g6" > "$f.pairfree" 2> "$f.err"
  echo "t=$t r=$r e=$e graphs=$(wc -l < $f.g6 | tr -d ' ') pairfree=$(wc -l < $f.pairfree | tr -d ' ') [$(tr '\n' ' ' < $f.err)]" >> census_side.out
}
run 4 6 23; run 4 6 24
run 5 6 27; run 5 6 28; run 5 6 29; run 5 6 30
run 5 7 29; run 5 7 30; run 5 7 31
run 6 7 33; run 6 7 34; run 6 7 35
echo done >> census_side.out
