#!/bin/bash
# B6 at N = 20: pair test (pairc f prints pair-FREE graphs) on all 121,790 graphs from
# genbg -q -d6:6 -D6:6 10 10 60:60 (6-regular bipartite, 10+10), split into 4 parts.
cd "$(dirname "$0")"
PC="../../../585-fable/tools/pairc"
for f in b6_20_part_aa b6_20_part_ab b6_20_part_ac b6_20_part_ad; do
  ( nice -n 10 timeout 1500 "$PC" f < "$f" > "$f.pairfree" 2> "$f.err"; echo "exit $?" >> "$f.err" ) &
done
wait
echo done > b6_20.DONE
