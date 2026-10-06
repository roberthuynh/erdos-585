#!/bin/bash
# Build the pruned geng (geng_pp) and the standalone decider (pairdec). Run from anywhere.
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
NA="$HOME/.cache/erdos585/nauty2_9_3"
W="-DMAXN=WORDSIZE -DWORDSIZE=32"
gcc -O3 -march=native $W -DPRUNE=pairprune -DSUMMARY=pairsummary -I"$NA" -o "$HERE/geng_pp" \
  "$NA/geng.c" "$HERE/pairprune.c" "$NA/gtoolsW.o" "$NA/nautyW1.o" "$NA/nautilW1.o" \
  "$NA/naugraphW1.o" "$NA/schreierW.o" "$NA/naurng.o"
gcc -O3 -march=native -DSTANDALONE -o "$HERE/pairdec" "$HERE/pairprune.c"
shasum -a 256 "$HERE/pairprune.c" "$HERE/geng_pp" "$HERE/pairdec" "$NA/geng.c"
