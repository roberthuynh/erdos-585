#!/bin/bash
# Build the PRUNE geng (geng_q4) and the filter from the sms-census nauty tree (read-only).
set -euo pipefail
N="[local path]"
D="$(cd "$(dirname "$0")" && pwd)"
B="[local scratch folder]"
mkdir -p "$B"; cd "$B"
W1=(-DMAXN=WORDSIZE -DWORDSIZE=32)
for f in gtools nauty nautil naugraph; do cc -O3 "${W1[@]}" -I"$N" -c "$N/$f.c" -o "${f}W1.o"; done
for f in schreier naurng; do cc -O3 -I"$N" -c "$N/$f.c" -o "$f.o"; done
OBJ=(gtoolsW1.o nautyW1.o nautilW1.o naugraphW1.o schreier.o naurng.o)
cc -O3 "${W1[@]}" -DPRUNE=q4prune -DSUMMARY=q4summary -I"$N" -I"$D" -o "$D/geng_q4" "$N/geng.c" "$D/q4prune.c" "${OBJ[@]}"
cc -O3 "${W1[@]}" -DPRUNE=q4prune -DSUMMARY=q4summary -DQ4FULLCHECK -I"$N" -I"$D" -o "$D/geng_q4_fullcheck" "$N/geng.c" "$D/q4prune.c" "${OBJ[@]}"
cc -O3 -I"$D" -o "$D/q4filter" "$D/q4filter.c"
echo BUILD_OK
cc -O3 "${W1[@]}" -I"$N" -c "$N/schreier.c" -o schreierW.o
cc -O3 "${W1[@]}" -DPRUNE1=q4prune_bg -I"$N" -I"$D" -o "$D/genbg_q4" "$N/genbg.c" "$D/q4prune_bg.c" gtoolsW1.o schreierW.o nautyW1.o nautilW1.o naugraphW1.o naurng.o
cc -O3 -I"$D" -o "$D/extend_s" "$D/extend_s.c"
echo BUILD2_OK
