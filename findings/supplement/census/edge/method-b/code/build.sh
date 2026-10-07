#!/bin/bash
# build.sh -- build method B binaries into code/bin (wave8/exb).
#   geng_h4    nauty 2.9.3 geng with PRUNE = h4prune (own decider h4.h)
#   geng_plain nauty 2.9.3 geng, unmodified, same flags
#   h4filt     stand-alone decider (own graph6 decoder + h4.h)
#   bipgen     own generator (canonical augmentation by class-B vertices,
#              nauty for automorphisms and canonical labels) + h4.h prune
# Nauty source: ~/.cache/erdos585/nauty2_9_3 (read only; objects built here).
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
NAUTY="$HOME/.cache/erdos585/nauty2_9_3"
BIN="$HERE/bin"
mkdir -p "$BIN"
CC=/usr/bin/clang
CF=(-O3 -DMAXN=WORDSIZE -DWORDSIZE=32 -I"$NAUTY")
SRC=("$NAUTY/gtools.c" "$NAUTY/nauty.c" "$NAUTY/nautil.c" "$NAUTY/naugraph.c"
     "$NAUTY/schreier.c" "$NAUTY/naurng.c")
"$CC" "${CF[@]}" -DPRUNE=h4prune -DSUMMARY=h4summary -o "$BIN/geng_h4" \
    "$NAUTY/geng.c" "$HERE/h4prune.c" "${SRC[@]}"
"$CC" "${CF[@]}" -o "$BIN/geng_plain" "$NAUTY/geng.c" "${SRC[@]}"
"$CC" -O3 -Wall -Wextra -o "$BIN/h4filt" "$HERE/h4filt.c"
"$CC" "${CF[@]}" -Wall -o "$BIN/bipgen" "$HERE/bipgen.c" "${SRC[@]}"
{
  date '+built %Y-%m-%d %H:%M:%S %Z'
  "$CC" --version | head -1
  shasum -a 256 "$BIN/bipgen" "$BIN/geng_h4" "$BIN/geng_plain" "$BIN/h4filt" \
      "$HERE/h4.h" "$HERE/bipgen.c" "$HERE/h4prune.c" "$HERE/h4filt.c" "$NAUTY/geng.c"
} > "$HERE/BUILD.txt"
cat "$HERE/BUILD.txt"
