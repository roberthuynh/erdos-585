#!/bin/bash
# Pilot: one slice r/MOD of genbg -X$X 11+11 6-regular, timed generation alone, then genbg | s6n22.
# Usage: run_pilot.sh r MOD X [s6n22 options...]
set -u
D="$(cd "$(dirname "$0")/.." && pwd)"
G="$HOME/.cache/erdos585/nauty2_9_3/genbg"
r="$1"; MOD="$2"; X="$3"; shift 3
P="$D/data/pilot/p_${X}_${r}of${MOD}"
/usr/bin/time -p "$G" -u -X"$X" -d6:6 -D6:6 11 11 "$r/$MOD" > "$P.genu" 2>&1
/usr/bin/time -p bash -c "\"$G\" -X$X -d6:6 -D6:6 11 11 $r/$MOD 2> \"$P.genbg.err\" | \"$D/code/s6n22\" -p \"$P\" -s $r -q $*" > "$P.time" 2>&1
echo "exit $?"
