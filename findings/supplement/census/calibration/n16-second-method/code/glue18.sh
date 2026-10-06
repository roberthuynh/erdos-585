#!/bin/bash
# UNSAT-side test at 18 vertices: the 120 known 5-regular pair-free graphs (B-1 glue18 classes).
# Usage: glue18.sh <pairsat|cuts>. Each graph gets its own file and a 600 s limit; env DEADLINE
# (epoch s) stops the loop before the next graph.
set -u
which=$1
LANE=[local path]
PY=[local path]
SP=[local scratch folder]
L=$LANE/logs/glue18; mkdir -p "$L" "$SP"
N=$(wc -l < "$LANE/data/glue18-classes.input.g6")
for i in $(seq 1 "$N"); do
  if [ -n "${DEADLINE:-}" ] && [ "$(date +%s)" -ge "$DEADLINE" ]; then echo "stopped at deadline before graph $i" >> "$L/$which.txt"; break; fi
  f="$SP/${which}_g$i.g6"; sed -n "${i}p" "$LANE/data/glue18-classes.input.g6" > "$f"
  t0=$(date +%s)
  if [ "$which" = pairsat ]; then
    timeout 600 "$PY" "$LANE/code/pairsat.py" "$f" "$SP/ps_$i" --solver m22 --n 18 --deg 5 --certs > /dev/null 2>&1
    st=$?; v=$(awk '{print $2}' "$SP/ps_$i.certs.txt" 2>/dev/null)
  else
    timeout 600 "$PY" "$LANE/code/pairsat_cuts.py" "$f" "$SP/cu_$i" > /dev/null 2>&1
    st=$?; v=$(awk '{print $2}' "$SP/cu_$i.certs.txt" 2>/dev/null)
  fi
  echo "$i status=$st verdict=${v:-NONE} seconds=$(( $(date +%s) - t0 ))" >> "$L/$which.txt"
done
echo done >> "$L/$which.txt"
