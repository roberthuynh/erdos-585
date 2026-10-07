#!/bin/bash
# Cross-checks with the second SAT encoding (pairsat_cuts.py, CaDiCaL 1.9.5), run after check 3.
# Part A (one worker): every graph on 8 vertices and the ladder levels vs pairsat.py/brute.py; the
# check-1 sets. Part B (glue18.sh): the 120 known 18-vertex pair-free graphs, both encodings.
set -u
LANE=[local path]
PY=[local path]
SP=[local scratch folder]
L=$LANE/logs/xcheck
mkdir -p "$L"
for n in 3 4 5 6 7 8; do
  "$PY" "$LANE/code/pairsat_cuts.py" "$SP/all_n$n.g6" "$L/all_n$n.cuts" > "$L/all_n$n.cuts.out" 2>&1
  echo "all n=$n vs brute: $("$PY" "$LANE/code/compare.py" "$L/all_n$n.cuts.certs.txt" "$LANE/logs/calib/all_n$n.brute.txt" | head -1)" >> "$L/compare.txt"
done
for ne in 7:15 8:18 9:21 9:22 10:23 10:24 10:25 11:26 11:27; do
  n=${ne%:*}; e=${ne#*:}
  "$PY" "$LANE/code/pairsat_cuts.py" "$SP/lad_n${n}_e$e.g6" "$L/lad_n${n}_e$e.cuts" > "$L/lad_n${n}_e$e.cuts.out" 2>&1
  echo "ladder n=$n e=$e vs pairsat: $("$PY" "$LANE/code/compare.py" "$L/lad_n${n}_e$e.cuts.certs.txt" "$LANE/logs/calib/lad_n${n}_e$e.certs.txt" | head -1)" >> "$L/compare.txt"
done
for f in trianglefree bipartite_gengb; do
  "$PY" "$LANE/code/pairsat_cuts.py" "$LANE/data/check1/$f.g6" "$L/check1_$f.cuts" > "$L/check1_$f.cuts.out" 2>&1
  echo "check1 $f: $(cat "$L/check1_$f.cuts.out")" >> "$L/compare.txt"
done
echo done > "$L/DONE_A"
