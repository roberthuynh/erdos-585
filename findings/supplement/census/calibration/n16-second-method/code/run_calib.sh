#!/bin/bash
# Calibration of pairsat.py against brute.py and against the B-1 ladder counts (CALIBRATION.md R2).
set -u
LANE=[local path]
NA=[local path]
PY=[local path]
SP=[local scratch folder]
L=$LANE/logs/calib
mkdir -p "$SP" "$L"
# (1) every graph on 3..8 vertices: SAT verdict vs exhaustive verdict, graph by graph
for n in 3 4 5 6 7 8; do
  "$NA/geng" -q "$n" > "$SP/all_n$n.g6"
  "$PY" "$LANE/code/pairsat.py" "$SP/all_n$n.g6" "$L/all_n$n" --solver m22 --certs > "$L/all_n$n.sat.out" 2>&1
  "$PY" "$LANE/code/brute.py" "$SP/all_n$n.g6" "$L/all_n$n.brute.txt" > "$L/all_n$n.brute.out" 2>&1
  echo "n=$n $(wc -l < "$SP/all_n$n.g6" | tr -d ' ') graphs: $("$PY" "$LANE/code/compare.py" "$L/all_n$n.certs.txt" "$L/all_n$n.brute.txt" | head -1)" >> "$L/compare.txt"
done
# (2) ladder levels with 3 <= degree <= 5 (geng -d3 -D5 n e:e)
for ne in 7:15 8:18 9:21 9:22 10:23 10:24 10:25 11:26 11:27; do
  n=${ne%:*}; e=${ne#*:}
  "$NA/geng" -q -d3 -D5 "$n" "$e:$e" > "$SP/lad_n${n}_e$e.g6"
  "$PY" "$LANE/code/pairsat.py" "$SP/lad_n${n}_e$e.g6" "$L/lad_n${n}_e$e" --solver m22 --certs > "$L/lad_n${n}_e$e.sat.out" 2>&1
  echo "n=$n e=$e graphs=$(wc -l < "$SP/lad_n${n}_e$e.g6" | tr -d ' ') $(cat "$L/lad_n${n}_e$e.sat.out")" >> "$L/ladder.txt"
done
# (3) exhaustive cross-check of the n = 9 and n = 10 ladder levels that contain pair-free graphs
for ne in 9:21 10:23; do
  n=${ne%:*}; e=${ne#*:}
  "$PY" "$LANE/code/brute.py" "$SP/lad_n${n}_e$e.g6" "$L/lad_n${n}_e$e.brute.txt" > "$L/lad_n${n}_e$e.brute.out" 2>&1
  echo "n=$n e=$e: $("$PY" "$LANE/code/compare.py" "$L/lad_n${n}_e$e.certs.txt" "$L/lad_n${n}_e$e.brute.txt" | head -1)" >> "$L/compare.txt"
done
echo done > "$L/DONE"
