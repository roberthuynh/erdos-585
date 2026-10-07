#!/bin/bash
# Check 1: triangle-free and bipartite 5-regular graphs on 16 vertices, stock nauty generators.
set -u
LANE=[local path]
NA=[local path]
PY=[local path]
D=$LANE/data/check1; L=$LANE/logs/check1
mkdir -p "$D" "$L"
cd "$D"
"$NA/geng" -t -d5 -D5 16 > trianglefree.g6 2> "$L/geng_t.err"
"$NA/geng" -tc -d5 -D5 16 > trianglefree_connected.g6 2> "$L/geng_tc.err"
"$NA/geng" -b -d5 -D5 16 > bipartite_gengb.g6 2> "$L/geng_b.err"
"$NA/genbg" -d5 -D5 8 8 > bipartite_genbg_bicoloured.g6 2> "$L/genbg.err"
for f in trianglefree trianglefree_connected bipartite_gengb bipartite_genbg_bicoloured; do
  "$NA/labelg" -q < "$f.g6" | LC_ALL=C sort -u > "$f.canon.g6"
done
{
  echo "lines: $(wc -l < trianglefree.g6) tf, $(wc -l < trianglefree_connected.g6) tf connected, $(wc -l < bipartite_gengb.g6) geng -b, $(wc -l < bipartite_genbg_bicoloured.g6) genbg bicoloured"
  echo "distinct canonical: $(wc -l < trianglefree.canon.g6) tf, $(wc -l < trianglefree_connected.canon.g6) tf connected, $(wc -l < bipartite_gengb.canon.g6) geng -b, $(wc -l < bipartite_genbg_bicoloured.canon.g6) genbg"
  echo "tf vs tf-connected differ: $(LC_ALL=C comm -3 trianglefree.canon.g6 trianglefree_connected.canon.g6 | wc -l)"
  echo "geng -b vs genbg differ: $(LC_ALL=C comm -3 bipartite_gengb.canon.g6 bipartite_genbg_bicoloured.canon.g6 | wc -l)"
  echo "bipartite not in tf: $(LC_ALL=C comm -23 bipartite_gengb.canon.g6 trianglefree.canon.g6 | wc -l)"
} > "$L/generation.txt"
for f in trianglefree bipartite_gengb bipartite_genbg_bicoloured.canon; do
  "$PY" "$LANE/code/pairsat.py" "$f.g6" "$L/$f" --solver m22 --n 16 --deg 5 --certs > "$L/$f.out" 2>&1
  "$PY" "$LANE/code/recheck_certs.py" "$L/$f.certs.txt" > "$L/$f.recheck.txt" 2>&1
  "$PY" "$LANE/code/pairsat.py" "$f.g6" "$L/$f.cd19" --solver cd19 --n 16 --deg 5 --certs > "$L/$f.cd19.out" 2>&1
done
shasum -a 256 *.g6 > "$L/inputs.sha256"
echo done > "$L/DONE"
