#!/bin/bash
# usage: run_cases2.sh n level star qfree allA out [cap]  -- every case index, deg y 4 and 5; 6 parallel
cd "$(dirname "$0")"
PY="$HOME/.cache/erdos585/venv/bin/python"
n=$1; lev=$2; star=$3; qf=$4; allA=$5; out=$6; cap=${7:-200}
N=$("$PY" -c "import c1_sat; print(len(c1_sat.cases_for($n, $allA)))")
: > "$out"
for ((i=${START:-0};i<N;i++)); do for d in 4 5; do echo "$i $d"; done; done | \
  xargs -P 6 -L 1 bash -c 'timeout '"$cap"' '"$PY"' -c "import c1_sat; c1_sat.one2('"$n"', $0, $1, \"'"$lev"'\", '"$star"', '"$qf"', '"$allA"')" >> '"$out"' 2>&1 || echo "case $0 deg $1 TIMEOUT/ERR" >> '"$out"
echo DONE >> "$out"
