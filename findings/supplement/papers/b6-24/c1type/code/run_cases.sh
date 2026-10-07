#!/bin/bash
# usage: run_cases.sh n level star out  -- runs every case index and deg y, 6 in parallel, 200 s each
cd "$(dirname "$0")"
PY="$HOME/.cache/erdos585/venv/bin/python"
n=$1; lev=$2; star=$3; out=$4
N=$("$PY" -c "import c1_sat; print(len(c1_sat.cases_for($n)))")
: > "$out"
jobs_list=()
for ((i=0;i<N;i++)); do for d in 4 5; do jobs_list+=("$i $d"); done; done
printf '%s\n' "${jobs_list[@]}" | xargs -P 6 -L 1 bash -c 'timeout 200 '"$PY"' -c "import c1_sat; c1_sat.one('"$n"', $0, $1, \"'"$lev"'\", '"$star"')" >> '"$out"' 2>&1 || echo "case $0 deg $1 TIMEOUT/ERR" >> '"$out"
echo DONE >> "$out"
