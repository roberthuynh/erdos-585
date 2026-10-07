#!/bin/bash
# n = 23, A = K44 - e, B = 7+7, full model (level y), deg y = 4 and 5, cap 1500 s each
cd "$(dirname "$0")"
PY="$HOME/.cache/erdos585/venv/bin/python"
: > sat23_k44.out
for d in 4 5; do
  ( nice -n 10 timeout 1500 "$PY" -c "import c1_sat; c1_sat.one2(23, 0, $d, 'y', True, False, False)" >> sat23_k44.out 2>&1 || echo "K44-e deg $d TIMEOUT/ERR" >> sat23_k44.out ) &
done
wait
echo DONE >> sat23_k44.out
