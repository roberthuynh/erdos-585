#!/bin/bash
# n = 23, A = K44 - e, B = 7+7, proof-faithful level k44p, deg w = 4 and 5, cap 900 s each
cd "$(dirname "$0")"
PY="$HOME/.cache/erdos585/venv/bin/python"
: > sat23_k44p.out
for d in 4 5; do
  ( nice -n 10 timeout 900 "$PY" -c "import c1_sat; c1_sat.one2(23, 0, $d, 'k44p', True, False, False)" >> sat23_k44p.out 2>&1 || echo "K44-e k44p deg $d TIMEOUT/ERR" >> sat23_k44p.out ) &
done
wait
echo DONE >> sat23_k44p.out
