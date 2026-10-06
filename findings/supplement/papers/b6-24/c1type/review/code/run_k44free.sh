#!/bin/bash
# Method 2 for K44-e | 7+7 at n = 23: free F[B], WLOG split (case y1pp / y1b1), symG for the residual
# group, lean levels (k44w, r12), one job per (case, deg w). Usage: run_k44free.sh <limit_seconds>
cd "$(dirname "$0")"
PY=~/.cache/erdos585/venv/bin/python
LIM="${1:-3000}"
for c in y1pp y1b1; do
  for dw in 4 5; do
    nohup nice -n 5 "$PY" run_shape.py n23k44 free "levels=k44w,r12,symG,case=$c" "degw=$dw" "limit=$LIM" workers=1 \
      > "k44free_${c}_d${dw}.out" 2> "k44free_${c}_d${dw}.err" < /dev/null &
    echo "started $c d$dw pid $!"
  done
done
