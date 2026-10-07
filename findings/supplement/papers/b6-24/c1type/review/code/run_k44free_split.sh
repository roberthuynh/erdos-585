#!/bin/bash
# Hedge for method 2: complete case split on the position of u1 (A:0..3, B:0..6) for one (case, deg w).
# Usage: run_k44free_split.sh <case y1pp|y1b1> <degw 4|5>
cd "$(dirname "$0")"
PY=~/.cache/erdos585/venv/bin/python
c="$1"; dw="$2"
for pos in A:0 A:1 A:2 A:3 B:0 B:1 B:2 B:3 B:4 B:5 B:6; do
  tag="${pos/:/}"
  nohup nice -n 10 "$PY" run_shape.py n23k44 free "levels=k44w,r12,symG,case=$c,u1=$pos" "degw=$dw" workers=1 \
    > "k44split_${c}_d${dw}_${tag}.out" 2> "k44split_${c}_d${dw}_${tag}.err" < /dev/null &
  echo "started $c d$dw u1=$pos pid $!"
done
