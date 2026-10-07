#!/bin/bash
cd "$(dirname "$0")"
PY=/usr/bin/python3
timeout 600 "$PY" stress.py 11 2000 stress_s11.out &
timeout 600 "$PY" stress.py 12 2000 stress_s12.out &
timeout 600 "$PY" stress.py 13 2000 stress_s13_low.out lowmatch &
timeout 600 "$PY" stress.py 14 2000 stress_s14_low.out lowmatch &
wait
echo STRESSDONE > stress_done.txt
