#!/bin/bash
# referee data runs (background); each writes its own .out as it goes
cd "$(dirname "$0")"
PY=/usr/bin/python3
timeout 900 "$PY" data_check.py core28.g6 dc_core28.out allpairs crit_first=24 &
timeout 900 "$PY" data_check.py e5_n22.g6 dc_e5_n22.out allpairs crit_first=60 &
timeout 900 "$PY" data_check.py e5_n24.g6 dc_e5_n24.out allpairs crit_first=40 &
timeout 1200 "$PY" data_check.py dm_part_aa dc_dm_aa.out crit_first=60 &
timeout 1200 "$PY" data_check.py dm_part_ab dc_dm_ab.out &
timeout 1200 "$PY" data_check.py dm_part_ac dc_dm_ac.out &
wait
echo ALLDONE > dc_done.txt
