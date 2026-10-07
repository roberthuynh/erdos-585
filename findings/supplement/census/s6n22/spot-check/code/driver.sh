#!/bin/bash
# driver.sh (wave8/s6spot): W workers (xargs -P) over data/jobs.txt ("r mode" per line), then
# code/collect.py. STOP file or STOP_EPOCH: no new slices; KILL_EPOCH: the whole process group
# is killed (slices without a done marker are simply not counted).
set -u
D="$(cd "$(dirname "$0")/.." && pwd)"
W="${W:-4}"
echo "$(date '+%F %T') driver start pid=$$ W=$W STOP_EPOCH=${STOP_EPOCH:-none} KILL_EPOCH=${KILL_EPOCH:-none}" >> "$D/logs/driver.log"
if [ -n "${KILL_EPOCH:-}" ]; then
  ( while [ "$(date +%s)" -lt "$KILL_EPOCH" ]; do sleep 15; kill -0 $$ 2>/dev/null || exit 0; done
    echo "$(date '+%F %T') kill epoch reached, killing group" >> "$D/logs/driver.log"
    kill -TERM -- -"$(ps -o pgid= $$ | tr -d ' ')" ) &
fi
xargs -P "$W" -L 1 "$D/code/run_slice.sh" < "$D/data/jobs.txt"
echo "$(date '+%F %T') workers finished (xargs exit $?)" >> "$D/logs/driver.log"
"$HOME/.cache/erdos585/venv/bin/python" "$D/code/collect.py" >> "$D/logs/driver.log" 2>&1
echo "$(date '+%F %T') driver end" >> "$D/logs/driver.log"
