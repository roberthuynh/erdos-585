#!/bin/bash
# postrun.sh DRIVER_PID: wait for the driver to exit, then SAT on all stalled AM-sample tests
# (sat_stalls.sh, 6 jobs, nice 10), check the saved frames, and rewrite RESULT.md. Skips the SAT step
# if the driver ends after 06:52 EDT (the run must end by 07:00).
set -u
D="$(cd "$(dirname "$0")/.." && pwd)"
P="$1"
while kill -0 "$P" 2>/dev/null; do sleep 60; done
LIMIT=$(date -j -f '%Y-%m-%d %H:%M:%S' '2026-10-06 06:52:00' +%s)
echo "- $(date '+%H:%M:%S') postrun: driver $P has exited" >> "$D/LOG.md"
if [ "$(date +%s)" -lt "$LIMIT" ]; then
  nice -n 10 "$D/code/sat_stalls.sh" 6 > "$D/logs/sat_stalls.log" 2>&1
  nice -n 10 /usr/bin/python3 "$D/code/check_stall_frames.py" "$D/data/stall_frames.txt" > "$D/logs/check_stall_frames.log" 2>&1
  echo "- $(date '+%H:%M:%S') postrun: stall SAT $(cat "$D/data/stall_sat/SUMMARY.txt" 2>/dev/null); frame check: $(tail -1 "$D/logs/check_stall_frames.log"); RESULT.md rewritten" >> "$D/LOG.md"
else
  echo "- $(date '+%H:%M:%S') postrun: past 06:52, stall SAT skipped" >> "$D/LOG.md"
fi
