#!/bin/bash
# launch.sh: start driver.sh detached (new session via setsid, nohup, nice 10), log to logs/driver.log.
# Prints the driver PID (= its process-group id). Env W, STOP_EPOCH, KILL_EPOCH pass through.
D="$(cd "$(dirname "$0")/.." && pwd)"
nohup /usr/bin/python3 -c 'import os, sys; os.setsid(); os.execvp(sys.argv[1], sys.argv[1:])' \
  nice -n 10 "$D/code/driver.sh" >> "$D/logs/driver.log" 2>&1 < /dev/null &
echo $!
