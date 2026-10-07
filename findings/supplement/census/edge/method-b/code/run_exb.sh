#!/bin/bash
# run_exb.sh -- detached, sharded, resumable driver for method B (wave8/exb).
#
#   run_exb.sh launch   start the driver detached (nohup, nice 10); refuses if one is alive
#   run_exb.sh drive    the driver loop itself (launch calls this)
#   run_exb.sh status   print progress per job; writes nothing
#
# Jobs: code/jobs.tsv (tag, mod, command with {r} and {mod}); work list:
# code/queue.txt ("tag r" per line, run in order).  Shard files:
# logs/<tag>/shard_<r>.{g6,err,done}; a shard counts only if .done exists
# and records exit status 0.  Claims are directories shard_<r>.claim
# (mkdir is atomic); a resume clears claims without .done.
# Workers: 4 before 11:00, 6 from 11:00 (machine shared with a census
# job until about 11:00); data/WORKERS overrides.  data/STOP: start nothing
# new, let running shards finish, then collect.  Each shard runs under
# timeout SHARD_TIMEOUT.  At the end the driver runs code/collect.py.
set -u
HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(dirname "$HERE")"
LOGS="$ROOT/logs"
DATA="$ROOT/data"
JOBS="$HERE/jobs.tsv"
QUEUE="$HERE/queue.txt"
PY="$HOME/.cache/erdos585/venv/bin/python"
SHARD_TIMEOUT=3000
DRIVERLOG="$LOGS/driver.log"
PIDFILE="$LOGS/driver.pid"

log() { echo "$(date '+%Y-%m-%d %H:%M:%S') $*" >> "$DRIVERLOG"; }

workers_now() {
  if [ -f "$DATA/WORKERS" ]; then
    local w; w="$(tr -dc '0-9' < "$DATA/WORKERS")"
    if [ -n "$w" ]; then echo "$w"; return; fi
  fi
  if [ "$(date +%H%M)" -lt 1100 ]; then echo 4; else echo 6; fi
}

cmd_for() { # tag r -> command line
  local tag="$1" r="$2" line mod cmd
  line="$(awk -F'\t' -v t="$tag" '$1 == t {print; exit}' "$JOBS")"
  mod="$(printf '%s' "$line" | cut -f2)"
  cmd="$(printf '%s' "$line" | cut -f3)"
  cmd="${cmd//\{r\}/$r}"
  cmd="${cmd//\{mod\}/$mod}"
  printf '%s' "$cmd"
}

run_shard() { # tag r
  local tag="$1" r="$2" dir="$LOGS/$1" cmd t0 t1 st
  cmd="$(cmd_for "$tag" "$r")"
  t0="$(date '+%Y-%m-%d %H:%M:%S')"
  ( cd "$HERE" && /usr/bin/time -p timeout "$SHARD_TIMEOUT" /bin/bash -c "set -o pipefail; $cmd" \
      > "$dir/shard_$r.g6" 2> "$dir/shard_$r.err" )
  st=$?
  t1="$(date '+%Y-%m-%d %H:%M:%S')"
  printf 'status %s\nstart %s\nend %s\ncmd %s\n' "$st" "$t0" "$t1" "$cmd" > "$dir/shard_$r.done"
  log "done $tag $r status $st"
}

drive() {
  echo $$ > "$PIDFILE"
  log "=== drive start pid $$"
  # clear stale claims (no .done)
  local tag r
  while read -r tag r; do
    [ -z "$tag" ] && continue
    mkdir -p "$LOGS/$tag"
    if [ -d "$LOGS/$tag/shard_$r.claim" ] && [ ! -f "$LOGS/$tag/shard_$r.done" ]; then
      rmdir "$LOGS/$tag/shard_$r.claim"
    fi
  done < "$QUEUE"
  while read -r tag r; do
    [ -z "$tag" ] && continue
    [ -f "$LOGS/$tag/shard_$r.done" ] && grep -q '^status 0$' "$LOGS/$tag/shard_$r.done" && continue
    rm -f "$LOGS/$tag/shard_$r.done"
    while :; do
      if [ -f "$DATA/STOP" ]; then break 2; fi
      local running; running="$(jobs -rp | wc -l | tr -d ' ')"
      if [ "$running" -lt "$(workers_now)" ]; then break; fi
      sleep 2
    done
    mkdir "$LOGS/$tag/shard_$r.claim" 2>/dev/null || continue
    run_shard "$tag" "$r" < /dev/null &
  done < "$QUEUE"
  [ -f "$DATA/STOP" ] && log "STOP seen; waiting for running shards"
  wait
  log "all shards ended; collecting"
  timeout 900 "$PY" "$HERE/collect.py" >> "$DRIVERLOG" 2>&1
  log "=== drive end"
  rm -f "$PIDFILE"
}

status() {
  local tag mod line total done ok
  while IFS=$'\t' read -r tag mod line; do
    [ -z "$tag" ] && continue
    case "$tag" in \#*) continue;; esac
    total="$(awk -v t="$tag" '$1 == t' "$QUEUE" | wc -l | tr -d ' ')"
    done=0; ok=0
    if [ -d "$LOGS/$tag" ]; then
      done="$(find "$LOGS/$tag" -name 'shard_*.done' | wc -l | tr -d ' ')"
      ok="$(grep -l '^status 0$' "$LOGS/$tag"/shard_*.done 2>/dev/null | wc -l | tr -d ' ')"
    fi
    outs="$(cat "$LOGS/$tag"/shard_*.g6 2>/dev/null | wc -l | tr -d ' ')"
    printf '%-26s %4s/%-4s done (%s ok)  output lines %s\n' "$tag" "$done" "$total" "$ok" "$outs"
  done < "$JOBS"
  if [ -f "$PIDFILE" ] && kill -0 "$(cat "$PIDFILE")" 2>/dev/null; then
    echo "driver alive: pid $(cat "$PIDFILE"), workers now $(workers_now)"
  else
    echo "driver not running"
  fi
  tail -n 3 "$DRIVERLOG" 2>/dev/null
}

launch() {
  if [ -f "$PIDFILE" ] && kill -0 "$(cat "$PIDFILE")" 2>/dev/null; then
    echo "driver already running: pid $(cat "$PIDFILE")"; exit 1
  fi
  mkdir -p "$LOGS" "$DATA"
  nohup nice -n 10 /bin/bash "$HERE/run_exb.sh" drive >> "$LOGS/driver.out" 2>&1 < /dev/null &
  echo "launched driver pid $!"
}

case "${1:-}" in
  launch) launch ;;
  drive) drive ;;
  status) status ;;
  *) echo "usage: run_exb.sh launch|drive|status"; exit 2 ;;
esac
