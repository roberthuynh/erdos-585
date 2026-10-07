#!/bin/bash
# run_excensus.sh: sharded, resumable census driver for the excensus lane (wave6).
#
# Jobs are rows of code/jobs.tsv (tab-separated: tag, kind, mod, binary, args). The work list is
# code/queue.txt, one "tag r" per line, run in file order by NW workers. Lines may be appended
# while the driver runs; a worker that reaches the end of the file exits.
#
# kind q4  : pruned generator (genbg_q4 / geng_q4). Output .g6 = graphs with NO 4-regular subgraph.
# kind sat : plain nauty 2.9.3 generator piped to census/sat_all.py (pysat decider). Output .g6 =
#            UNSAT graphs (no 4-regular subgraph); .sat holds "SAT n UNSAT m".
#
# Shard r of job T writes logs/T/shard_r.{g6,err} and, on success, logs/T/shard_r.done.
# A shard counts only if its .done file exists. Claims are mkdir locks logs/T/shard_r.claim.
#
# Modes:
#   launch : start the driver detached (nohup, nice 10). Refuses if a driver is running.
#            Clears stale claims first, so it is also the resume command.
#   drive  : (internal) run NW workers, wait, then run code/collect.py.
#   status : print per-job progress (collect.py --no-write).
#
# Deadlines: no shard starts at or after CUTOFF (2026-10-06 06:00 EDT); every shard runs under
# timeout so it is killed at HARDEND (06:58 EDT). Graceful stop: touch data/STOP.
set -u
E=[local path]
C="$E/code"
JOBS="${EXC_JOBS:-$C/jobs.tsv}"; export EXC_JOBS="$JOBS"
QUEUE="${EXC_QUEUE:-$C/queue.txt}"
NW=${EXC_NW:-3}
CUTOFF=1791280800    # date -j -f '%Y-%m-%d %H:%M:%S' '2026-10-06 06:00:00' +%s  (EDT)
HARDEND=1791284280   # date -j -f '%Y-%m-%d %H:%M:%S' '2026-10-06 06:58:00' +%s  (EDT)
TIMEOUT=/opt/homebrew/bin/timeout
PY=[local path]
SATALL=[local path]
SELF="$C/run_excensus.sh"
PIDFILE="$E/logs/driver.pid"

run_shard() {
  local tag=$1 r=$2 w=$3 jl kind mod bin args L rem rc t0 t1 z u
  jl=$(awk -F'\t' -v t="$tag" '$1 == t' "$JOBS")
  if [ -z "$jl" ]; then echo "$(date '+%F %T') w$w $tag $r: no such job"; return; fi
  kind=$(printf '%s\n' "$jl" | cut -f2)
  mod=$(printf '%s\n' "$jl" | cut -f3)
  bin=$(printf '%s\n' "$jl" | cut -f4)
  args=$(printf '%s\n' "$jl" | cut -f5)
  L="$E/logs/$tag"
  rem=$((HARDEND - $(date +%s)))
  if [ "$rem" -le 5 ]; then return; fi
  t0=$(date '+%F %T')
  case "$kind" in
    q4)
      # shellcheck disable=SC2086
      "$TIMEOUT" "$rem" /usr/bin/time -p "$bin" $args "$r/$mod" "$L/shard_$r.g6" 2> "$L/shard_$r.err"
      rc=$? ;;
    sat)
      "$TIMEOUT" "$rem" /usr/bin/time -p /bin/bash -c \
        "set -o pipefail; \"$bin\" $args $r/$mod | \"$PY\" \"$SATALL\" - \"$L/shard_$r.g6\" > \"$L/shard_$r.sat\"" \
        2> "$L/shard_$r.err"
      rc=$? ;;
    *) echo "$(date '+%F %T') w$w $tag: unknown kind $kind"; return ;;
  esac
  t1=$(date '+%F %T')
  z=$(grep -m1 '^>Z' "$L/shard_$r.err" | awk '{print $2}')
  u=$(awk '/^user/ {print $2}' "$L/shard_$r.err" | tail -n 1)
  if [ "$rc" -eq 0 ] && [ -n "$z" ]; then
    if [ "$kind" = sat ]; then
      printf 'tag=%s r=%s mod=%s generated=%s %s user=%s start=%s end=%s\n' \
        "$tag" "$r" "$mod" "$z" "$(cat "$L/shard_$r.sat")" "${u:-?}" "$t0" "$t1" > "$L/shard_$r.done"
    else
      printf 'tag=%s r=%s mod=%s graphs=%s user=%s start=%s end=%s\n' \
        "$tag" "$r" "$mod" "$z" "${u:-?}" "$t0" "$t1" > "$L/shard_$r.done"
    fi
  fi
  echo "$t1 w$w $tag $r/$mod rc=$rc out=${z:-none} user=${u:-?}"
}

worker() {
  local w=$1 i=0 line tag r L
  while :; do
    i=$((i + 1))
    line=$(sed -n "${i}p" "$QUEUE")
    if [ -z "$line" ]; then echo "$(date '+%F %T') w$w end of queue at line $i"; break; fi
    case "$line" in \#*) continue ;; esac
    if [ "$(date +%s)" -ge "$CUTOFF" ]; then echo "$(date '+%F %T') w$w launch cutoff reached, stopping"; break; fi
    if [ -e "$E/data/STOP" ]; then echo "$(date '+%F %T') w$w STOP file present, stopping"; break; fi
    tag=${line%% *}; r=${line##* }
    L="$E/logs/$tag"; mkdir -p "$L"
    mkdir "$L/shard_$r.claim" 2> /dev/null || continue
    if [ ! -e "$L/shard_$r.done" ]; then run_shard "$tag" "$r" "$w"; fi
    rmdir "$L/shard_$r.claim"
  done
}

case "${1:-status}" in
  launch)
    if [ -f "$PIDFILE" ] && kill -0 "$(cat "$PIDFILE")" 2> /dev/null; then
      echo "driver already running, pid $(cat "$PIDFILE")"; exit 1
    fi
    find "$E/logs" -type d -name 'shard_*.claim' -prune -exec rmdir {} \; 2> /dev/null
    nohup nice -n 10 /bin/bash "$SELF" drive >> "$E/logs/driver.log" 2>&1 < /dev/null &
    echo $! > "$PIDFILE"
    echo "driver pid $! (log $E/logs/driver.log)"
    ;;
  drive)
    echo "=== drive start $(date '+%F %T %Z') pid $$ workers $NW"
    shasum -a 256 "$JOBS" "$QUEUE"
    for ((w = 0; w < NW; w++)); do worker "$w" & done
    wait
    echo "=== workers done $(date '+%F %T %Z')"
    "$PY" "$C/collect.py"
    echo "=== drive end $(date '+%F %T %Z')"
    ;;
  status)
    "$PY" "$C/collect.py" --no-write
    ;;
  *) echo "usage: $0 launch|status"; exit 2 ;;
esac
