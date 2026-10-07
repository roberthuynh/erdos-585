#!/bin/bash
# run_selftest.sh: end-to-end test of the launch-script template on a run with known output (290 graphs).
# plain geng + pairc). Command: geng_q4 -b -d4 -D6 18 50:54 r/40, r = 0..39.
# Cores: 12 concurrent (nice 15). Projected: ~340 core-s (0.1 core-h), ~1 min wall on 12 cores
# (pilot: shards 0,13,26,39 of 40 took 6.8-9.7 s each, 2026-10-04, machine load 4-13).
# Expected output: 0 graphs (every shard .err ends '>Z 0 graphs generated'; found.g6 empty).
# Already known by other methods: plain geng + pairc (CHECKPOINT-05) and genbg_q4 9 9 50:54 (0, 57 s).
# Launch:  bash [local path]
#          (detaches itself: nohup nice -n 15, at most 12 shards at a time; driver log in
#          census/logs/selftest/driver.log, shard i writes logs/selftest/shard_i.g6 and shard_i.err)
# Status:  bash [local path] selftest 40
# Stop:    pkill -f 'run_selftest.sh'; then pkill -f 'geng_q4 -b -d4 -D6 14 30:42 '
# Restart: run the launch line again; shards whose .err already has a ">Z" line are skipped.
set -u
TAG=selftest
MOD=8
MAXJ=12
BIN=[local path]
ARGS=(-b -d4 -D6 14 30:42)
C=[local path]
L="$C/logs/$TAG"
SELF="$C/run_$TAG.sh"
mkdir -p "$L"
case "${1:-launch}" in
  launch)
    echo "launching $TAG: $MOD shards, $MAXJ at a time, nice 15; driver log $L/driver.log"
    nohup nice -n 15 /bin/bash "$SELF" drive > "$L/driver.log" 2>&1 < /dev/null &
    echo "driver pid $!"
    ;;
  drive)
    echo "start $(date)"
    echo "cmd: $BIN ${ARGS[*]} r/$MOD (r = 0..$((MOD - 1)))"
    shasum -a 256 "$BIN"
    seq 0 $((MOD - 1)) | xargs -P "$MAXJ" -n 1 /bin/bash "$SELF" shard
    echo "end $(date)"
    /bin/bash "$C/sum_shards.sh" "$TAG" "$MOD"
    ;;
  shard)
    r=$2
    if grep -q '^>Z' "$L/shard_$r.err" 2>/dev/null; then exit 0; fi
    /usr/bin/time -p "$BIN" "${ARGS[@]}" "$r/$MOD" "$L/shard_$r.g6" 2> "$L/shard_$r.err"
    ;;
esac
