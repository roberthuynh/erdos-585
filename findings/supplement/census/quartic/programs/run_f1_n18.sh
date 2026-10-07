#!/bin/bash
# run_f1_n18.sh: the last open piece of F1 at n = 18 (bipartite, δ ≥ 4, Δ ≤ 6, e ≥ 48 ⇒ 4-regular
# subgraph). Sides are 8 + 10 (then e = 48) or 9 + 9. Already 0 graphs: `genbg_q4 -u -d4:4 -D6:6
# 10 8 48:48` (2.6 s) and `genbg_q4 -u -d4:4 -D6:6 9 9 50:54` (57 s). Left: sides 9 + 9, e = 48, 49:
#   genbg_q4 -X-2 -d4:4 -D6:6 9 9 48:49 r/24,  r = 0..23.
# Cores: 12 concurrent (nice 15). Projected: ~700 core-s (0.2 core-h), ~2 min wall on 12 cores.
# Pilot (2026-10-05, load ~30): unsplit run hit the 240 s cap (220 s CPU); -X-2 shards 0, 100 of
# mod 200 took 5.9, 4.9 s and shard 7 of mod 20 took 35.2 s, all 0 graphs. Fit t = P + W/mod:
# P ~ 2.1 s, W ~ 660 s.
# Expected output: 0 graphs. Any graph found is a 4-regular-free bipartite graph with δ ≥ 4,
# Δ ≤ 6 and e = 3n − 6 or 3n − 5 at n = 18: sum_shards.sh re-decides it with
# validate_sat.py --expect-unsat. Report it to the lead at once.
# Launch:  bash [local path]
#          (detaches itself: nohup nice -n 15, at most 12 shards at a time; driver log in
#          census/logs/f1_n18/driver.log, shard i writes logs/f1_n18/shard_i.g6 and shard_i.err)
# Status:  bash [local path] f1_n18 24
# Stop:    pkill -f 'run_f1_n18.sh'; then pkill -f 'genbg_q4 -X-2 -d4:4 -D6:6 9 9 48:49 '
# Restart: run the launch line again; shards whose .err already has a ">Z" line are skipped.
set -u
TAG=f1_n18
MOD=24
MAXJ=12
BIN=[local path]
ARGS=(-X-2 -d4:4 -D6:6 9 9 48:49)
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
