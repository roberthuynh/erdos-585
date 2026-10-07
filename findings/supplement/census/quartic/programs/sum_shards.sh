#!/bin/bash
# sum_shards.sh TAG MOD
# Sums a sharded census run written by a census/run_*.sh script.
# Checks every shard 0..MOD-1 finished (its .err has a ">Z" line), sums the graph counts and the
# user CPU seconds, lists missing shards, and concatenates any output graphs into
# logs/TAG/found.g6. If any graph was found it re-decides each one with validate_sat.py
# --expect-unsat (independent pysat check) and says so loudly.
set -u
TAG=$1; MOD=$2
C=[local path]
L="$C/logs/$TAG"
PY=[temporary path]
V=[local path]
total=0; done_n=0; missing=(); cpu=0
for ((r = 0; r < MOD; r++)); do
  err="$L/shard_$r.err"
  z=$(grep -m1 '^>Z' "$err" 2>/dev/null)
  if [ -z "$z" ]; then missing+=("$r"); continue; fi
  c=$(printf '%s\n' "$z" | awk '{print $2}')
  u=$(awk '/^user/ {print $2}' "$err")
  total=$((total + c)); done_n=$((done_n + 1))
  cpu=$(awk -v a="$cpu" -v b="${u:-0}" 'BEGIN {printf "%.2f", a + b}')
done
: > "$L/found.g6"
for ((r = 0; r < MOD; r++)); do
  [ -s "$L/shard_$r.g6" ] && cat "$L/shard_$r.g6" >> "$L/found.g6"
done
nfound=$(grep -c . "$L/found.g6")
echo "TAG=$TAG MOD=$MOD finished=$done_n/$MOD graphs=$total found_lines=$nfound user_cpu_s=$cpu"
if [ "${#missing[@]}" -gt 0 ]; then
  echo "MISSING shards (${#missing[@]}): ${missing[*]:0:50}"
fi
if [ "$nfound" -gt 0 ]; then
  echo "!!! $nfound graph(s) with no 4-regular subgraph reported: re-deciding with validate_sat.py --expect-unsat"
  "$PY" "$V" --expect-unsat "$L/found.g6"; echo "validate_sat exit $?"
fi
