#!/bin/bash
# run_shard.sh r: slice r of MOD (genbg -X-3 -d6:6 -D6:6 11 11 r/MOD) through s6n22, SAT on the
# survivors (if any), then the done marker. Skips a slice that has a done marker; a slice without
# one is redone from scratch. Outputs: data/shards/<r/100>/s<r>.{sum,stall,surv,bad,genbg.err,done}.
set -u
D="$(cd "$(dirname "$0")/.." && pwd)"
G="$HOME/.cache/erdos585/nauty2_9_3/genbg"
PY="$HOME/.cache/erdos585/venv/bin/python"
MOD=10000
OPTS=(-q -A 4 -M 64 -X 1000 -F 1000 -R 3 -N 50000 -B 5000000)
r="$1"
if [ -e "$D/STOP" ] || [ "$(date +%s)" -ge "${STOP_EPOCH:-9999999999}" ]; then exit 0; fi
S="$D/data/shards/$((r / 100))"
mkdir -p "$S"
P="$S/s$r"
[ -e "$P.done" ] && exit 0
t0=$(date +%s)
"$G" -X-3 -d6:6 -D6:6 11 11 "$r/$MOD" 2> "$P.genbg.err" | "$D/code/s6n22" -p "$P" -s "$r" "${OPTS[@]}"
st=("${PIPESTATUS[@]}")
if [ "${st[0]}" != 0 ] || [ "${st[1]}" != 0 ]; then
  echo "$(date '+%F %T') r=$r FAILED pipestatus=${st[*]}" >> "$D/logs/failed.txt"; exit 1
fi
gen=$(grep -o '>Z [0-9]* graphs' "$P.genbg.err" | awk '{print $2}')
got=$(grep '^graphs=' "$P.sum" | cut -d= -f2)
if [ -z "$gen" ] || [ "$gen" != "$got" ]; then
  echo "$(date '+%F %T') r=$r COUNT_MISMATCH gen=$gen got=$got" >> "$D/logs/failed.txt"; exit 1
fi
if [ -s "$P.surv" ]; then
  if ! "$PY" "$D/code/sat_check.py" "$P.surv" "$P.sat.jsonl" --seconds 600 > "$P.sat.log" 2>&1; then
    echo "$(date '+%F %T') r=$r SAT_FAILED" >> "$D/logs/failed.txt"; exit 1
  fi
fi
echo "gen=$gen start=$t0 end=$(date +%s)" > "$P.done"
