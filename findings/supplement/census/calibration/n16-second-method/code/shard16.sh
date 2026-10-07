#!/bin/bash
# Check 3 shard: plain (unpruned) stock geng -d5 -D5 16 <res>/<mod> into a file, then the SAT decider.
# Usage: shard16.sh <tag> <res> <mod>. Env: CUTOFF (epoch s; no new shard starts after it),
# DECIDER_FLAGS (extra pairsat.py flags, search heuristics only).
set -u
tag=$1; r=$2; mod=$3; n=16
LANE=[local path]
SP=[local scratch folder]
GENG=[local path]
PY=[local path]
mkdir -p "$SP" "$LANE/logs/$tag"
base="$LANE/logs/$tag/n${n}_r${r}_m${mod}"
g6="$SP/${tag}_n${n}_r${r}_m${mod}.g6"
[ -e "$base.done" ] && exit 0
if [ -n "${CUTOFF:-}" ] && [ "$(date +%s)" -ge "$CUTOFF" ]; then echo "$r" >> "$LANE/logs/$tag/skipped_after_cutoff.txt"; exit 0; fi
t0=$(date +%s)
"$GENG" -d5 -D5 "$n" "$r/$mod" > "$g6" 2> "$base.geng.err"
gst=$?
t1=$(date +%s)
"$PY" "$LANE/code/pairsat.py" "$g6" "$base" --solver m22 --n "$n" --deg 5 --log "$base.progress" --every 50000 ${DECIDER_FLAGS:-} > "$base.out" 2> "$base.err"
pst=$?
t2=$(date +%s)
lines=$(wc -l < "$g6" | tr -d ' ')
sha=$(shasum -a 256 "$g6" | cut -d' ' -f1)
echo "tag=$tag n=$n res=$r mod=$mod geng_status=$gst decider_status=$pst g6_lines=$lines g6_sha256=$sha geng_s=$((t1-t0)) decide_s=$((t2-t1))" > "$base.meta"
if [ "$gst" -eq 0 ] && [ "$pst" -eq 0 ] && grep -q '^>Z' "$base.geng.err"; then touch "$base.done"; rm -f "$g6"; fi
