#!/bin/bash
# Resume a gen585 run in <=210-second slices (each under timeout 240) until it reports complete.
# Usage: run_slices.sh TAG MAXSLICES -- <gen585 args without -f/-o/-t>
# State: runs/state_TAG.txt ; finals: runs/finals_TAG.txt ; slice log: runs.log
cd "$(dirname "$0")" || exit 1
tag="$1"; max="$2"; shift 3
for ((i = 1; i <= max; i++)); do
  out=$(timeout 240 "./${GEN:-gen585}" "$@" -f "runs/state_${tag}.txt" -o "runs/finals_${tag}.txt" -t 210 2>/dev/null)
  st=$(printf '%s\n' "$out" | grep '^STATUS')
  printf '%s %s slice %d: %s\n' "$(date '+%F %T')" "$tag" "$i" "$st" >> runs.log
  printf '%s\n' "$out" > "runs/last_${tag}.txt"
  case "$st" in *"STATUS complete"*) break ;; "") echo "$(date '+%F %T') $tag slice $i: no STATUS (crash or timeout)" >> runs.log; break ;; esac
done
