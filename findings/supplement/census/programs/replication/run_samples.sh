#!/bin/bash
# usage: run_samples.sh TAG "GENGARGS" MOD RES...
cd "$(dirname "$0")/.." || exit 1
tag="$1"; args="$2"; mod="$3"; shift 3
for r in "$@"; do
  /usr/bin/time -p env RV_SP=5 RV_SPMIN=2 timeout 240 ./rvgeng $args "$r/$mod" "samp/out_${tag}_$r.g6" 2> "samp/err_${tag}_$r.txt"
  echo "$tag res=$r rc=$? $(grep -h '>Z' samp/err_${tag}_$r.txt) $(grep -h '^real' samp/err_${tag}_$r.txt)" >> samp/summary.txt
done
