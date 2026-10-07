#!/bin/bash
# exp_budget.sh in.g6 tag shard "opts1" "opts2" ...: run s6n22 with each option set, print key counters.
D="$(cd "$(dirname "$0")/.." && pwd)"
in="$1"; tag="$2"; sh="$3"; shift 3
i=0
for opts in "$@"; do
  i=$((i+1))
  # shellcheck disable=SC2086
  timeout 240 nice -n 10 "$D/code/s6n22" $opts -p "${tag}_$i" -s "$sh" -q < "$in"
  echo "[$opts] $(grep -E '^(graphs|tests|t1_solved|t1_stalls|t2_solved|survivors|verify_fail|sec_e10|sec_t1|sec_t2|t2_nodes)=' "${tag}_$i.sum" | tr '\n' ' ')"
done
