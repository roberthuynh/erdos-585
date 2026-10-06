#!/bin/bash
# Session 3 re-runs for PAPER Appendix A (saved outputs). Run from wave4/theory. Each step time-limited.
cd "$(dirname "$0")"
G="$HOME/.cache/erdos585/nauty2_9_3/genbg"
PC="../../../585-fable/tools/pairc"
PY="$HOME/.cache/erdos585/venv/bin/python"
# (1) pair-free 5+5 bipartite graphs by edge count (Lemma 6.1(a)); genbg default: no degree bounds
: > census55.out
for e in 18 19 20 21 22 23 24 25; do
  "$G" -q 5 5 "$e:$e" > "census55_e$e.g6"
  timeout 240 "$PC" f < "census55_e$e.g6" > "census55_e$e.pairfree" 2> "census55_e$e.err"
  echo "e=$e graphs=$(wc -l < census55_e$e.g6 | tr -d ' ') pairfree=$(wc -l < census55_e$e.pairfree | tr -d ' ') [$(tr '\n' ' ' < census55_e$e.err)]" >> census55.out
done
# (2) check_lp.py re-run, seeds 11-14 (a = 8, 6 trials each), and (3) check_identities.py (40 instances)
for s in 11 12 13 14; do
  ( nice -n 10 timeout 600 "$PY" check_lp.py "$s" 8 6 > "check_lp_s3_$s.out" 2>&1 ) &
done
( nice -n 10 timeout 600 "$PY" check_identities.py 7 40 > check_identities_s3.out 2>&1 ) &
wait
echo done > final_checks.DONE
