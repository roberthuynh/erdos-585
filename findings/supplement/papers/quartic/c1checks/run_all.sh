#!/bin/bash
# Reproduce Appendix A of C1-PAPER.md. Run from this directory: bash run_all.sh wave1; bash run_all.sh wave2
# Every python run is under timeout 240. Each writes out_*.json and log_*.txt (last line: exit code).
PY=[temporary path]
case "${1:-}" in
  wave1)
    for i in 0 1 2 3 4 5; do
      (timeout 240 "$PY" check_subcase.py 1 "$i" 6 > "log_subcase_$i.txt" 2>&1; echo "exit $?" >> "log_subcase_$i.txt") &
    done
    (timeout 240 "$PY" check_identities.py > log_identities.txt 2>&1; echo "exit $?" >> log_identities.txt
     timeout 240 "$PY" check_core.py 7 100 > log_core.txt 2>&1; echo "exit $?" >> log_core.txt) &
    wait ;;
  wave2)
    for i in 0 1 2 3 4 5; do
      (timeout 240 "$PY" check_sparse_core.py "$i" 6 > "log_sparse_core_$i.txt" 2>&1; echo "exit $?" >> "log_sparse_core_$i.txt") &
    done
    for i in 0 1 2; do
      (timeout 240 "$PY" check_lattice_pairs.py "$i" > "log_lattice_$i.txt" 2>&1; echo "exit $?" >> "log_lattice_$i.txt") &
    done
    (timeout 240 "$PY" check_adversarial.py 200 > log_adversarial.txt 2>&1; echo "exit $?" >> log_adversarial.txt) &
    wait ;;
  *) echo "usage: bash run_all.sh wave1|wave2"; exit 2 ;;
esac
