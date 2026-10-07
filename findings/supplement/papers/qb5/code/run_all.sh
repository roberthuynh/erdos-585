#!/bin/bash
# Reproduce every computation of PAPER.md Appendix A (lane qb5). About 2-4 minutes on one core.
# Inputs: P4's sparse QB(5) classes (reports/585-next/wave3/P4/checks/data/qb5_n*.g6) and nauty genbg 2.9.3.
# Writes regenerated files to $OUT (default: a scratch directory) and compares them with code/data.
set -uo pipefail
cd "$(dirname "$0")"
PY=[temporary path]
GENBG="$HOME/.cache/erdos585/nauty2_9_3/genbg"
P4=../../../wave3/P4/checks/data
OUT="${OUT:-[local scratch folder]}"
mkdir -p "$OUT"
fail=0
/usr/bin/clang -O3 -o petal petal.c && /usr/bin/clang -O3 -o clcheck clcheck.c || exit 2
echo "== A.1 petal.c on P4's sparse classes"
for f in qb5_n11_5_6 qb5_n12_6_6 qb5_n13_6_7 qb5_n14_7_7 qb5_n15_7_8; do
  echo "-- $f"; timeout 240 ./petal < "$P4/$f.g6" 2>&1 >/dev/null | grep -E "^graphs|^core|^E5|bad W-vertex"
done
echo "== A.2 regenerate tb19 and data files"
timeout 240 "$GENBG" -q -d0:1 -D2:3 6 6 10:10 > "$OUT/cut66.g6"
$PY assemble_tb.py 6 4 3 6 < "$OUT/cut66.g6" > "$OUT/tb19_all.g6"
for m in alpha beta alpha1; do $PY gen_template.py $m 300 7 > "$OUT/template_$m.g6"; done
$PY gen_j3.py u1u2 1500 11 | sort -u > "$OUT/j3_u1u2.g6"
$PY gen_j3.py u0 1500 12 | sort -u > "$OUT/j1_u0.g6"
$PY gen_e5.py 60 5 | sort -u > "$OUT/e5_n22.g6"
$PY gen_e5.py 40 9 big | sort -u > "$OUT/e5_n24.g6"
for f in tb19_all template_alpha template_beta template_alpha1 j3_u1u2 j1_u0 e5_n22 e5_n24; do
  if cmp -s "$OUT/$f.g6" "data/$f.g6"; then echo "$f reproduced"; else echo "$f DIFFERS"; fail=1; fi
done
echo "== A.2-A.4 petal.c and clcheck.c on the built families"
for f in tb19_all j3_u1u2 j1_u0 e5_n22 e5_n24; do
  echo "-- $f"; timeout 240 ./petal < "data/$f.g6" 2>&1 >/dev/null | grep -E "^graphs|^core|^E5|^alpha petals|bad W-vertex"
done
for f in template_alpha template_beta template_alpha1 j3_u1u2 tb19_split; do
  echo "-- clcheck $f"; timeout 240 ./clcheck < "data/$f.g6" 2>&1 >/dev/null
done
echo "== A.5 independent checks (verify_certs.py)"
for f in "$P4/qb5_n11_5_6.g6" "$P4/qb5_n13_6_7.g6" "$P4/qb5_n15_7_8.g6" data/tb19_all.g6 data/j3_u1u2.g6 data/j1_u0.g6; do
  timeout 600 $PY verify_certs.py c2core < "$f" || fail=1
done
head -10 data/e5_n22.g6 | timeout 600 $PY verify_certs.py e5 || fail=1
head -4 data/e5_n24.g6 | timeout 600 $PY verify_certs.py e5 || fail=1
head -3 data/tb19_split.g6 | timeout 600 $PY verify_certs.py sparse || fail=1
echo "== A.6 pairs in E5 instances"
timeout 240 $PY pairs_e5.py < data/e5_n22.g6 | awk '{print $2, $3}' | sort | uniq -c
timeout 240 $PY pairs_e5.py < data/e5_n24.g6 | awk '{print $2, $3}' | sort | uniq -c
echo "RESULT: $([ $fail = 0 ] && echo ALL-OK || echo FAILURES)"
exit $fail
