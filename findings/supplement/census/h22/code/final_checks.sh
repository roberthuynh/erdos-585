#!/bin/bash
# wave4/h22b: checks after all n=22 shards are done. Writes data/final/*, logs to stdout.
# usage: final_checks.sh   (run from anywhere; detached with nohup)
set -u
D="$(cd "$(dirname "$0")/.." && pwd)"
cd "$D" || exit 1
PY=python3
VPY="$HOME/.cache/erdos585/venv/bin/python"
L="$HOME/.cache/erdos585/nauty2_9_3/labelg"
O=data/final
mkdir -p "$O"
step() { echo "$(date '+%F %T') $*"; }

step "collect"
$PY code/collect.py data/n22 2000 > "$O/collect.txt"; echo "collect_exit=$?"
cat "$O/collect.txt"

/bin/ls data/n22 | grep '^s_[0-9]*\.out\.gz$' | sed 's|^|data/n22/|' | sort -t_ -k2 -n > "$O/files.list"
step "files=$(wc -l < "$O/files.list")"

step "verify_certs (4 parallel parts)"
rm -f "$O"/files.part.*
split -l 500 "$O/files.list" "$O/files.part."
for p in "$O"/files.part.*; do
  ( xargs $PY code/verify_certs.py < "$p" > "$p.verify" 2>&1; echo "$p verify_exit=$?" ) &
done
wait
cat "$O"/files.part.*.verify > "$O/verify.txt"
grep '^verify_certs' "$O/verify.txt" | awk '{for(i=2;i<=NF;i++){split($i,a,"="); s[a[1]]+=a[2]}} END{for(k in s) printf "%s=%d ", k, s[k]; print ""}' > "$O/verify_sum.txt"
cat "$O/verify_sum.txt"
grep -c '^FAIL\|^LISTED' "$O/verify.txt"

step "extract C / X / E lines, all g6"
xargs gzip -dc < "$O/files.list" > "$O/all_lines.txt"
awk '$2=="C"' "$O/all_lines.txt" > "$O/cut_lines.txt"
awk '$2=="X" || $2=="E"' "$O/all_lines.txt" > "$O/exceptions.txt"
awk '$2=="H"' "$O/all_lines.txt" | awk 'NR % 1000 == 1' > "$O/H_sample.txt"
cut -d' ' -f1 "$O/all_lines.txt" > "$O/all.g6"
step "lines=$(wc -l < "$O/all_lines.txt") C=$(wc -l < "$O/cut_lines.txt") XE=$(wc -l < "$O/exceptions.txt") Hsample=$(wc -l < "$O/H_sample.txt")"
step "distinct g6 strings: $(sort -u "$O/all.g6" | wc -l)"

step "SAT on cut graphs"
$VPY code/sat_hd.py "$O/cut_lines.txt" > "$O/cut_sat.txt" 2> "$O/cut_sat.err"; echo "sat_exit=$?"; cat "$O/cut_sat.err"
if [ -s "$O/exceptions.txt" ]; then
  step "SAT on exceptions"
  $VPY code/sat_hd.py "$O/exceptions.txt" > "$O/exc_sat.txt" 2> "$O/exc_sat.err"; cat "$O/exc_sat.err"
fi
step "SAT on 1-in-1000 sample of HD graphs"
$VPY code/sat_hd.py "$O/H_sample.txt" > "$O/H_sample_sat.txt" 2> "$O/H_sample_sat.err"; echo "sat_exit=$?"; cat "$O/H_sample_sat.err"

step "labelg: uncoloured canonical forms of all graphs (duplicate check)"
"$L" -q "$O/all.g6" "$O/all.can"; echo "labelg_exit=$?"
step "canonical lines=$(wc -l < "$O/all.can") distinct=$(sort -u "$O/all.can" | wc -l)"

step "labelg: cut graphs vs original 236 non-HD"
cut -d' ' -f1 "$O/cut_lines.txt" > "$O/cut.g6"
"$L" -q "$O/cut.g6" "$O/cut.can"
"$L" -q ../../wave3/pairs/data/q4bip_a11_nonhd.g6 "$O/orig236.can"
sort -u "$O/cut.can" > "$O/cut.can.sorted"; sort -u "$O/orig236.can" > "$O/orig236.can.sorted"
step "mine distinct=$(wc -l < "$O/cut.can.sorted") original lines=$(wc -l < ../../wave3/pairs/data/q4bip_a11_nonhd.g6) original distinct=$(wc -l < "$O/orig236.can.sorted") identical=$(cmp -s "$O/cut.can.sorted" "$O/orig236.can.sorted" && echo yes || echo no)"

step "swap flags vs labelg 2-coloured canonical forms, all graphs"
$PY code/swap_labelg_prep.py "$O/swap_all" "$O/all_lines.txt"
FS="-faaaaaaaaaaabbbbbbbbbbb"
"$L" -q "$FS" "$O/swap_all.A.g6" "$O/swap_all.A.can"
"$L" -q "$FS" "$O/swap_all.B.g6" "$O/swap_all.B.can"
paste -d' ' "$O/swap_all.A.can" "$O/swap_all.B.can" "$O/swap_all.flags" \
  | awk '{l=($1==$2)?1:0; c[l" "$3]++} END{for(k in c) print "labelg_swap mine_swap:", k, c[k]}' > "$O/swap_cmp.txt"
cat "$O/swap_cmp.txt"
rm -f "$O/swap_all.A.g6" "$O/swap_all.B.g6" "$O/swap_all.A.can" "$O/swap_all.B.can"

step "geng CPU seconds (sum of >Z lines)"
grep -h '^>Z' data/n22/s_*.gerr | awk '{s+=$6; n++} END{printf "shards=%d geng_cpu_s=%.1f geng_cpu_h=%.2f\n", n, s, s/3600}' | tee "$O/geng_cpu.txt"
step "FINAL CHECKS DONE"
echo done > "$O/DONE"
