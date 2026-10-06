#!/bin/bash
# pipecheck.sh -- validate the method B pipeline on a small class (wave8/exb).
# Usage: pipecheck.sh TAG "GENG-ARGS" [REFERENCE.g6]
#   A = geng_h4 GENG-ARGS                  (pruned by the own decider)
#   B = geng_plain GENG-ARGS | h4filt      (whole class, own decider on each graph)
#   C = B re-decided by the PySAT decider (sat4.py, own encoding)
# Compares A and B as sets of canonical forms (nauty labelg), and with the
# reference file if given (canonical forms, after labelg).
set -uo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(dirname "$HERE")"
BIN="$HERE/bin"
LABELG="$HOME/.cache/erdos585/nauty2_9_3/labelg"
PY="$HOME/.cache/erdos585/venv/bin/python"
TAG="$1"; ARGS="$2"; REF="${3:-}"
OUT="$ROOT/data/pipecheck/$TAG"
mkdir -p "$OUT"
read -r -a A <<< "$ARGS"
{ /usr/bin/time -p "$BIN/geng_h4" "${A[@]}" > "$OUT/pruned.g6"; } 2> "$OUT/pruned.err"
{ /usr/bin/time -p "$BIN/geng_plain" "${A[@]}" | "$BIN/h4filt" > "$OUT/plain_filtered.g6"; } 2> "$OUT/plain.err"
"$LABELG" -q "$OUT/pruned.g6" 2>/dev/null | LC_ALL=C sort > "$OUT/pruned.can"
"$LABELG" -q "$OUT/plain_filtered.g6" 2>/dev/null | LC_ALL=C sort > "$OUT/plain.can"
np=$(wc -l < "$OUT/pruned.g6" | tr -d ' ')
nf=$(wc -l < "$OUT/plain_filtered.g6" | tr -d ' ')
same=$(cmp -s "$OUT/pruned.can" "$OUT/plain.can" && echo yes || echo NO)
dupp=$(uniq -d "$OUT/pruned.can" | wc -l | tr -d ' ')
gen=$(grep -E '^>Z' "$OUT/plain.err" | head -1)
tot=$(grep -E '^>T' "$OUT/plain.err" | head -1)
sat=$("$PY" "$HERE/sat4.py" --expect-none < "$OUT/plain_filtered.g6" 2>&1 | tail -1)
line="$TAG | geng $ARGS | pruned $np | plain+h4filt $nf | same set: $same | dup canon in pruned: $dupp | plain: $gen; $tot | SAT on plain output: $sat"
if [ -n "$REF" ]; then
  "$LABELG" -q "$REF" 2>/dev/null | LC_ALL=C sort > "$OUT/ref.can"
  nr=$(wc -l < "$OUT/ref.can" | tr -d ' ')
  sr=$(cmp -s "$OUT/ref.can" "$OUT/plain.can" && echo yes || echo NO)
  line="$line | reference $nr, same set: $sr"
fi
grep -E '^>Z|^real|^user' "$OUT/pruned.err" | tr '\n' ' ' | sed 's/^/pruned run: /' >> "$OUT/summary.txt"
echo >> "$OUT/summary.txt"
echo "$line" | tee -a "$OUT/summary.txt"
