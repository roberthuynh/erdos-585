#!/bin/bash
# Validation of the PRUNE hook: pruned geng output counts against the B-1 ladder (CALIBRATION.md R2)
# and against "plain geng | pairc f" on the same parameters.
set -u
HERE="$(cd "$(dirname "$0")" && pwd)"
G="$HOME/.cache/erdos585/nauty2_9_3/geng"
P="$HERE/../../../../585-fable/tools/pairc"
T="${TMPDIR:-/tmp}"
for spec in "9 21:21" "9 20:20" "10 23:23" "10 22:22" "11 26:26" "11 27:27" "10 0:25" "8 0:20"; do
  set -- $spec
  n=$1; e=$2
  plain=$("$G" -q -d3 -D5 "$n" "$e" | "$P" f 2>/dev/null | sort | shasum | cut -c1-12)
  plainc=$("$G" -q -d3 -D5 "$n" "$e" | "$P" f 2>/dev/null | wc -l | tr -d ' ')
  pr=$("$HERE/geng_pp" -q -d3 -D5 "$n" "$e" 2>/dev/null | "$HOME/.cache/erdos585/nauty2_9_3/labelg" -q 2>/dev/null | sort | shasum | cut -c1-12)
  pl=$("$G" -q -d3 -D5 "$n" "$e" | "$P" f 2>/dev/null | "$HOME/.cache/erdos585/nauty2_9_3/labelg" -q 2>/dev/null | sort | shasum | cut -c1-12)
  prc=$("$HERE/geng_pp" -q -d3 -D5 "$n" "$e" 2>/dev/null | wc -l | tr -d ' ')
  echo "n=$n e=$e plain_geng+pairc_free=$plainc pruned_geng_out=$prc canon_sets_equal=$([ "$pr" = "$pl" ] && echo yes || echo NO)"
done
