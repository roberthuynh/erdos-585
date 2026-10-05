#!/bin/bash
# Checks one declaration. Usage: ./check.sh <file.lean> <declaration>
# PASS requires: lake build exit 0, zero `sorry` in the file (comments ignored), axioms within the allowlist.
set -u -o pipefail
cd "$(dirname "$0")" || exit 2
if [ "$#" -ne 2 ]; then
  echo "usage: ./check.sh <file.lean> <declaration>, e.g. ./check.sh Openmath/Proofs/Final.lean Erdos585.maxEdges_seven" >&2
  exit 2
fi
FILE="$1"
DECL="$2"
ALLOW='^(propext|Classical\.choice|Quot\.sound)$'

MODNAME="${FILE%.lean}"; MODNAME="${MODNAME//\//.}"
echo "== lake build $MODNAME ($(cat lean-toolchain))"
if lake build "$MODNAME" 2>&1 | grep -v -E '^(✔|⚠) \[' | tail -n 25; then BUILD=ok; else BUILD=fail; fi

SORRIES=missing
if [ -f "$FILE" ]; then
  SORRIES=$(python3 - "$FILE" <<'PY'
import re, sys
s = open(sys.argv[1], encoding="utf-8").read()
s = re.sub(r"/-.*?-/", "", s, flags=re.S)   # block comments and docstrings
s = re.sub(r"--[^\n]*", "", s)              # line comments
print(len(re.findall(r"\bsorry\b", s)))
PY
  )
  echo "== sorry in $FILE, comments ignored: $SORRIES"
else
  echo "== $FILE missing"
fi

AXIOMS="n/a"; BAD=""
if [ "$BUILD" = ok ] && [ -f "$FILE" ]; then
  MOD="${FILE%.lean}"; MOD="${MOD//\//.}"
  OUT=$(printf 'import %s\nset_option linter.style.moduleDocstring false\n#print axioms %s\n' "$MOD" "$DECL" | lake env lean --stdin 2>&1)
  echo "== axioms"; echo "$OUT"
  # `#print axioms` wraps long output across lines; flatten before matching.
  FLAT=$(echo "$OUT" | tr '\n' ' ')
  AXIOMS=$(echo "$FLAT" | sed -n 's/.*depends on axioms: \[\([^]]*\)\].*/\1/p' | tr -d ' ')
  if [ -z "$AXIOMS" ] && echo "$FLAT" | grep -q "does not depend on any axioms"; then AXIOMS="none"; fi
  for a in $(echo "$AXIOMS" | tr ',' ' '); do
    [ "$a" = none ] && continue
    echo "$a" | grep -qE "$ALLOW" || BAD="$BAD $a"
  done
fi

VERDICT=FAIL
if [ "$BUILD" = ok ] && [ "$SORRIES" = 0 ] && [ -z "$BAD" ] && [ "$AXIOMS" != "n/a" ] && [ -n "$AXIOMS" ]; then VERDICT=PASS; fi
echo "RESULT: $VERDICT build=$BUILD sorry=$SORRIES axioms=[${AXIOMS}] disallowed=[${BAD# }]"
[ "$VERDICT" = PASS ]
