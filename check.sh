#!/bin/bash
# Checks one declaration. Usage: ./check.sh <file.lean> <declaration>
# PASS requires successful build and axiom query, zero sorry tokens, and allowed axioms.
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
from pathlib import Path
sys.path.insert(0, str(Path("scripts").resolve()))
from check_axioms import lean_code
s = lean_code(Path(sys.argv[1]).read_text(encoding="utf-8"))
print(len(re.findall(r"\bsorry\b", s)))
PY
  )
  echo "== sorry in $FILE, comments ignored: $SORRIES"
else
  echo "== $FILE missing"
fi

AXIOMS="n/a"; BAD=""; AXIOM_QUERY=not_run
if [ "$BUILD" = ok ] && [ -f "$FILE" ]; then
  MOD="${FILE%.lean}"; MOD="${MOD//\//.}"
  if OUT=$(printf 'import %s\n\n/-! Axiom audit of the requested declaration. -/\n#print axioms %s\n' "$MOD" "$DECL" | lake env lean --stdin 2>&1); then
    AXIOM_QUERY=ok
  else
    AXIOM_QUERY=fail
  fi
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
if [ "$BUILD" = ok ] && [ "$AXIOM_QUERY" = ok ] && [ "$SORRIES" = 0 ] && [ -z "$BAD" ] && [ "$AXIOMS" != "n/a" ] && [ -n "$AXIOMS" ]; then VERDICT=PASS; fi
echo "RESULT: $VERDICT build=$BUILD axiom_query=$AXIOM_QUERY sorry=$SORRIES axioms=[${AXIOMS}] disallowed=[${BAD# }]"
[ "$VERDICT" = PASS ]
