#!/usr/bin/env python3
"""Check the frozen statement and axioms of the listed proved declarations."""
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
STATEMENT_SHA256 = "a3db41edba984fc3ab9bce5eda89e1856ea91b2190d01264d61f8fb2a9566603"
# Proof holes, and the ways to skip or extend the kernel listed in the Lean reference's
# "Validating a Lean Proof".
DISALLOWED = (r"\b(?:sorry|admit|native_decide|ofReduceBool|ofReduceNat|implemented_by|extern|unsafe|axiom)\b"
              r"|decide\s*\+native|debug\.skipKernelTC")


def lean_code(text):
    """Remove nested comments and string literals before inspecting source tokens."""
    result = []
    i = depth = 0
    string = False
    while i < len(text):
        pair = text[i:i + 2]
        if depth:
            if pair == "/-":
                depth += 1
                i += 2
            elif pair == "-/":
                depth -= 1
                i += 2
                result.append(" ")
            else:
                i += 1
        elif string:
            if text[i] == "\\":
                i += 2
            elif text[i] == '"':
                string = False
                i += 1
                result.append(" ")
            else:
                i += 1
        elif pair == "/-":
            depth = 1
            i += 2
        elif pair == "--":
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
        elif text[i] == '"':
            string = True
            i += 1
        else:
            result.append(text[i])
            i += 1
    if depth or string:
        raise ValueError("Unterminated source comment or string")
    return "".join(result)


def parse_checks(output, names):
    """Split `#check @name` output into name -> type, with whitespace normalized."""
    types, current = {}, None
    for line in output.splitlines():
        head = next((n for n in names if line.startswith(f"@{n} :") or line.startswith(f"{n} :")), None)
        if head is not None:
            current = head
            types[current] = line.split(" :", 1)[1]
        elif current is not None:
            types[current] += " " + line
    missing = [n for n in names if n not in types]
    if missing:
        raise ValueError(f"No #check output for {missing}")
    return {n: " ".join(t.split()) for n, t in types.items()}


def main():
    if hashlib.sha256((ROOT / "Openmath/Target.lean").read_bytes()).hexdigest() != STATEMENT_SHA256:
        raise ValueError("Statement differs from the frozen submitted file")
    sources = sorted((ROOT / "Openmath/Proofs").rglob("*.lean")) + [ROOT / "Openmath.lean", ROOT / "Axioms.lean"]
    for path in sources:
        if re.search(DISALLOWED, lean_code(path.read_text())):
            raise ValueError(f"Disallowed proof token in {path.relative_to(ROOT)}")
    entries = json.loads((ROOT / "scripts/headline-theorems.json").read_text())
    expected = {entry["declaration"] for entry in entries}
    if len(expected) != len(entries) or not expected:
        raise ValueError("Empty or duplicate theorem list")
    printed = re.findall(r"^#print axioms (\S+)$", (ROOT / "Axioms.lean").read_text(), re.M)
    if len(printed) != len(expected) or set(printed) != expected:
        raise ValueError("Axiom driver does not match the theorem list")
    result = subprocess.run(["lake", "env", "lean", "Axioms.lean"], cwd=ROOT,
                            capture_output=True, text=True, timeout=240)
    print(result.stdout, end="")
    print(result.stderr, end="", file=sys.stderr)
    if result.returncode:
        return result.returncode
    records = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", result.stdout)
    records += [(name, "") for name in re.findall(
        r"'([^']+)' does not depend on any axioms", result.stdout)]
    if len(records) != len(expected) or {name for name, _ in records} != expected:
        raise ValueError("Missing, duplicate, or unexpected axiom output")
    for name, axioms in records:
        bad = {x.strip() for x in axioms.split(",") if x.strip()} - ALLOWED
        if bad:
            raise ValueError(f"{name}: disallowed axioms {sorted(bad)}")
    print(f"AXIOMS: PASS ({len(expected)} proved declarations)")
    # Freeze the headline statements: each `#check @name` must print the type recorded in the list.
    imports = sorted({entry["module"] for entry in entries})
    checks = "".join(f"import {m}\n" for m in imports) + "set_option linter.style.moduleDocstring false\n"
    checks += "".join(f"#check @{entry['declaration']}\n" for entry in entries)
    result = subprocess.run(["lake", "env", "lean", "--stdin"], cwd=ROOT,
                            input=checks, capture_output=True, text=True, timeout=240)
    if result.returncode:
        print(result.stdout, end="")
        print(result.stderr, end="", file=sys.stderr)
        return result.returncode
    printed_types = parse_checks(result.stdout, [entry["declaration"] for entry in entries])
    for entry in entries:
        if " ".join(entry.get("type", "").split()) != printed_types[entry["declaration"]]:
            raise ValueError(f"{entry['declaration']}: statement differs from the recorded type")
    print(f"STATEMENTS: PASS ({len(entries)} recorded types)")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (ValueError, OSError, subprocess.TimeoutExpired) as error:
        print(f"AXIOMS: FAIL: {error}", file=sys.stderr)
        sys.exit(1)
