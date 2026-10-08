#!/usr/bin/env python3
"""Exercise oracle failure paths with a mocked Lake command, without testing mathematics."""
from pathlib import Path
import json
import os
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent.parent
CASES = [
    ("allowed axioms", "allowed", False, True),
    ("no axioms", "none", False, True),
    ("query fails after printing allowed axioms", "query_failure", False, False),
    ("build fails", "build_failure", False, False),
    ("disallowed axiom", "disallowed", False, False),
    ("missing axiom record", "no_record", False, False),
    ("actual sorry token", "allowed", True, False),
    ("nested comments and string literal", "allowed", "comments", True),
    ("source file missing", "allowed", "missing", False),
]
MOCK = '''#!/usr/bin/env python3
import os, sys
mode = os.environ["ORACLE_TEST_MODE"]
if sys.argv[1] == "build":
    print("mock build output")
    sys.exit(1 if mode == "build_failure" else 0)
if mode == "query_failure":
    print("error: simulated axiom-query failure")
if mode == "none":
    print("'Fixture.sample' does not depend on any axioms")
elif mode == "disallowed":
    print("'Fixture.sample' depends on axioms: [sorryAx]")
elif mode != "no_record":
    print("'Fixture.sample' depends on axioms: [propext, Classical.choice, Quot.sound]")
sys.exit(1 if mode == "query_failure" else 0)
'''


def main():
    results = []
    with tempfile.TemporaryDirectory(prefix="check-sh-test-") as directory:
        work = Path(directory)
        (work / "scripts").mkdir()
        shutil.copy2(ROOT / "check.sh", work / "check.sh")
        shutil.copy2(ROOT / "scripts/check_axioms.py", work / "scripts/check_axioms.py")
        (work / "lean-toolchain").write_text("mocked-for-failure-path-test\n")
        (work / "bin").mkdir()
        mock = work / "bin/lake"
        mock.write_text(MOCK)
        mock.chmod(0o755)
        for title, mode, source_kind, expected in CASES:
            fixture = work / "Fixture.lean"
            if source_kind == "missing":
                fixture.unlink(missing_ok=True)
            elif source_kind == "comments":
                fixture.write_text('/- outer /- sorry -/ still a comment -/\n'
                                   'def message := "sorry"\n'
                                   'theorem sample : True := by trivial\n')
            else:
                fixture.write_text("theorem sample : True := by " +
                                   ("sorry" if source_kind else "trivial") + "\n")
            environment = dict(os.environ, ORACLE_TEST_MODE=mode,
                               PATH=str(work / "bin") + os.pathsep + os.environ["PATH"],
                               PYTHONDONTWRITEBYTECODE="1")
            run = subprocess.run(["bash", "check.sh", "Fixture.lean", "Fixture.sample"],
                                 cwd=work, env=environment, capture_output=True, text=True, timeout=30)
            observed = run.returncode == 0 and "RESULT: PASS" in run.stdout
            assert observed == expected, (title, run.returncode, run.stdout, run.stderr)
            if not expected:
                assert run.returncode != 0 and "RESULT: FAIL" in run.stdout, title
            if mode == "query_failure":
                assert "axiom_query=fail" in run.stdout, run.stdout
            results.append({"case": title, "expected_pass": expected,
                            "exit": run.returncode, "observed_pass": observed})
    print(json.dumps({"oracle_failure_paths": "PASS", "cases": results,
                      "mathematical_proofs_tested": False}, indent=2))


if __name__ == "__main__":
    main()
