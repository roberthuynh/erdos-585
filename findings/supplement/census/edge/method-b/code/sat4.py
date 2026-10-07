"""sat4.py -- PySAT decider of method B (wave8/exb), own CNF (deciders.cnf_h4).

Reads graph6 lines on stdin and decides for each graph whether it has a
nonempty 4-regular subgraph.  SAT answers are checked (the model's edges
must form a 4-regular subgraph).

  --verdicts      print "<graph6> H" or "<graph6> 0" per graph on stdout
  --expect-none   exit 1 unless no graph has a 4-regular subgraph
  --solver NAME   PySAT solver name (default minisat22)
The last line on stderr: "SAT4 <n> graphs: with H <a>, without <b> [...]".
"""

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import deciders as D  # noqa: E402


def main():
    args = sys.argv[1:]
    verdicts = "--verdicts" in args
    expect_none = "--expect-none" in args
    solver = "minisat22"
    if "--solver" in args:
        solver = args[args.index("--solver") + 1]
    n_all = n_h = 0
    for line in sys.stdin:
        s = line.strip()
        if not s:
            continue
        n, edges = D.parse_g6(s)
        has, _ = D.sat_has_h4(n, edges, solver)
        n_all += 1
        n_h += has
        if verdicts:
            print(s, "H" if has else "0")
    tail = ""
    if expect_none:
        tail = " expect-none: " + ("OK" if n_h == 0 else "FAIL")
    print(f"SAT4 {n_all} graphs: with H {n_h}, without {n_all - n_h} (solver {solver}){tail}",
          file=sys.stderr)
    return 1 if (expect_none and n_h) else 0


if __name__ == "__main__":
    sys.exit(main())
