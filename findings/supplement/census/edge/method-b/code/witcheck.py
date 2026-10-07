"""witcheck.py -- method B re-check of lower-bound witnesses (wave8/exb).

For each graph6 file given: n, edges, bipartite (own 2-colouring), side sizes,
min / max degree, e = 3n - 8, and three deciders of our own for "no nonempty
4-regular subgraph": h4filt (C search), PySAT (own CNF, Minisat 2.2; also
Glucose 4 for a second solver), and the flow method (4-factor test over all
balanced vertex subsets of the 4-core).  Writes data/WITNESS-CHECK.txt.
Usage: python witcheck.py FILE.g6 ...
"""

import os
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, HERE)
import deciders as D  # noqa: E402


def main():
    lines = []
    allok = True
    for path in sys.argv[1:]:
        for g6 in [l.strip() for l in open(path) if l.strip()]:
            n, edges = D.parse_g6(g6)
            col = D.bicolour(n, edges)
            deg = [0] * n
            for u, w in edges:
                deg[u] += 1
                deg[w] += 1
            sides = sorted([col.count(0), col.count(1)]) if col else None
            r = subprocess.run([os.path.join(HERE, "bin", "h4filt"), "-a", "-q"], input=g6 + "\n",
                               capture_output=True, text=True)
            cv = r.stdout.split()[1]
            s1, _ = D.sat_has_h4(n, edges, "minisat22")
            s2, _ = D.sat_has_h4(n, edges, "glucose4")
            t0 = time.time()
            fl = D.flow_has_h4(n, edges) if col else None
            tf = time.time() - t0
            K, _ = D.core4(n, edges, range(n))
            ok = (col is not None and max(deg) <= 6 and len(edges) == 3 * n - 8 and cv == "0"
                  and not s1 and not s2 and fl is False)
            allok &= ok
            lines.append(f"{os.path.relpath(path, ROOT)}: n={n} e={len(edges)} (3n-8={3 * n - 8}) "
                         f"bipartite={col is not None} sides={sides} mindeg={min(deg)} maxdeg={max(deg)} "
                         f"4-core size={len(K)} | h4filt: {'none' if cv == '0' else 'HAS'} | "
                         f"SAT minisat22: {'UNSAT' if not s1 else 'SAT'} | SAT glucose4: "
                         f"{'UNSAT' if not s2 else 'SAT'} | flow: {'none' if fl is False else fl} "
                         f"({tf:.1f} s) | {'OK' if ok else 'FAIL'}")
    lines.append("WITCHECK " + ("PASS" if allok else "FAIL"))
    out = os.path.join(ROOT, "data", "WITNESS-CHECK.txt")
    with open(out, "w") as f:
        f.write("\n".join(lines) + "\n")
    print("\n".join(lines))
    return 0 if allok else 1


if __name__ == "__main__":
    sys.exit(main())
