"""chain.py -- method B: ex(n) from n = 8 upward by Lemma B and edge deletion.

Counted graph: simple, bipartite, max degree <= 6, no nonempty 4-regular
subgraph.  ex(n) = max edges of a counted graph on n vertices.

  Base: ex(7) = 12.  Every bipartite graph on <= 7 vertices has max degree
  <= 6 and no nonempty 4-regular subgraph (that needs 4 vertices on each
  side), and K_{3,4} has 12 = floor(49/4) edges.
  Lemma B: a counted graph with e edges on n vertices has minimum degree
  >= e - ex(n-1) (delete a vertex of minimum degree).
  Edge deletion: a counted graph with more than e edges contains a counted
  graph with exactly e edges on the same vertices.
  Sides: with minimum degree >= t, each colour class S has
  t|S| <= e <= 6|S|.

For n = 8, 9, ...: for e = ex(n-1)+1, ex(n-1)+2, ... decide whether a
counted graph on n vertices with e edges exists, searching only the class
"minimum degree >= t = e - ex(n-1)", all side splits allowed by t|S| <= e
<= 6|S|, with bipgen (own generator + own decider; -1 stops at the first
graph found).  The first e with none gives ex(n) = e - 1 (the graph found at
e - 1 is the lower bound; each is re-decided by the PySAT decider).

Usage: python chain.py NMAX [--skip-empty N:E ...]
  --skip-empty N:E   do not run the emptiness search at (N, E); it is taken
                     from a separate (detached) run and marked so here.
Writes data/chain.txt and data/chain_witness_n<N>_e<E>.g6.
"""

import math
import os
import re
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
BIPGEN = os.path.join(HERE, "bin", "bipgen")
PY = sys.executable
sys.path.insert(0, HERE)
import deciders as D  # noqa: E402


def splits(n, e, t):
    lo = math.ceil(e / 6)
    hi = e // t if t > 0 else n
    out = []
    for a in range(0, n // 2 + 1):
        b = n - a
        if lo <= a <= hi and lo <= b <= hi:
            out.append((a, b))
    return out


def run(a, b, e, t, first):
    args = [BIPGEN, "-q"] + (["-1"] if first else []) + [str(a), str(b), f"{e}:{e}", f"{t}:{t}", "6:6"]
    t0 = time.time()
    r = subprocess.run(args, capture_output=True, text=True, timeout=3600)
    if r.returncode:
        raise RuntimeError(r.stderr)
    m = re.search(r">Z\s+(\d+) graphs", r.stderr)
    cpu = re.search(r"generated in ([0-9.]+) sec", r.stderr)
    return int(m.group(1)), r.stdout.split(), float(cpu.group(1)), time.time() - t0


def main():
    nmax = int(sys.argv[1])
    skip = set()
    if "--skip-empty" in sys.argv:
        for x in sys.argv[sys.argv.index("--skip-empty") + 1:]:
            if ":" in x:
                n_, e_ = x.split(":")
                skip.add((int(n_), int(e_)))
    ex = {7: 12}
    lines = ["# chain.py: ex(n) by Lemma B, own generator and decider",
             "ex(7) = 12 (base: bipartite on 7 vertices, K_{3,4})"]
    total_cpu = 0.0
    for n in range(8, nmax + 1):
        prev = ex[n - 1]
        e = prev + 1
        last_witness = None
        while True:
            t = e - prev
            if t > 6:
                lines.append(f"n={n} e={e}: t={t} > 6, impossible")
                break
            sp = splits(n, e, t)
            found = None
            runs = []
            empty_level = (n, e) in skip
            if empty_level:
                lines.append(f"n={n} e={e} t>={t} splits {sp}: emptiness taken from the detached runs")
                break
            for a, b in sp:
                cnt, graphs, cpu, wall = run(a, b, e, t, first=True)
                total_cpu += cpu
                runs.append(f"{a}+{b}: {cnt} ({cpu:.2f} s)")
                if cnt:
                    found = graphs[0]
                    break
            if found:
                nn, edges = D.parse_g6(found)
                has, _ = D.sat_has_h4(nn, edges)
                col = D.bicolour(nn, edges)
                deg = [0] * nn
                for u, w in edges:
                    deg[u] += 1
                    deg[w] += 1
                okg = (nn == n and len(edges) == e and col is not None and max(deg) <= 6 and not has)
                if not okg:
                    raise RuntimeError(f"witness check failed at n={n} e={e}: {found}")
                path = os.path.join(ROOT, "data", f"chain_witness_n{n}_e{e}.g6")
                with open(path, "w") as f:
                    f.write(found + "\n")
                last_witness = (e, os.path.basename(path))
                lines.append(f"n={n} e={e} t>={t}: counted graph found ({'; '.join(runs)}); "
                             f"SAT: no 4-regular subgraph; bipartite, max degree {max(deg)}")
                e += 1
                continue
            lines.append(f"n={n} e={e} t>={t} splits {sp}: none ({'; '.join(runs)})")
            break
        ex[n] = e - 1
        lw = f"witness {last_witness[1]}" if last_witness else "witness: graph for n-1 plus an isolated vertex"
        if (n, e) in skip:
            lines.append(f"=> ex({n}) >= {ex[n]}  (3n-8 = {3 * n - 8}; {lw}); ex({n}) = {ex[n]} "
                         f"exactly when the separate runs at e = {e} find no graph")
        else:
            lines.append(f"=> ex({n}) = {ex[n]}  (3n-8 = {3 * n - 8}; {lw})")
    lines.append(f"total bipgen CPU {total_cpu:.1f} s")
    out = os.path.join(ROOT, "data", "chain.txt")
    with open(out, "w") as f:
        f.write("\n".join(lines) + "\n")
    print("\n".join(lines))


if __name__ == "__main__":
    main()
