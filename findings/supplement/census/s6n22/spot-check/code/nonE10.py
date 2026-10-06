#!/usr/bin/env python3
"""nonE10.py (wave8/s6spot): the non-E10 graphs found by e10cut in the e10only slices.
For each: graph6 (to data/nonE10.g6), min essential cut and the cut set S from e10cut, the 66
tests from spantest (SPAN / NO), and for every NO test two extra checks:
  (1) one-cycle SAT: does Y = B - o - y have even one Hamilton cycle? (fresh solver, lazy cuts)
  (2) counting certificate: for T in {S - o - y, V - S - o - y}, let a and b be the numbers of
      edges of delta_Y(T) whose T-end is on side A, resp. B, and d = |T_A| - |T_B|. A Hamilton
      cycle meets T in paths whose ends are T-ends of crossing edges; a path with both ends on A
      has one more A-vertex than B-vertex, and so on, so d = p_AA - p_BB. Hence one Hamilton cycle
      uses at least mA A-ends and mB B-ends, with (mA, mB) = (1, 1) if d = 0, (2d, 0) if d > 0,
      (0, -2d) if d < 0. If a < mA or b < mB: no Hamilton cycle; if a < 2 mA or b < 2 mB: no two
      edge-disjoint Hamilton cycles.
Writes data/nonE10.txt and data/nonE10.g6."""
import os, sys, json, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import spantest as sp
from pysat.solvers import Solver
D = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "data")


def one_hc(n, edges, o, y):
    V = [v for v in range(n) if v not in (o, y)]
    E = [e for e in edges if o not in e and y not in e]
    var = {e: i + 1 for i, e in enumerate(E)}
    inc = {v: [] for v in V}
    for e in E:
        inc[e[0]].append(var[e]); inc[e[1]].append(var[e])
    cl = []
    for v in V:
        xs = inc[v]
        cl += [[-a, -b, -c] for a, b, c in itertools.combinations(xs, 3)]
        cl += [list(t) for t in itertools.combinations(xs, len(xs) - 1)]
    s = Solver(name="cadical153", bootstrap_with=cl)
    try:
        while True:
            if not s.solve():
                return None
            m = set(l for l in s.get_model() if l > 0)
            nb = {}
            for e in E:
                if var[e] in m:
                    nb.setdefault(e[0], []).append(e[1]); nb.setdefault(e[1], []).append(e[0])
            cyc = sp.cycles_of(len(V), V, nb)
            if len(cyc) == 1:
                return cyc[0]
            for c in cyc:
                S = set(c)
                s.add_clause([var[e] for e in E if (e[0] in S) != (e[1] in S)])
    finally:
        s.delete()


def parity_cert(n, edges, o, y, S):
    half = n // 2
    for T in (set(S) - {o, y}, set(range(n)) - set(S) - {o, y}):
        d_edges = [e for e in edges if o not in e and y not in e and ((e[0] in T) != (e[1] in T))]
        a = sum(1 for u, v in d_edges if (u if u in T else v) < half)
        b = len(d_edges) - a
        d = sum(1 for v in T if v < half) - sum(1 for v in T if v >= half)
        mA, mB = (1, 1) if d == 0 else ((2 * d, 0) if d > 0 else (0, -2 * d))
        if a < 2 * mA or b < 2 * mB:
            kind = "no Hamilton cycle" if (a < mA or b < mB) else "no two edge-disjoint Hamilton cycles"
            return "%s: T=%s, a=%d, b=%d, d=%d" % (kind, sorted(T), a, b, d)
    return None


out, g6out = [], []
for line in open(os.path.join(D, "jobs.txt")):
    r, mode = line.split()
    P = os.path.join(D, "slices", "s" + r)
    if not os.path.exists(P + ".done"):
        continue
    sj = json.load(open(P + ".span.json"))
    lines = open(P + ".g6").read().split("\n")
    nos = {}
    for l in open(P + ".no"):
        f = dict(x.split("=") for x in l.split()[1:])
        nos.setdefault(int(f["graph"]), []).append((int(f["o"]), int(f["y"]), f["fresh"]))
    for rec in sj["non_e10_graphs"]:
        gi = rec["index"]
        n, E = sp.decode_g6(lines[gi])
        S = [v for v in range(n) if int(rec["cutset_mask"], 16) >> v & 1]
        cut = [e for e in E if (e[0] in S) != (e[1] in S)]
        g6out.append(lines[gi])
        out.append("slice %s (mode %s) graph index %d: min essential cut %d, S = %s (|S_A| = %d, "
                   "|S_B| = %d), cut edges %s" % (r, mode, gi, rec["mincut"], S,
                   sum(v < 11 for v in S), sum(v >= 11 for v in S), cut))
        t = rec.get("tests")
        if t is None:
            out.append("  tests: not run")
            continue
        no = nos.get(gi, [])
        out.append("  tests: %d SPAN (witness verified), %d NO (both SAT encodings): %s" % (
            t["SPAN"], t["NO"], [(o, y) for o, y, _ in no]))
        out.append("  NO edges are exactly the cut edges: %s" % (sorted((o, y) for o, y, _ in no) == sorted(cut)))
        for o, y, fr in no:
            hc = one_hc(n, E, o, y)
            cert = parity_cert(n, E, o, y, S)
            out.append("  NO (%d,%d): second encoding %s; one Hamilton cycle in Y: %s; counting certificate: %s" % (
                o, y, fr, "none (UNSAT)" if hc is None else "exists", cert))
open(os.path.join(D, "nonE10.txt"), "w").write("\n".join(out) + "\n")
open(os.path.join(D, "nonE10.g6"), "w").write("\n".join(g6out) + "\n")
print("\n".join(out))
