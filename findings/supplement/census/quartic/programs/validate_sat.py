"""Independent check of 4-regular-subgraph existence by SAT (pysat), plus witness checks.

CNF: x_e for each edge, y_v for each vertex.
  x_e -> y_u, x_e -> y_v;  at most 4 of the x_e at v (all 5-subsets);
  y_v -> at least 4 of the x_e at v (every (d-3)-subset of incident edges has a true one);
  OR of all y_v (nonempty).
A model is a nonempty subgraph with every degree in {0, 4}.

Usage: python validate_sat.py FILE.g6 [FILE.g6 ...]
  prints, per file, how many graphs are SAT (have one) / UNSAT, and checks each SAT model.
  With --expect-unsat, exits 1 if any graph is SAT.
"""
import sys, itertools
import networkx as nx
from pysat.solvers import Solver


def has_q4(g):
    nodes = list(g.nodes())
    idx = {v: i + 1 for i, v in enumerate(nodes)}
    edges = list(g.edges())
    ev = {e: len(nodes) + 1 + i for i, e in enumerate(edges)}
    inc = {v: [] for v in nodes}
    for (u, v), x in ev.items():
        inc[u].append(x); inc[v].append(x)
    cl = []
    for (u, v), x in ev.items():
        cl.append([-x, idx[u]]); cl.append([-x, idx[v]])
    for v in nodes:
        xs = inc[v]; d = len(xs)
        for B in itertools.combinations(xs, 5):
            cl.append([-b for b in B])
        if d < 4:
            cl.append([-idx[v]])
        else:
            for A in itertools.combinations(xs, d - 3):
                cl.append([-idx[v]] + list(A))
    cl.append([idx[v] for v in nodes])
    with Solver(name="cadical153", bootstrap_with=cl) as s:
        if not s.solve():
            return None
        m = set(l for l in s.get_model() if l > 0)
        H = nx.Graph([e for e, x in ev.items() if x in m])
        return H


def check_witness(g, H):
    assert H.number_of_edges() > 0
    assert all(g.has_edge(u, v) for u, v in H.edges())
    assert all(d == 4 for _, d in H.degree())
    return True


if __name__ == "__main__":
    expect_unsat = "--expect-unsat" in sys.argv
    bad = 0
    for fn in [a for a in sys.argv[1:] if not a.startswith("--")]:
        sat = unsat = 0
        for line in open(fn):
            line = line.strip()
            if not line:
                continue
            g = nx.from_graph6_bytes(line.encode())
            H = has_q4(g)
            if H is None:
                unsat += 1
            else:
                check_witness(g, H); sat += 1
                if expect_unsat:
                    bad += 1; print("UNEXPECTED SAT", line)
        print(f"{fn}: SAT(has 4-regular subgraph) {sat}  UNSAT(none) {unsat}")
    sys.exit(1 if bad else 0)
