#!/usr/bin/env python3
"""Spanning pair (two edge-disjoint Hamilton cycles) by SAT with lazy connectivity cuts.

Same encoding as the wildcard lane's pair_oracle.py, with every vertex forced into the support,
so each color class is a 2-factor and the lazy cuts make each a single Hamilton cycle. Written
for wave4/va6 to test S6 (B - o - y has two edge-disjoint Hamilton cycles for every port y).

Usage: span_oracle.py graph.json o y [--seconds S]      (o, y: vertices of graph.json to delete)
       span_oracle.py graph.json --all-ports o [--seconds S]  (every neighbor y of o)
Output: one JSON line per test: {"o":.., "y":.., "status": "SPAN"|"NOSPAN"|"TIMEOUT", "rounds":..}
"""
import itertools, json, sys, threading, time

import networkx as nx
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
from pysat.solvers import Solver


def spanning_pair(nodes, edges, seconds=120.0, solver_name="m22"):
    nodes = sorted(nodes)
    edges = sorted(set((min(a, b), max(a, b)) for a, b in edges))
    ids = IDPool()
    x = [[ids.id(("x", c, i)) for i in range(len(edges))] for c in range(2)]
    inc = {v: [] for v in nodes}
    for i, (a, b) in enumerate(edges):
        inc[a].append(i)
        inc[b].append(i)
    cl = []
    for i in range(len(edges)):
        cl.append([-x[0][i], -x[1][i]])
    for v in nodes:
        for c in range(2):
            lits = [x[c][i] for i in inc[v]]
            if len(lits) < 2:
                return {"status": "NOSPAN", "rounds": 0, "reason": "degree < 2"}
            enc = CardEnc.equals(lits=lits, bound=2, vpool=ids, encoding=EncType.seqcounter)
            cl.extend(enc.clauses)
    deadline = time.monotonic() + seconds
    solver = Solver(name=solver_name, bootstrap_with=cl)
    rounds = 0
    try:
        while True:
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                return {"status": "TIMEOUT", "rounds": rounds}
            timer = threading.Timer(remaining, solver.interrupt)
            timer.daemon = True
            timer.start()
            try:
                ok = solver.solve_limited(expect_interrupt=True)
            finally:
                timer.cancel()
                solver.clear_interrupt()
            if ok is None:
                return {"status": "TIMEOUT", "rounds": rounds}
            if ok is False:
                return {"status": "NOSPAN", "rounds": rounds}
            rounds += 1
            model = set(l for l in solver.get_model() if l > 0)
            colored = [[edges[i] for i in range(len(edges)) if x[c][i] in model] for c in range(2)]
            done = True
            for c in range(2):
                H = nx.Graph()
                H.add_nodes_from(nodes)
                H.add_edges_from(colored[c])
                comps = [set(k) for k in nx.connected_components(H)]
                if len(comps) == 1:
                    continue
                done = False
                for K in comps:
                    cut = [i for i, (p, q) in enumerate(edges) if (p in K) != (q in K)]
                    for cc in range(2):
                        solver.add_clause([x[cc][i] for i in cut])  # every Hamilton cycle crosses K
            if done:
                return {"status": "SPAN", "rounds": rounds,
                        "cycles": [sorted(colored[0]), sorted(colored[1])]}
    finally:
        solver.delete()


def main():
    args = sys.argv[1:]
    seconds = 120.0
    if "--seconds" in args:
        k = args.index("--seconds"); seconds = float(args[k + 1]); del args[k:k + 2]
    d = json.load(open(args[0])); n, E = d["n"], [tuple(e) for e in d["edges"]]
    G = nx.Graph(); G.add_nodes_from(range(n)); G.add_edges_from(E)
    if args[1] == "--all-ports":
        o = int(args[2]); pairs = [(o, y) for y in sorted(G.neighbors(o))]
    else:
        pairs = [(int(args[1]), int(args[2]))]
    for o, y in pairs:
        H = G.copy(); H.remove_nodes_from([o, y])
        t = time.time()
        r = spanning_pair(list(H.nodes()), list(H.edges()), seconds)
        out = {"o": o, "y": y, "status": r["status"], "rounds": r["rounds"], "t": round(time.time() - t, 2)}
        if r["status"] == "SPAN":
            # verify: two edge-disjoint Hamilton cycles of H
            c0, c1 = r["cycles"]
            ok = all(nx.is_connected(nx.Graph(c)) and len(nx.Graph(c).nodes()) == H.number_of_nodes()
                     and all(dg == 2 for _, dg in nx.Graph(c).degree()) for c in (c0, c1))
            ok = ok and not (set(c0) & set(c1)) and set(c0) <= set(map(lambda e: tuple(sorted(e)), H.edges()))
            out["verified"] = bool(ok)
        print(json.dumps(out)); sys.stdout.flush()


if __name__ == "__main__":
    main()
