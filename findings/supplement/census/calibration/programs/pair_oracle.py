#!/usr/bin/env python3
"""Decide whether a simple graph contains a pair: two edge-disjoint cycles on one vertex set.

Written for this lane without reading the team's decider. Encoding:
  s[v]      v is in the support S
  x[c][e]   edge e has color c (c = 0, 1)
  - a colored edge has both ends in S; no edge has both colors
  - a vertex in S has exactly two edges of each color; a vertex outside S has none
  - S is nonempty
Each color class is then a 2-regular spanning subgraph of G[S]. Connectivity is lazy: if color c
splits into components, then for each component K we add, for BOTH colors c',
  (not a_K) or (not b_K) or OR{ x[c'][e] : e in delta(K) },
where s[u] implies a_K for u in K and s[w] implies b_K for w outside K. Every genuine pair
satisfies these clauses, because a Hamilton cycle of G[S] crosses every cut that splits S.
So UNSAT (without timeout) means no pair.

Optional exact decomposition (decompose=True): a support S induces minimum degree >= 4, so
S lies in the 4-core; and a pair cannot cross an edge cut of at most 3 edges inside the current
graph. Recursively restrict to 4-cores and to classes of local edge connectivity >= 4, then
solve each terminal piece separately. A pair exists in G iff it exists in some terminal piece.
"""
import itertools, json, sys, threading, time

import networkx as nx
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
from pysat.solvers import Solver


def canon(edges):
    out = set()
    for a, b in edges:
        a, b = int(a), int(b)
        if a == b:
            raise ValueError("loop")
        out.add((min(a, b), max(a, b)))
    return sorted(out)


def four_core_pieces(nodes, edges):
    """Terminal pieces of the recursive 4-core / local-edge-connectivity>=4 decomposition."""
    G = nx.Graph()
    G.add_nodes_from(nodes)
    G.add_edges_from(edges)
    stack, done = [G], []
    while stack:
        H = stack.pop()
        H = nx.k_core(H, 4).copy()
        if H.number_of_nodes() < 5:
            continue
        comps = [H.subgraph(c).copy() for c in nx.connected_components(H)]
        if len(comps) > 1:
            stack.extend(comps)
            continue
        nx.set_edge_attributes(H, 1, "capacity")
        T = nx.gomory_hu_tree(H)
        C = nx.Graph()
        C.add_nodes_from(H)
        C.add_edges_from((u, v) for u, v, w in T.edges(data="weight") if w >= 4)
        classes = [set(c) for c in nx.connected_components(C)]
        if len(classes) == 1:
            done.append(H)
        else:
            stack.extend(H.subgraph(c).copy() for c in classes if len(c) >= 5)
    return done


def _solve_piece(nodes, edges, deadline, solver_name, max_support=None):
    nodes = sorted(nodes)
    edges = canon(edges)
    ids = IDPool()
    s = {v: ids.id(("s", v)) for v in nodes}
    x = [[ids.id(("x", c, i)) for i in range(len(edges))] for c in range(2)]
    inc = {v: [] for v in nodes}
    for i, (a, b) in enumerate(edges):
        inc[a].append(i)
        inc[b].append(i)
    cl = [[s[v] for v in nodes]]
    for i, (a, b) in enumerate(edges):
        cl.append([-x[0][i], -x[1][i]])
        for c in range(2):
            cl.append([-x[c][i], s[a]])
            cl.append([-x[c][i], s[b]])
    for v in nodes:
        for c in range(2):
            lits = [x[c][i] for i in inc[v]]
            if len(lits) < 2:
                cl.append([-s[v]])
                continue
            # at least two when selected
            cl.append([-s[v]] + lits)
            for j in range(len(lits)):
                cl.append([-s[v]] + lits[:j] + lits[j + 1:])
            # at most two
            if len(lits) <= 10:
                for t in itertools.combinations(lits, 3):
                    cl.append([-l for l in t])
            else:
                enc = CardEnc.atmost(lits=lits, bound=2, vpool=ids, encoding=EncType.seqcounter)
                cl.extend(enc.clauses)
    if max_support is not None and max_support < len(nodes):
        enc = CardEnc.atmost(lits=[s[v] for v in nodes], bound=max_support, vpool=ids,
                             encoding=EncType.seqcounter)
        cl.extend(enc.clauses)
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
                return {"status": "NOPAIR", "rounds": rounds}
            rounds += 1
            model = set(l for l in solver.get_model() if l > 0)
            S = [v for v in nodes if s[v] in model]
            colored = [[edges[i] for i in range(len(edges)) if x[c][i] in model] for c in range(2)]
            comps = []
            for c in range(2):
                H = nx.Graph()
                H.add_nodes_from(S)
                H.add_edges_from(colored[c])
                comps.append([set(k) for k in nx.connected_components(H)])
            if all(len(k) == 1 for k in comps):
                return {"status": "PAIR", "rounds": rounds, "support": S,
                        "cycles": [cycle_order(colored[0]), cycle_order(colored[1])]}
            for c in range(2):
                if len(comps[c]) == 1:
                    continue
                for K in comps[c]:
                    a = ids.id(("a", frozenset(K)))
                    b = ids.id(("b", frozenset(K)))
                    new = [[-s[u], a] for u in K] + [[-s[w], b] for w in nodes if w not in K]
                    cut = [i for i, (p, q) in enumerate(edges) if (p in K) != (q in K)]
                    for cc in range(2):
                        new.append([-a, -b] + [x[cc][i] for i in cut])
                    for clause in new:
                        solver.add_clause(clause)
    finally:
        solver.delete()


def cycle_order(cycle_edges):
    adj = {}
    for a, b in cycle_edges:
        adj.setdefault(a, []).append(b)
        adj.setdefault(b, []).append(a)
    start = min(adj)
    order, prev, cur = [start], None, start
    while True:
        nxt = [w for w in adj[cur] if w != prev]
        nxt = nxt[0] if prev is not None else min(adj[cur])
        if nxt == start:
            break
        order.append(nxt)
        prev, cur = cur, nxt
    return order


def decide(n, edges, seconds=60.0, decompose=True, solver_name="m22", max_support=None):
    """max_support restricts to supports of at most that size; then NOPAIR only means
    'no pair with a support that small'."""
    edges = canon(edges)
    deadline = time.monotonic() + seconds
    if decompose:
        pieces = four_core_pieces(range(n), edges)
        jobs = [(sorted(P.nodes()), canon(P.edges())) for P in pieces]
    else:
        jobs = [(list(range(n)), edges)]
    info = {"pieces": [len(j[0]) for j in jobs], "decompose": decompose, "max_support": max_support}
    timed_out = False
    for nodes, es in jobs:
        r = _solve_piece(nodes, es, deadline, solver_name, max_support)
        if r["status"] == "PAIR":
            r.update(info)
            return r
        if r["status"] == "TIMEOUT":
            timed_out = True
            break
    return dict(status="TIMEOUT" if timed_out else "NOPAIR", **info)


def find_small_pair(n, edges, seconds=60.0, caps=(7, 9, 11)):
    """Try support caps in increasing order, then the unrestricted check. A NOPAIR answer is
    returned only from the unrestricted call."""
    for b in caps:
        if b >= n:
            break
        r = decide(n, edges, seconds=seconds, max_support=b)
        if r["status"] in ("PAIR", "TIMEOUT"):
            return r
    return decide(n, edges, seconds=seconds)


def load(path):
    d = json.load(open(path))
    edges = d["edges"]
    n = d.get("n", 1 + max(max(e) for e in edges))
    return n, edges


if __name__ == "__main__":
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument("graph", help="JSON with n and edges")
    ap.add_argument("--seconds", type=float, default=200)
    ap.add_argument("--plain", action="store_true", help="no decomposition")
    args = ap.parse_args()
    n, edges = load(args.graph)
    print(json.dumps(decide(n, edges, args.seconds, decompose=not args.plain)))
