#!/usr/bin/env python3
"""Second SAT encoding for pairs, used to certify NOPAIR answers and to cross-check pairsat.py.

A pair is two edge-disjoint cycles with the same vertex set. Unlike pairsat.py (one universal CNF,
graph as assumptions, connectivity by reachability levels), this builds a fresh CNF per graph
over the graph's own edges and enforces connectivity lazily with cut clauses:
  x[v] (v in S), a[e], b[e] for the edges e of G
  a[e] -> x[u], x[v]; b[e] likewise; not(a[e] and b[e]); OR_v x[v]
  x[v] -> at least 2 and at most 2 a-edges at v (b likewise)
Each model gives S with two edge-disjoint 2-factors A, B of G[S]. If A (or B) has a component T
with S not inside T, the cut "S meets T and S meets V-T -> A crosses d(T) and B crosses d(T)" is
added (aux i_T, o_T); every pair satisfies it, the current model does not. Repeat until a model
with A and B single cycles (PAIR, verified) or UNSAT (NOPAIR). Finitely many T, so it stops.
"""
import argparse
import itertools
import json
import sys
import time

import networkx as nx
from pysat.solvers import Solver


def components(S, es):
    nb = {v: [] for v in S}
    for u, v in es:
        nb[u].append(v)
        nb[v].append(u)
    seen, comps = set(), []
    for s in S:
        if s in seen:
            continue
        stack, comp = [s], []
        seen.add(s)
        while stack:
            u = stack.pop()
            comp.append(u)
            for w in nb[u]:
                if w not in seen:
                    seen.add(w)
                    stack.append(w)
        comps.append(comp)
    return comps, nb


def walk(start, nb):
    seq, prev, cur = [start], None, start
    while True:
        nxt = [w for w in nb[cur] if w != prev] if prev is not None else nb[cur][:1]
        if not nxt:
            return seq
        prev, cur = cur, nxt[0]
        if cur == start:
            return seq
        seq.append(cur)


def decide(n, edges, solver="cd19", max_iter=100000):
    E = list(edges)
    top = [0]

    def new():
        top[0] += 1
        return top[0]

    x = [new() for _ in range(n)]
    a = [new() for _ in E]
    b = [new() for _ in E]
    inc = [[] for _ in range(n)]
    for i, (u, v) in enumerate(E):
        inc[u].append(i)
        inc[v].append(i)
    s = Solver(name=solver)
    for i, (u, v) in enumerate(E):
        for c in (a, b):
            s.add_clause([-c[i], x[u]])
            s.add_clause([-c[i], x[v]])
        s.add_clause([-a[i], -b[i]])
    s.add_clause(list(x))
    for v in range(n):
        for c in (a, b):
            lits = [c[i] for i in inc[v]]
            if len(lits) < 2:
                s.add_clause([-x[v]])
                continue
            for j in range(len(lits)):
                s.add_clause([-x[v]] + lits[:j] + lits[j + 1:])
            for t in itertools.combinations(lits, 3):
                s.add_clause([-t[0], -t[1], -t[2]])
    cuts = 0
    for it in range(max_iter):
        if not s.solve():
            s.delete()
            return False, None, it, cuts
        model = s.get_model()
        val = lambda var: model[var - 1] > 0
        S = [v for v in range(n) if val(x[v])]
        Ae = [E[i] for i in range(len(E)) if val(a[i])]
        Be = [E[i] for i in range(len(E)) if val(b[i])]
        ca, nba = components(S, Ae)
        cb, nbb = components(S, Be)
        if len(ca) == 1 and len(cb) == 1:
            s.delete()
            return True, (S, walk(S[0], nba), walk(S[0], nbb)), it, cuts
        for comps in (ca, cb):
            if len(comps) < 2:
                continue
            for T in comps:
                Ts = set(T)
                cut = [i for i, (u, v) in enumerate(E) if (u in Ts) != (v in Ts)]
                iT, oT = new(), new()
                for w in range(n):
                    s.add_clause([-x[w], iT] if w in Ts else [-x[w], oT])
                s.add_clause([-iT, -oT] + [a[i] for i in cut])
                s.add_clause([-iT, -oT] + [b[i] for i in cut])
                cuts += 1
    raise RuntimeError("iteration limit")


def main():
    sys.path.insert(0, __file__.rsplit("/", 1)[0])
    from pairsat import verify_pair, nx_adj
    ap = argparse.ArgumentParser()
    ap.add_argument("input")
    ap.add_argument("out_prefix")
    ap.add_argument("--solver", default="cd19")
    a = ap.parse_args()
    t0 = time.time()
    st = {"graphs": 0, "pair": 0, "nopair": 0, "verify_fail": 0, "max_iter": 0, "cuts": 0}
    with open(a.input, "rb") as fh, open(a.out_prefix + ".certs.txt", "w") as out:
        for line in fh:
            line = line.strip()
            if not line or line.startswith(b">"):
                continue
            n, adj = nx_adj(line)
            edges = sorted({(min(u, v), max(u, v)) for u in range(n) for v in adj[u]})
            ok, cert, it, cuts = decide(n, edges, a.solver)
            st["graphs"] += 1
            st["max_iter"] = max(st["max_iter"], it)
            st["cuts"] += cuts
            if ok:
                S, c1, c2 = cert
                good, why = verify_pair(n, adj, c1, c2)
                if not good:
                    st["verify_fail"] += 1
                    out.write("%s VERIFYFAIL %s\n" % (line.decode(), why))
                    continue
                st["pair"] += 1
                out.write("%s PAIR C1=%s C2=%s\n" % (line.decode(), ",".join(map(str, c1)),
                                                    ",".join(map(str, c2))))
            else:
                st["nopair"] += 1
                out.write("%s NOPAIR\n" % line.decode())
    st["seconds"] = round(time.time() - t0, 2)
    with open(a.out_prefix + ".summary.json", "w") as f:
        json.dump(st, f, indent=1)
        f.write("\n")
    print(json.dumps(st))


if __name__ == "__main__":
    main()
