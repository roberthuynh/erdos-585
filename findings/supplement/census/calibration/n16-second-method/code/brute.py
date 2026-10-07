#!/usr/bin/env python3
"""Exhaustive pair finder, used to calibrate pairsat.py and to certify any NOPAIR answer.

A pair is two edge-disjoint cycles with the same vertex set. For every vertex set S (|S| >= 3)
this lists every Hamilton cycle of G[S] as an edge bitmask and looks for two disjoint ones.
Filters, each a plain necessary condition: G[S] has at least 2|S| edges, and (option --mindeg4,
off by default) every vertex of S has at least 4 neighbours in S (it lies on two edge-disjoint
cycles inside S). With --residual, instead of comparing all cycle pairs it searches, for each
Hamilton cycle C1 of G[S], a Hamilton cycle of G[S] - E(C1).
The graph is read with networkx's graph6 decoder, not with pairsat.g6_decode.
"""
import argparse
import sys
import time

import networkx as nx


def read_graph(line):
    G = nx.from_graph6_bytes(line.strip())
    n = G.number_of_nodes()
    adj = [0] * n
    for u, v in G.edges():
        adj[u] |= 1 << v
        adj[v] |= 1 << u
    return n, adj


def popcount(x):
    return bin(x).count("1")


def ham_cycles(n, adj, S, forbid=None):
    """Yield (edge-set as frozenset of (u,v) u<v, vertex list) for each Hamilton cycle of G[S]
    avoiding the edges in forbid (a set of (u,v)), each cycle once."""
    verts = [v for v in range(n) if S >> v & 1]
    k = len(verts)
    s0 = verts[0]
    sub = [adj[v] & S for v in range(n)]
    if forbid:
        sub = list(sub)
        for (u, v) in forbid:
            sub[u] &= ~(1 << v)
            sub[v] &= ~(1 << u)
    path = [s0]

    def rec(cur, visited):
        if len(path) == k:
            if sub[cur] >> s0 & 1 and path[1] < path[-1]:
                es = frozenset((min(path[i], path[(i + 1) % k]), max(path[i], path[(i + 1) % k]))
                               for i in range(k))
                yield es, list(path)
            return
        nb = sub[cur] & ~visited
        while nb:
            low = nb & -nb
            w = low.bit_length() - 1
            nb ^= low
            path.append(w)
            yield from rec(w, visited | low)
            path.pop()

    yield from rec(s0, 1 << s0)


def has_pair(n, adj, mindeg4=False, residual=False):
    full = (1 << n) - 1
    for S in range(1, full + 1):
        k = popcount(S)
        if k < 3:
            continue
        degs = [popcount(adj[v] & S) for v in range(n) if S >> v & 1]
        if sum(degs) // 2 < 2 * k:
            continue
        if mindeg4 and min(degs) < 4:
            continue
        if residual:
            for e1, p1 in ham_cycles(n, adj, S):
                for e2, p2 in ham_cycles(n, adj, S, forbid=e1):
                    return True, (S, p1, p2)
        else:
            cyc = list(ham_cycles(n, adj, S))
            for i in range(len(cyc)):
                for j in range(i + 1, len(cyc)):
                    if not (cyc[i][0] & cyc[j][0]):
                        return True, (S, cyc[i][1], cyc[j][1])
    return False, None


def check_witness(n, adj, p1, p2):
    def es(p):
        k = len(p)
        if k < 3 or len(set(p)) != k:
            return None
        out = set()
        for i in range(k):
            u, v = p[i], p[(i + 1) % k]
            if not adj[u] >> v & 1:
                return None
            out.add((min(u, v), max(u, v)))
        return out if len(out) == k else None
    a, b = es(p1), es(p2)
    return a is not None and b is not None and set(p1) == set(p2) and not (a & b)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("input")
    ap.add_argument("output")
    ap.add_argument("--mindeg4", action="store_true")
    ap.add_argument("--residual", action="store_true")
    a = ap.parse_args()
    t0 = time.time()
    cnt = {"PAIR": 0, "NOPAIR": 0, "BADWITNESS": 0}
    with open(a.input, "rb") as fh, open(a.output, "w") as out:
        for line in fh:
            line = line.strip()
            if not line or line.startswith(b">"):
                continue
            n, adj = read_graph(line)
            ok, w = has_pair(n, adj, a.mindeg4, a.residual)
            if ok:
                S, p1, p2 = w
                if not check_witness(n, adj, p1, p2):
                    cnt["BADWITNESS"] += 1
                    out.write("%s BADWITNESS\n" % line.decode())
                    continue
                cnt["PAIR"] += 1
                out.write("%s PAIR C1=%s C2=%s\n" % (line.decode(), ",".join(map(str, p1)),
                                                    ",".join(map(str, p2))))
            else:
                cnt["NOPAIR"] += 1
                out.write("%s NOPAIR\n" % line.decode())
    cnt["seconds"] = round(time.time() - t0, 2)
    print(cnt)


if __name__ == "__main__":
    main()
