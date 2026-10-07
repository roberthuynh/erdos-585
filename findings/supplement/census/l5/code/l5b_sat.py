#!/usr/bin/env python3
"""L5B: second-method decider for census L5 (no pair-free bipartite graph with min degree >= 4,
max degree <= 6 and e = 3n - 5 on <= 17 vertices).

A *pair* is two edge-disjoint cycles with the same vertex set. This file shares no code with
pairc, ptool, mpair or the referee's rpair/genbip; the method is a SAT encoding, not a search.

Reads graph6 lines on stdin (one graph per line). For each graph:
  1. class filter (mode "census"): e = 3n - 5, every degree in [4, 6], bipartite (BFS 2-colouring
     of every component). Records connectivity and the side sizes of the bipartition.
  2. SAT decision (encode() below). SAT: the model is decoded into two cycles C1, C2 and checked
     here (simple cycles, same vertex set, edge-disjoint). UNSAT: the graph is pair-free.
Output, one line per graph:
  "<g6> P <k> <C1> <C2>"   pair found; k = |S|; cycles as letters, vertex i -> chr(97 + i)
  "<g6> F"                 no pair (UNSAT)
  "<g6> X <reason>"        not in the class (census mode only)
A JSON summary goes to the file given by --summary (written at the end, atomically).

Encoding (variables):
  x_v        v is in S
  r_e, b_e   edge e is on the red cycle C1 / the blue cycle C2
  o_v        v is the root (the least vertex of S)
  R^c_{v,k}  (colour c, 0 <= k <= K = floor(n/2)) v is joined to the root by a c-path of length <= k;
             R^c_{v,0} is o_v itself
  t^c_{u,v,k} auxiliary: R^c_{u,k-1} and the edge uv has colour c
Clauses:
  r_e -> x_u, x_w;  b_e -> x_u, x_w;  not (r_e and b_e)
  for each v and colour c: at most 2 incident c-edges; x_v -> at least 2 incident c-edges
  exactly one root; o_v -> x_v; o_v -> not x_u for u < v
  R^c_{v,k} -> R^c_{v,k-1} or OR_u t^c_{u,v,k};  t^c_{u,v,k} -> R^c_{u,k-1};  t^c_{u,v,k} -> c_{uv}
  x_v -> R^c_{v,K}
Soundness: in a model each colour class is 2-regular on S and every vertex of S is joined to the
root by a path of that colour, so each colour class is one cycle through all of S.
Completeness: from a pair (C1, C2) on S take root = min S, R^c_{v,k} = [dist_{Cc}(root, v) <= k]
(distances on a cycle of length |S| <= n are <= floor(n/2) = K) and t as forced; every clause holds.
"""
import argparse
import json
import os
import sys
import time

from pysat.solvers import Solver


def parse_g6(line):
    s = line.strip()
    if s.startswith('>>graph6<<'):
        s = s[10:]
    vals = [ord(ch) - 63 for ch in s]
    if not vals or vals[0] < 0 or vals[0] > 62 or any(x < 0 or x > 63 for x in vals):
        raise ValueError('bad graph6: %r' % s)
    n = vals[0]
    nbits = n * (n - 1) // 2
    if len(vals) - 1 != (nbits + 5) // 6:
        raise ValueError('bad graph6 length: %r' % s)
    bits = []
    for x in vals[1:]:
        for sh in (5, 4, 3, 2, 1, 0):
            bits.append((x >> sh) & 1)
    if any(bits[nbits:]):
        raise ValueError('nonzero padding: %r' % s)
    edges = []
    k = 0
    for j in range(1, n):
        for i in range(j):
            if bits[k]:
                edges.append((i, j))
            k += 1
    return n, edges


def class_check(n, edges):
    """Return (reason or None, info). info: connected flag and side sizes (connected case)."""
    deg = [0] * n
    adj = [[] for _ in range(n)]
    for u, w in edges:
        deg[u] += 1
        deg[w] += 1
        adj[u].append(w)
        adj[w].append(u)
    if len(edges) != 3 * n - 5:
        return 'edges', None
    if n == 0 or min(deg) < 4:
        return 'mindeg', None
    if max(deg) > 6:
        return 'maxdeg', None
    col = [-1] * n
    comps = 0
    for s in range(n):
        if col[s] != -1:
            continue
        comps += 1
        col[s] = 0
        stack = [s]
        while stack:
            v = stack.pop()
            for w in adj[v]:
                if col[w] == -1:
                    col[w] = 1 - col[v]
                    stack.append(w)
                elif col[w] == col[v]:
                    return 'nonbipartite', None
    a = col.count(0)
    info = {'connected': comps == 1, 'sides': sorted((a, n - a)) if comps == 1 else None}
    return None, info


def encode(n, edges):
    m = len(edges)
    inc = [[] for _ in range(n)]
    nbr = [[] for _ in range(n)]
    for i, (u, w) in enumerate(edges):
        inc[u].append(i)
        inc[w].append(i)
        nbr[u].append((w, i))
        nbr[w].append((u, i))
    X = [1 + v for v in range(n)]
    RED = [1 + n + i for i in range(m)]
    BLUE = [1 + n + m + i for i in range(m)]
    ROOT = [1 + n + 2 * m + v for v in range(n)]
    top = 2 * n + 2 * m
    cls = []
    for i, (u, w) in enumerate(edges):
        r, b = RED[i], BLUE[i]
        cls.append([-r, X[u]])
        cls.append([-r, X[w]])
        cls.append([-b, X[u]])
        cls.append([-b, X[w]])
        cls.append([-r, -b])
    for v in range(n):
        d = len(inc[v])
        if d == 0:
            cls.append([-X[v]])
            continue
        for colv in (RED, BLUE):
            lits = [colv[i] for i in inc[v]]
            for a in range(d):
                for b2 in range(a + 1, d):
                    for c in range(b2 + 1, d):
                        cls.append([-lits[a], -lits[b2], -lits[c]])
            for f in range(d):
                cls.append([-X[v]] + [lits[j] for j in range(d) if j != f])
    cls.append(list(ROOT))
    for v in range(n):
        cls.append([-ROOT[v], X[v]])
        for u in range(v):
            cls.append([-ROOT[v], -ROOT[u]])
            cls.append([-ROOT[v], -X[u]])
    K = n // 2
    for colv in (RED, BLUE):
        prev = ROOT
        for k in range(1, K + 1):
            cur = list(range(top + 1, top + 1 + n))
            top += n
            for v in range(n):
                clause = [-cur[v], prev[v]]
                for (u, i) in nbr[v]:
                    top += 1
                    clause.append(top)
                    cls.append([-top, prev[u]])
                    cls.append([-top, colv[i]])
                cls.append(clause)
            prev = cur
        for v in range(n):
            cls.append([-X[v], prev[v]])
    return cls, (X, RED, BLUE, ROOT)


def walk_cycle(n, edges, chosen, start):
    """Follow the 2-regular edge set `chosen` from `start`; return the vertex sequence."""
    adj = [[] for _ in range(n)]
    for i in chosen:
        u, w = edges[i]
        adj[u].append(w)
        adj[w].append(u)
    seq = [start]
    prev, cur = None, start
    while True:
        nxt = [w for w in adj[cur] if w != prev]
        if len(adj[cur]) != 2:
            raise AssertionError('colour class not 2-regular at %d' % cur)
        w = nxt[0] if prev is not None else adj[cur][0]
        if w == start:
            break
        seq.append(w)
        prev, cur = cur, w
        if len(seq) > n:
            raise AssertionError('walk too long')
    return seq


def check_pair(n, edges, c1, c2):
    """Independent-of-encoding check of a decoded pair: simple cycles, same vertex set, disjoint."""
    eset = set(edges)

    def cyc_edges(c):
        if len(c) < 3 or len(set(c)) != len(c):
            return None
        es = set()
        for j in range(len(c)):
            a, b = c[j], c[(j + 1) % len(c)]
            e = (min(a, b), max(a, b))
            if e not in eset or e in es:
                return None
            es.add(e)
        return es

    e1, e2 = cyc_edges(c1), cyc_edges(c2)
    return e1 is not None and e2 is not None and set(c1) == set(c2) and not (e1 & e2)


def decide(n, edges, solver_name):
    cls, (X, RED, BLUE, ROOT) = encode(n, edges)
    with Solver(name=solver_name, bootstrap_with=cls) as s:
        if not s.solve():
            return None
        model = s.get_model()
    val = set(l for l in model if l > 0)
    S = [v for v in range(n) if X[v] in val]
    reds = [i for i in range(len(edges)) if RED[i] in val]
    blues = [i for i in range(len(edges)) if BLUE[i] in val]
    root = [v for v in range(n) if ROOT[v] in val]
    assert len(root) == 1 and root[0] == min(S)
    c1 = walk_cycle(n, edges, reds, root[0])
    c2 = walk_cycle(n, edges, blues, root[0])
    if not check_pair(n, edges, c1, c2) or sorted(c1) != S:
        raise AssertionError('decoded pair fails the check')
    return S, c1, c2


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--mode', choices=['census', 'general'], default='census')
    ap.add_argument('--solver', default='m22')
    ap.add_argument('--summary', default=None)
    ap.add_argument('--label', default='')
    args = ap.parse_args()
    t0 = time.time()
    st = {'label': args.label, 'mode': args.mode, 'solver': args.solver, 'read': 0, 'in_class': 0,
          'rejected': {}, 'pair': 0, 'pair_free': 0, 'connected': 0, 'disconnected': 0,
          'sides': {}, 'S_size': {}, 'n': {}}
    out = sys.stdout
    for line in sys.stdin:
        g6 = line.strip()
        if not g6:
            continue
        st['read'] += 1
        n, edges = parse_g6(g6)
        st['n'][str(n)] = st['n'].get(str(n), 0) + 1
        if args.mode == 'census':
            why, info = class_check(n, edges)
            if why is not None:
                st['rejected'][why] = st['rejected'].get(why, 0) + 1
                out.write('%s X %s\n' % (g6, why))
                continue
            st['in_class'] += 1
            if info['connected']:
                st['connected'] += 1
                key = '%d+%d' % tuple(info['sides'])
                st['sides'][key] = st['sides'].get(key, 0) + 1
            else:
                st['disconnected'] += 1
        res = decide(n, edges, args.solver)
        if res is None:
            st['pair_free'] += 1
            out.write('%s F\n' % g6)
        else:
            S, c1, c2 = res
            st['pair'] += 1
            k = str(len(S))
            st['S_size'][k] = st['S_size'].get(k, 0) + 1
            out.write('%s P %d %s %s\n' % (g6, len(S), ''.join(chr(97 + v) for v in c1),
                                           ''.join(chr(97 + v) for v in c2)))
    out.flush()
    st['seconds'] = round(time.time() - t0, 3)
    txt = json.dumps(st, sort_keys=True)
    if args.summary:
        tmp = args.summary + '.tmp'
        with open(tmp, 'w') as f:
            f.write(txt + '\n')
        os.replace(tmp, args.summary)
    sys.stderr.write(txt + '\n')


if __name__ == '__main__':
    main()
