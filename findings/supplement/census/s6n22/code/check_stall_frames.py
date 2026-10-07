#!/usr/bin/env python3
"""check_stall_frames.py -- independent check of the stalled-frame lines (wave6/s6n22).

For each line of data/stall_frames.txt (format in RESULT.md): rebuild Y = B - o - y and Y+ = Y + Lambda
from the line alone, and check that the colours form a frame (every vertex of Y+ meets exactly one edge
of each colour 0..5; Lambda edges join N(o)-y to N(y)-o and have colours 4, 5) and that Phi (min over
the three pairings of colours 0-3 of the cycle counts) equals phi_stall and is at least 3.
Usage: check_stall_frames.py [file] ; prints counts and the first few problems.
"""
import sys


def parse_g6(line):
    n = ord(line[0]) - 63
    bits = []
    for ch in line[1:]:
        v = ord(ch) - 63
        bits.extend((v >> (5 - k)) & 1 for k in range(6))
    adj = {v: set() for v in range(n)}
    p = 0
    for j in range(1, n):
        for i in range(j):
            if bits[p]:
                adj[i].add(j); adj[j].add(i)
            p += 1
    return n, adj


def cycles(edges_ab, V):
    """edges_ab: list of (u, v) forming a 2-regular multigraph on V; number of cycles."""
    par = {v: v for v in V}

    def f(x):
        while par[x] != x:
            par[x] = par[par[x]]; x = par[x]
        return x
    comps = len(V)
    for u, v in edges_ab:
        a, b = f(u), f(v)
        if a != b:
            par[a] = b; comps -= 1
    return comps


def check(line):
    f = line.split()
    rec = dict(x.split("=", 1) for x in f[2:] if "=" in x)
    g6 = f[1] if f[0].startswith("slice=") else f[0]
    if not f[0].startswith("slice="):
        rec = dict(x.split("=", 1) for x in f[1:] if "=" in x)
    n, adj = parse_g6(g6)
    m = n // 2
    o, y = int(rec["o"]), int(rec["y"])
    if y not in adj[o] or not (o < m <= y):
        return "o, y not an edge A-B"
    Yedges = []
    for a in range(m):
        if a == o:
            continue
        for b in sorted(adj[a]):
            if b != y:
                Yedges.append((a, b))
    cols = rec["col"]
    if len(cols) != len(Yedges):
        return "col length %d != %d Y edges" % (len(cols), len(Yedges))
    E = [(a, b, int(c)) for (a, b), c in zip(Yedges, cols)]
    Po, Qy = adj[o] - {y}, adj[y] - {o}
    lam_p, lam_q = set(), set()
    for item in rec["lam"].split(","):
        pq, c = item.split(":")
        p, q = map(int, pq.split("-"))
        c = int(c)
        if p not in Po or q not in Qy or c not in (4, 5):
            return "bad Lambda edge %s" % item
        lam_p.add(p); lam_q.add(q)
        E.append((q, p, c))
    if lam_p != Po or lam_q != Qy:
        return "Lambda is not a bijection N(o)-y -> N(y)-o"
    V = [v for v in range(n) if v not in (o, y)]
    for v in V:
        cs = sorted(c for a, b, c in E if v in (a, b))
        if cs != [0, 1, 2, 3, 4, 5]:
            return "vertex %d colours %s" % (v, cs)
    best = min(cycles([(a, b) for a, b, c in E if c in pr[:2]], V) + cycles([(a, b) for a, b, c in E if c in pr[2:]], V)
               for pr in ((0, 1, 2, 3), (0, 2, 1, 3), (0, 3, 1, 2)))
    if best != int(rec["phi_stall"]):
        return "Phi %d != phi_stall %s" % (best, rec["phi_stall"])
    if best < 3:
        return "Phi < 3 at a stall"
    return None


def main():
    path = sys.argv[1] if len(sys.argv) > 1 else "data/stall_frames.txt"
    ok = bad = 0
    shown = 0
    for line in open(path):
        if not line.strip():
            continue
        err = check(line)
        if err is None:
            ok += 1
        else:
            bad += 1
            if shown < 5:
                print("PROBLEM:", err, "|", line[:120].rstrip()); shown += 1
    print("frames ok=%d problems=%d" % (ok, bad))


if __name__ == "__main__":
    main()
