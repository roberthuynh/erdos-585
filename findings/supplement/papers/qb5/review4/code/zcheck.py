#!/usr/bin/env python3
"""zcheck.py -- REVIEW4 side check of the heuristic in PAPER4 §0 (not used in any proof there):
(1) p in I_X(M)  iff  the multigraph X + z - p has a 4-factor (z joined to a by m(a) parallel edges);
(2) where X + z fails the hypotheses of PAPER.md Theorem 5.1: parallel edges, and sets S containing z,
    3 <= |S| <= |X|, with g(S) = 6|S| - 2e(S) < 12 (classified: z + S0 with S0 tight and m(S0) = 4, or other).
I_X(M) by brute force over A1 subset of A - p (m(A1) >= dem_X(A1)), 4-factor by max flow (own Edmonds-Karp).
Usage: zcheck.py blockfile nblocks nm seed
"""
import itertools
import random
import sys
from collections import deque


def popc(x):
    return bin(x).count("1")


def maxflow(n, edges, s, t):
    g = [[] for _ in range(n)]
    cap = []
    to = []
    for u, v, c in edges:
        g[u].append(len(to)); to.append(v); cap.append(c)
        g[v].append(len(to)); to.append(u); cap.append(0)
    flow = 0
    while True:
        par = [-1] * n
        par[s] = -2
        q = deque([s])
        while q and par[t] == -1:
            u = q.popleft()
            for e in g[u]:
                if cap[e] > 0 and par[to[e]] == -1:
                    par[to[e]] = e
                    q.append(to[e])
        if par[t] == -1:
            return flow
        # bottleneck
        b = 10 ** 9
        v = t
        while v != s:
            e = par[v]; b = min(b, cap[e]); v = to[e ^ 1]
        v = t
        while v != s:
            e = par[v]; cap[e] -= b; cap[e ^ 1] += b; v = to[e ^ 1]
        flow += b


def in_IX(na, cm, m, p):
    others = [a for a in range(na) if a != p]
    for r in range(1, len(others) + 1):
        for A1 in itertools.combinations(others, r):
            mask = sum(1 << a for a in A1)
            dem = 4 * len(A1) - sum(min(4, popc(c & mask)) for c in cm)
            if sum(m[a] for a in A1) < dem:
                return False
    return True


def has_4factor_z(na, cm, m, p):
    # vertices: s=0, A-p, C, z, t
    A = [a for a in range(na) if a != p]
    ida = {a: 1 + i for i, a in enumerate(A)}
    nc = len(cm)
    idc = [1 + len(A) + j for j in range(nc)]
    z = 1 + len(A) + nc
    t = z + 1
    E = []
    for a in A:
        E.append((0, ida[a], 4))
        if m[a]:
            E.append((ida[a], z, m[a]))
    for j, c in enumerate(cm):
        for a in A:
            if c >> a & 1:
                E.append((ida[a], idc[j], 1))
        E.append((idc[j], t, 4))
    E.append((z, t, 4))
    need = 4 * len(A)
    if need != 4 * (nc + 1):
        return False
    return maxflow(t + 1, E, 0, t) == need


def sparsity_failures(na, cm, m):
    """sets S containing z with |S| = 3 or 4 (small sets) and g < 12, classified."""
    nc = len(cm)
    out = {"tight_allends": 0, "z_a_c_m3": 0, "other": 0}
    V = [("a", a) for a in range(na)] + [("c", j) for j in range(nc)]
    for r in (2, 3):
        for S0 in itertools.combinations(V, r):
            Am = sum(1 << v for k, v in S0 if k == "a")
            Cs = [v for k, v in S0 if k == "c"]
            e0 = sum(popc(cm[j] & Am) for j in Cs)
            g0 = 6 * r - 2 * e0
            mz = sum(m[a] for a in range(na) if Am >> a & 1)
            g = g0 + 6 - 2 * mz
            if g < 12:
                if g0 == 12 and mz == 4:
                    out["tight_allends"] += 1
                elif r == 2 and popc(Am) == 1 and len(Cs) == 1 and mz == 3 and e0 == 1:
                    out["z_a_c_m3"] += 1
                else:
                    out["other"] += 1
    return out


def multisets(na, delta):
    def rec(a, left):
        if a == na:
            if left == 0:
                yield ()
            return
        for v in range(0, min(3, delta[a], left) + 1):
            for rest in rec(a + 1, left - v):
                yield (v,) + rest
    return list(rec(0, 4))


def main():
    fn, nb, nm, seed = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    rng = random.Random(seed)
    lines = [l.split() for l in open(fn) if l.strip()]
    rng.shuffle(lines)
    tot = agree = dis = 0
    par = 0
    sf = {"tight_allends": 0, "z_a_c_m3": 0, "other": 0}
    for x in lines[:nb]:
        na, nc = int(x[0]), int(x[1])
        cm = [int(v) for v in x[2:2 + nc]]
        d = [sum(c >> a & 1 for c in cm) for a in range(na)]
        delta = [6 - v for v in d]
        ms = multisets(na, delta)
        for m in rng.sample(ms, min(nm, len(ms))):
            if any(v >= 2 for v in m):
                par += 1
            f = sparsity_failures(na, cm, m)
            for k in sf:
                sf[k] += f[k]
            for p in range(na):
                r1 = in_IX(na, cm, m, p)
                r2 = has_4factor_z(na, cm, m, p)
                tot += 1
                if r1 == r2:
                    agree += 1
                else:
                    dis += 1
                    print("DISAGREE", x[:2 + nc], m, p, r1, r2)
    print(f"(block, m, p) triples {tot}: agree {agree}, disagree {dis}")
    print(f"multisets with a parallel edge at z (some m(a) >= 2): {par}")
    print(f"small sparsity failures of X + z (|S| = 3, 4): {sf}")


if __name__ == "__main__":
    main()
