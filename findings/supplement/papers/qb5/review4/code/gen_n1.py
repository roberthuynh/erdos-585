#!/usr/bin/env python3
"""gen_n1.py -- REVIEW4: random blocks planted with the rigid (N1) configuration.

Hand analysis (REVIEW4.md §3) shows that two maximal overloaded sets T, T' with T n T' = {a}
force: m(a) = 3, d_a = 3, the fourth unit at b in T' only; kappa(X'(T)) = kappa(X'(T')) = -1,
theta* = 1 on both; C'(T) n C'(T') = {c*} with a ~ c*; a's other neighbours c1 in C'(T) - c*,
c2 in C'(T') - c*; T - a saturated into C'(T); T' - a saturated into C'(T') except deg_X(b) = 5;
c* has exactly 3 neighbours in T - a and 2 in T' - a.
This script plants exactly that and completes the block at random (Z = rest of A, W = rest of C,
|W| = |Z| - 4, all remaining C-degree goes to Z). Sparsity is NOT checked here; kl1rev checks it.

Usage: gen_n1.py p q r count seed   (p = |T - a|, q = |T' - a|, r = |Z|)
Vertex order in A: a=0, t_1..t_p, s_1..s_q (s_1 = b), z_1..z_r.
"""
import random
import sys


def rand_bip(left_deg, right_deg, rng, tries=3):
    """random simple bipartite graph with prescribed degrees: Havel-Hakimi realization
    (left vertices in random order, each joined to the right vertices of largest remaining degree),
    then random degree-preserving 2-switches."""
    L, R = len(left_deg), len(right_deg)
    if sum(left_deg) != sum(right_deg) or any(d > R for d in left_deg) or any(d > L for d in right_deg):
        return None
    for _ in range(tries):
        rem = list(right_deg)
        adj = [set() for _ in range(L)]
        ok = True
        for i in sorted(range(L), key=lambda i: (-left_deg[i], rng.random())):
            order = sorted(range(R), key=lambda j: (-rem[j], rng.random()))
            pick = order[:left_deg[i]]
            if any(rem[j] <= 0 for j in pick):
                ok = False
                break
            for j in pick:
                adj[i].add(j)
                rem[j] -= 1
        if not ok:
            continue
        # randomize by 2-switches: (i1,j1),(i2,j2) -> (i1,j2),(i2,j1)
        for _ in range(20 * sum(left_deg)):
            i1, i2 = rng.randrange(L), rng.randrange(L)
            if i1 == i2 or not adj[i1] or not adj[i2]:
                continue
            j1 = rng.choice(tuple(adj[i1])); j2 = rng.choice(tuple(adj[i2]))
            if j2 in adj[i1] or j1 in adj[i2]:
                continue
            adj[i1].remove(j1); adj[i1].add(j2); adj[i2].remove(j2); adj[i2].add(j1)
        return adj
    return None


def build(p, q, r, rng):
    nA = 1 + p + q + r
    a = 0
    T = list(range(1, 1 + p))
    S = list(range(1 + p, 1 + p + q))
    b = S[0]
    Z = list(range(1 + p + q, nA))
    # C indices: cstar=0, CT = c1,u_1..u_p (p+1), CT2 = c2, v_1..v_q (q+1), W (r-4)
    cstar = 0
    CT = list(range(1, 2 + p))
    CT2 = list(range(2 + p, 3 + p + q))
    W = list(range(3 + p + q, 3 + p + q + r - 4))
    nC = 3 + p + q + r - 4
    assert nA == nC + 2
    nb = [set() for _ in range(nC)]
    # a
    nb[cstar].add(a); nb[CT[0]].add(a); nb[CT2[0]].add(a)
    # T - a into {cstar} + CT, each degree 6; cstar exactly 3; others >= 3 and <= 6 - [c = c1]
    colsT = [cstar] + CT
    for _ in range(50):
        degs = [3]
        rest = 6 * p - 3
        k = len(CT)
        caps = [5] + [6] * (k - 1)  # c1 also has a
        if rest > sum(min(c, p) for c in caps) or rest < 3 * k:
            return None
        d = [3] * k
        left = rest - 3 * k
        while left > 0:
            j = rng.randrange(k)
            if d[j] < min(caps[j], p):
                d[j] += 1
                left -= 1
        degs += d
        g = rand_bip([6] * p, degs, rng)
        if g is not None:
            for i, t in enumerate(T):
                for j in g[i]:
                    nb[colsT[j]].add(t)
            break
    else:
        return None
    # T' - a into {cstar} + CT2: b degree 5, others 6; cstar exactly 2; others >= 2
    colsS = [cstar] + CT2
    for _ in range(50):
        k = len(CT2)
        caps = [5] + [6] * (k - 1)  # c2 also has a
        rest = 6 * q - 1 - 2
        if rest > sum(min(c, q) for c in caps) or rest < 2 * k:
            return None
        d = [2] * k
        left = rest - 2 * k
        while left > 0:
            j = rng.randrange(k)
            if d[j] < min(caps[j], q):
                d[j] += 1
                left -= 1
        g = rand_bip([5] + [6] * (q - 1), [2] + d, rng)
        if g is not None:
            for i, s in enumerate(S):
                for j in g[i]:
                    nb[colsS[j]].add(s)
            break
    else:
        return None
    if len(nb[cstar]) != 6:
        return None
    # remaining C-degree goes to Z
    rowsC = CT + CT2 + W
    need = [6 - len(nb[c]) for c in rowsC]
    tot = sum(need)
    if tot != 6 * r - 8:
        return None
    # Z degrees in [4, 6] summing to tot (delta(Z) = 8)
    for _ in range(50):
        zd = [6] * r
        drop = 6 * r - tot
        ok = True
        while drop > 0:
            j = rng.randrange(r)
            if zd[j] > 4:
                zd[j] -= 1
                drop -= 1
            elif all(x <= 4 for x in zd):
                ok = False
                break
        if not ok:
            return None
        g = rand_bip(need, zd, rng)
        if g is not None:
            for i, c in enumerate(rowsC):
                for j in g[i]:
                    nb[c].add(Z[j])
            break
    else:
        return None
    if any(len(x) != 6 for x in nb):
        return None
    masks = [sum(1 << v for v in x) for x in nb]
    return nA, nC, masks


def main():
    p, q, r, count, seed = map(int, sys.argv[1:6])
    rng = random.Random(seed)
    out = 0
    att = 0
    while out < count and att < count * 20:
        att += 1
        res = build(p, q, r, rng)
        if res is None:
            continue
        nA, nC, masks = res
        print(nA, nC, *masks)
        out += 1


if __name__ == "__main__":
    main()
