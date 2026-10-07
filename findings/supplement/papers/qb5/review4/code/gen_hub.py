#!/usr/bin/env python3
"""gen_hub.py -- REVIEW4: random blocks with a planted hub K+ and single-vertex petals, so that the
hub/petal count of PAPER4 Thm 3.1 is exercised under a COVERING multiset m (never in the data).

Templates (K = first k vertices of A, X = K+_C = first x vertices of C):
  A45: K_{4,5} (case beta, m(K) = 4 intended: one unit at each K-vertex, deg_X = 5)
  B56: K_{5,6} minus 3 edges (case beta, m(K) = 3 intended)
  D55: K_{5,5} minus 1 edge, plus 2 edges from K to C - X (case delta, m(K) = 4 intended)
Petals: ny vertices y, each with exactly 3 neighbours in X (E = 3 when m(y) = 0).
Rest: nR vertices R in A, W = C - X. Free X-slots go to R; W's six edges go to Y u R (and the
K-extra edges of D55). Degrees of Y u R are drawn in [4, 6] so that an m supported on K covers L_A.
Sparsity is NOT checked here; kl1rev checks it and skips non-sparse blocks.

Usage: gen_hub.py template ny nR count seed
"""
import random
import sys


def realize(left_need, right_need, allowed, rng, tries=30):
    """random simple bipartite graph, left i gets left_need[i] edges, right j right_need[j],
    edge (i, j) only if allowed(i, j). Greedy by most-constrained with random restarts."""
    L, R = len(left_need), len(right_need)
    if sum(left_need) != sum(right_need):
        return None
    for _ in range(tries):
        rem = list(right_need)
        adj = [set() for _ in range(L)]
        ok = True
        for i in sorted(range(L), key=lambda i: (-left_need[i], rng.random())):
            opts = [j for j in range(R) if rem[j] > 0 and allowed(i, j)]
            if len(opts) < left_need[i]:
                ok = False
                break
            opts.sort(key=lambda j: (-rem[j] - 2 * rng.random()))
            for j in opts[:left_need[i]]:
                adj[i].add(j)
                rem[j] -= 1
        if ok and all(v == 0 for v in rem):
            return adj
    return None


def build(tpl, ny, nR, rng):
    if tpl == "A45":
        k, x = 4, 5
        KX = [(i, j) for i in range(k) for j in range(x)]
        kextra = [0] * k
    elif tpl == "B56":
        k, x = 5, 6
        KX = [(i, j) for i in range(k) for j in range(x)]
        miss = set()
        while len(miss) < 3:
            e = (rng.randrange(k), rng.randrange(x))
            # spread: distinct K-vertices and distinct X-vertices
            if any(e[0] == m[0] or e[1] == m[1] for m in miss):
                continue
            miss.add(e)
        KX = [e for e in KX if e not in miss]
        kextra = [0] * k
    elif tpl == "D55":
        k, x = 5, 5
        KX = [(i, j) for i in range(k) for j in range(x)]
        e0 = (rng.randrange(k), rng.randrange(x))
        KX.remove(e0)
        kextra = [0] * k
        # 2 edges from K to W, at two distinct K-vertices other than e0's (keeps deg <= 6)
        cand = [i for i in range(k) if i != e0[0]]
        rng.shuffle(cand)
        kextra[cand[0]] = 1
        kextra[cand[1]] = 1
    else:
        raise SystemExit("bad template")
    nA = k + ny + nR
    nC = nA - 2
    nW = nC - x
    if nW < 0:
        return None
    Y = list(range(k, k + ny))
    Rv = list(range(k + ny, nA))
    nb = [set() for _ in range(nC)]
    for i, j in KX:
        nb[j].add(i)
    # petals: y gets exactly 3 X-neighbours with free slots
    for y in Y:
        free = [j for j in range(x) if len(nb[j]) < 6]
        if len(free) < 3:
            return None
        for j in rng.sample(free, 3):
            nb[j].add(y)
    xfree = [6 - len(nb[j]) for j in range(x)]
    # degrees of Y and R
    for _ in range(200):
        dy = [rng.randint(4, 6) for _ in Y]
        dr = [rng.randint(4, 6) for _ in Rv]
        a_stub = sum(kextra) + sum(d - 3 for d in dy) + sum(dr)
        c_stub = sum(xfree) + 6 * nW
        if a_stub == c_stub:
            break
    else:
        return None
    # stage 1: X free slots -> R (each r at most 2 X-neighbours, so no new petal K + r is planted)
    if sum(xfree) > 0:
        if nR == 0:
            return None
        rcap = [min(2, d) for d in dr]
        if sum(rcap) < sum(xfree):
            return None
        # choose how many X-edges each r takes
        for _ in range(100):
            take = [0] * nR
            left = sum(xfree)
            while left > 0:
                i = rng.randrange(nR)
                if take[i] < rcap[i]:
                    take[i] += 1
                    left -= 1
            g = realize(take, xfree, lambda i, j: True, rng)
            if g is not None:
                break
        else:
            return None
        for i, r in enumerate(Rv):
            for j in g[i]:
                nb[j].add(r)
    else:
        take = [0] * nR
    # stage 2: W stubs -> Kextra u Y u R remaining
    left_need = [6] * nW
    a_list = [i for i in range(k) if kextra[i]] + Y + Rv
    a_need = [1] * sum(kextra) + [d - 3 for d in dy] + [dr[i] - take[i] for i in range(nR)]
    g = realize(left_need, a_need, lambda i, j: True, rng)
    if g is None:
        return None
    for i in range(nW):
        for j in g[i]:
            nb[x + i].add(a_list[j])
    if any(len(s) != 6 for s in nb):
        return None
    return nA, nC, [sum(1 << v for v in s) for s in nb]


def main():
    tpl = sys.argv[1]
    ny, nR, count, seed = map(int, sys.argv[2:6])
    rng = random.Random(seed)
    out = att = 0
    while out < count and att < 40 * count:
        att += 1
        res = build(tpl, ny, nR, rng)
        if res is None:
            continue
        print(res[0], res[1], *res[2])
        out += 1


if __name__ == "__main__":
    main()
