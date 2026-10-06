#!/usr/bin/env python3
"""gen_big.py -- REVIEW4: hub K+ = K_{4,5} (case beta, m(K) = 4) with one single-vertex petal {y}
(3 edges to X) and one big tight petal P = Q u P_C, Q = 5 A-vertices, P_C = 5 C-vertices,
K_{5,5} minus one edge, one edge from each q to X (E = 5, kappa(P) = 0). Rest completed at random.
Sparsity is checked by kl1rev. Usage: gen_big.py nW count seed
"""
import random
import sys
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from gen_hub import realize  # noqa: E402


def build(nW, rng):
    k, x = 4, 5
    K = list(range(4)); y = 4; Q = list(range(5, 10))
    nR = nW + 2
    R = list(range(10, 10 + nR))
    nA = 10 + nR
    X = list(range(5)); PC = list(range(5, 10)); W = list(range(10, 10 + nW))
    nC = 10 + nW
    assert nA == nC + 2
    nb = [set() for _ in range(nC)]
    for c in X:
        nb[c].update(K)
    for c in rng.sample(X, 3):
        nb[c].add(y)
    miss = (rng.choice(Q), rng.choice(PC))
    for q in Q:
        for c in PC:
            if (q, c) != miss:
                nb[c].add(q)
    # one X-edge per q, respecting X capacity 6
    free = [c for c in X if len(nb[c]) < 6]
    slots = []
    for c in X:
        slots += [c] * (6 - len(nb[c]))
    rng.shuffle(slots)
    if len(slots) < 5:
        return None
    used = slots[:5]
    for q, c in zip(Q, used):
        if q in nb[c]:
            return None
        nb[c].add(q)
    # remaining: X slots, P_C slots, W (6 each) -> y (extra) and R
    cl = [c for c in X + PC if len(nb[c]) < 6] + W
    need = [6 - len(nb[c]) for c in cl]
    for _ in range(200):
        dy = rng.randint(4, 6)
        dr = [rng.randint(4, 6) for _ in R]
        if (dy - 3) + sum(dr) == sum(need):
            break
    else:
        return None
    alist = [y] + R
    aneed = [dy - 3] + dr
    # X- and P_C-slots must not go to y (keep y's petal exact) or to Q/K; only W may reach y
    def allowed(i, j):
        c = cl[i]
        return not (alist[j] == y and c < 10)
    g = realize(need, aneed, allowed, rng)
    if g is None:
        return None
    for i, c in enumerate(cl):
        for j in g[i]:
            nb[c].add(alist[j])
    if any(len(s) != 6 for s in nb):
        return None
    return nA, nC, [sum(1 << v for v in s) for s in nb]


def main():
    nW, count, seed = map(int, sys.argv[1:4])
    rng = random.Random(seed)
    out = att = 0
    while out < count and att < 50 * count:
        att += 1
        r = build(nW, rng)
        if r:
            print(r[0], r[1], *r[2])
            out += 1


if __name__ == "__main__":
    main()
