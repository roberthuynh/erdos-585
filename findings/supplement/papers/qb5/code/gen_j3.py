"""Random block-pair instances of shape j = 3 or j = 1 (lane qb5).

Usage: python gen_j3.py MODE COUNT SEED > out.g6
T = K_{4,6}: T_W (4) saturated into T_U (6), a W-small 2-block.
B: a U-small 3-block, B_U (b = 3 or 4) saturated into B_W (b + 3), random 6-subsets.
Cut: 10 edges T_U - B_W. MODE u1u2: two T_U vertices get 1 cut edge (degree 5), four get 2.
MODE u0: one T_U vertex gets 0 cut edges (degree 4), five get 2.
Candidates only; sparsity and the rest are checked by clcheck.c / petal.c.
"""
import random
import sys
from g6 import encode


def build(mode, rng):
    b = rng.choice([3, 4])
    TU = list(range(6))
    TW = list(range(6, 10))
    BU = list(range(10, 10 + b))
    BW = list(range(10 + b, 10 + b + b + 3))
    N = 10 + 2 * b + 3
    E = set((u, w) for u in TU for w in TW)
    for u in BU:
        for w in rng.sample(BW, 6):
            E.add((u, w))
    if mode == "u1u2":
        capT = [1, 1, 2, 2, 2, 2]
    else:
        capT = [0, 2, 2, 2, 2, 2]
    deg = {v: 0 for v in range(N)}
    for (x, y) in E:
        deg[x] += 1
        deg[y] += 1
    stubs = [u for u, c in zip(TU, capT) for _ in range(c)]
    rng.shuffle(stubs)
    for u in stubs:
        cand = [w for w in BW if (u, w) not in E and deg[w] < 6]
        if not cand:
            return None
        # bias: allow up to 3 cut edges per B_W vertex
        cand = [w for w in cand if sum(1 for t in TU if (t, w) in E) < 3] or cand
        w = rng.choice(cand)
        E.add((u, w))
        deg[u] += 1
        deg[w] += 1
    if any(deg[v] < 4 or deg[v] > 6 for v in range(N)):
        return None
    return encode(N, list(E))


def main():
    mode, count, seed = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    rng = random.Random(seed)
    out = att = 0
    while out < count and att < 500 * count:
        att += 1
        g = build(mode, rng)
        if g:
            print(g)
            out += 1


if __name__ == "__main__":
    main()
