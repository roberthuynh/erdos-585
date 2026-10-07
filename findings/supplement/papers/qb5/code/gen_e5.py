"""Random E5 block pairs with a 7-edge cut of matching number <= 3 (lane qb5).

Usage: python gen_e5.py COUNT SEED [big] > out.g6   (big: Y also has sides 5, 7, n = 24)
X: C (5) saturated into A (7), each C-vertex misses one A-vertex; a1 is missed by two C-vertices
(in-X degree 3), so it can take 3 cut edges. Y = K_{4,6}: B (4) saturated into D (6), D in-Y degree 4.
Cut: 7 edges A - D whose bipartite graph has a vertex cover of size <= 3 (checked by brute force).
Candidates only; sparsity is checked by petal.c (E5 mode reports has4factor and min g).
"""
import random
import sys
from itertools import combinations
from g6 import encode


def nu_le3(cut):
    verts = sorted({x for e in cut for x in e})
    for k in range(1, 4):
        for K in combinations(verts, k):
            if all(a in K or d in K for a, d in cut):
                return True
    return False


def build(rng):
    C = list(range(5))
    A = list(range(5, 12))
    big = len(sys.argv) > 3
    B = list(range(12, 17 if big else 16))
    D = list(range(17 if big else 16, 24 if big else 22))
    N = 24 if big else 22
    E = set()
    miss = [A[0], A[0]] + rng.sample(A[1:], 3)
    for c, m in zip(C, miss):
        for a in A:
            if a != m:
                E.add((c, a))
    if big:
        missB = [D[0], D[0]] + rng.sample(D[1:], 3)
        for b, m in zip(B, missB):
            for d in D:
                if d != m:
                    E.add((b, d))
    else:
        for b in B:
            for d in D:
                E.add((b, d))
    deg = {v: 0 for v in range(N)}
    for x, y in E:
        deg[x] += 1
        deg[y] += 1
    cut = set()
    # cover: a1 = A[0] with 3 cut edges, plus two more cover vertices
    k2, k3 = rng.sample([v for v in A[1:] + D], 2)
    cover = [A[0], k2, k3]
    tries = 0
    while len(cut) < 7 and tries < 2000:
        tries += 1
        a = rng.choice(A)
        d = rng.choice(D)
        if (a, d) in cut or deg[a] >= 6 or deg[d] >= 6:
            continue
        if not (a in cover or d in cover):
            continue
        cut.add((a, d))
        deg[a] += 1
        deg[d] += 1
    if len(cut) < 7 or not nu_le3(cut):
        return None
    if any(deg[v] < 4 for v in range(N)):
        return None
    return encode(N, list(E | cut))


def main():
    count, seed = int(sys.argv[1]), int(sys.argv[2])
    rng = random.Random(seed)
    out = att = 0
    while out < count and att < 2000 * count:
        att += 1
        g = build(rng)
        if g:
            print(g)
            out += 1


if __name__ == "__main__":
    main()
