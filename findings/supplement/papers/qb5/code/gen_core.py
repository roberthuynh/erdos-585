"""E5 instances whose X-block carries a planted core (lane qb5, round 2; NOTES.md section 6).

X (18 vertices): T = 4 A-vertices, C' = 5 C-vertices adjacent to all of T (T u C' = K_{4,5}), A1 = 6
A-vertices, C'' = 3 C-vertices adjacent to all of A1 (K_{3,6}); every C'-vertex has 2 more neighbours in
A1, spread so that every A1-vertex gets 1 or 2 (in-block degree 4 or 5, no in-degree-3 vertex).
dem_X(A1) = 2 > 0 = |A1 n L_A|, so A1 is a non-generic group, relevant for p in T when the cut puts a
cut edge on at least 3 vertices of T - p.  Y = K_{4,6} (n = 28) or a random 5+7 block (n = 30).
Cut: 7 random edges A-D within the free degrees, at least `tcut` of them on T.
Usage: gen_core.py COUNT SEED [tcut] [y57]  -> graph6 lines (candidates; sparsity is checked by e5check).
"""
import random
import sys

from g6 import encode


def build(rng, tcut, y57):
    T = list(range(0, 4)); A1 = list(range(4, 10))
    Cp = list(range(10, 15)); Cpp = list(range(15, 18))
    E = set()
    for y in Cp:
        for t in T:
            E.add((y, t))
    for x in Cpp:
        for a in A1:
            E.add((x, a))
    # 10 edges C' -> A1, two per C'-vertex, A1 loads a permutation of (2,2,2,2,1,1)
    for _ in range(200):
        load = [2, 2, 2, 2, 1, 1]
        rng.shuffle(load)
        slots = [a for a, l in zip(A1, load) for _ in range(l)]
        rng.shuffle(slots)
        pairs = [slots[2 * i:2 * i + 2] for i in range(5)]
        if all(p[0] != p[1] for p in pairs):
            break
    else:
        return None
    for y, pr in zip(Cp, pairs):
        for a in pr:
            E.add((y, a))
    nX = 18
    if not y57:
        B = list(range(nX, nX + 4)); D = list(range(nX + 4, nX + 10))
        for b in B:
            for d in D:
                E.add((b, d))
        N = nX + 10
    else:
        B = list(range(nX, nX + 5)); D = list(range(nX + 5, nX + 12))
        miss = rng.sample(D, 5) if rng.random() < 0.5 else [D[0], D[0]] + rng.sample(D[1:], 3)
        for b, m in zip(B, miss):
            for d in D:
                if d != m:
                    E.add((b, d))
        N = nX + 12
    deg = {v: 0 for v in range(N)}
    for u, v in E:
        deg[u] += 1
        deg[v] += 1
    A = T + A1
    cut = set()
    tl = rng.sample(T, tcut)
    for t in tl:
        d = rng.choice(D)
        if deg[d] >= 6:
            return None
        cut.add((t, d)); deg[t] += 1; deg[d] += 1
    tries = 0
    while len(cut) < 7 and tries < 500:
        tries += 1
        a = rng.choice(A); d = rng.choice(D)
        if (a, d) in cut or deg[a] >= 6 or deg[d] >= 6:
            continue
        cut.add((a, d)); deg[a] += 1; deg[d] += 1
    if len(cut) < 7 or any(deg[v] < 4 for v in range(N)):
        return None
    return encode(N, list(E | cut))


def main():
    count, seed = int(sys.argv[1]), int(sys.argv[2])
    tcut = int(sys.argv[3]) if len(sys.argv) > 3 else 3
    y57 = len(sys.argv) > 4
    rng = random.Random(seed)
    out = seen = 0
    got = set()
    while out < count and seen < 100000:
        seen += 1
        g = build(rng, tcut, y57)
        if g and g not in got:
            got.add(g)
            print(g)
            out += 1


if __name__ == '__main__':
    main()
