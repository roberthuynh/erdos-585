"""Random C2 instances built around a planted port violation (lane qb5).

Usage: python gen_template.py MODE COUNT SEED > out.g6
MODE alpha: S = K_{c,c+2} (C saturated, a U-small 2-block), a planted alpha violation (k = 2, eps = 0)
            at a port of Q; 7 edges from A to Q_U.
MODE beta : S = K_{c,c+3} with c = 3 (a U-small 3-block), planted beta1a (k = 3, eps = 0), 11 edges.
MODE alpha1: as alpha but eps = 1: one C-vertex sends one edge to Q_W (C then has 5 edges into A).
Q is random bipartite with sides Q_U (m+1 or m+2) and Q_W (m), Z_U = {u1, u2} in Q_U (degree 5).
Degrees are drawn by random edge placement with rejection; the result is only a candidate: sparsity
and everything else are checked by clcheck.c.
"""
import random
import sys
from g6 import encode


def build(mode, rng):
    if mode in ("alpha", "alpha1"):
        c = 4
        a = c + 2
        cut_total = 7
        m = 5
        qu, qw = m + 1, m
    else:
        c = 3
        a = c + 3
        cut_total = 11
        m = rng.choice([4, 5])
        qu, qw = m + 2, m
    eps = 1 if mode == "alpha1" else 0
    # vertex ids
    C = list(range(c))
    QU = list(range(c, c + qu))
    Avs = list(range(c + qu, c + qu + a))
    QW = list(range(c + qu + a, c + qu + a + qw))
    N = c + qu + a + qw
    E = set()
    # S: C saturated into A (complete when a = 6), minus eps edges replaced by edges to Q_W
    for x in C:
        nb = rng.sample(Avs, 6) if a > 6 else list(Avs)
        for y in nb:
            E.add((x, y))
    if eps:
        x = C[0]
        y = rng.choice([y for y in Avs if (x, y) in E])
        E.discard((x, y))
        E.add((x, rng.choice(QW)))
    deg = [0] * N
    for (x, y) in E:
        deg[x] += 1
        deg[y] += 1
    u1, u2 = QU[0], QU[1]
    cap = {v: 6 for v in range(N)}
    cap[u1] = cap[u2] = 5
    # cut edges A - Q_U
    tries = 0
    cut = 0
    while cut < cut_total:
        tries += 1
        if tries > 10000:
            return None
        x = rng.choice(Avs)
        y = rng.choice(QU)
        if (y, x) in E or deg[x] >= cap[x] or deg[y] >= cap[y]:
            continue
        E.add((y, x))
        deg[x] += 1
        deg[y] += 1
        cut += 1
    # Q: fill Q_U to capacity using Q_W vertices (Q_W degrees <= 6)
    for y in QU:
        need = cap[y] - deg[y]
        cand = [w for w in QW if deg[w] < 6 and (y, w) not in E]
        if len(cand) < need:
            return None
        rng.shuffle(cand)
        cand.sort(key=lambda w: deg[w])  # prefer low-degree W to spread
        for w in cand[:need]:
            E.add((y, w))
            deg[y] += 1
            deg[w] += 1
    # sanity: degrees
    if any(deg[v] > 6 for v in range(N)) or any(deg[v] < 4 for v in range(N)):
        return None
    if any(deg[x] != 6 for x in C if not (eps and x == C[0])) or (eps and deg[C[0]] != 6):
        return None
    return encode(N, list(E))


def main():
    mode, count, seed = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    rng = random.Random(seed)
    out = 0
    attempts = 0
    while out < count and attempts < 200 * count:
        attempts += 1
        g = build(mode, rng)
        if g:
            print(g)
            out += 1


if __name__ == "__main__":
    main()
