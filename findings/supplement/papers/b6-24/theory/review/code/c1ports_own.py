"""c1ports_own.py (referee's own code): exhaustive test of PAPER Lemma 7.1 and of the parts of
Corollary 7.2 / Lemma 7.3 that do not use pair-freeness, on sparse C1 instances (graph6 file).
For every port y (vertex of the larger class W with degree 4 or 5), Y = X - y, Q := U, P := W - y,
u1 = the degree-5 vertex of U. For every nonempty proper S of V(Y):
  (iii) g(S) >= 4 + 2|N(y) cap S| and s(S) >= 2 - [u1 in S] - j(S); (i) D_Y(Q) = D_Y(P) = 1 + deg y;
  thin balanced S (2 <= |S| <= |V(Y)|-2, dQ(S) <= 1): u1 in S, dQ = 1, D_Y(S_Q) >= 4, g_X(S+y) = 10;
  forced S with dP(S) >= 1: j >= 2 - [u1 in S] and D(S_Q) >= 2j + 1.
Also checks X sparse by brute force.
Usage: python c1ports_own.py file.g6 maxinst seed
"""
import random
import sys

import networkx as nx


def main():
    path, k, seed = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    rnd = random.Random(seed)
    lines = [l.strip() for l in open(path) if l.strip()]
    rnd.shuffle(lines)
    stats = {"inst": 0, "ports": 0, "sets": 0, "fail_iii": 0, "fail_i": 0, "thin": 0, "fail_thin": 0,
             "forced_excl": 0, "fail_forced": 0, "notsparse": 0, "notC1": 0}
    for line in lines[:k]:
        G = nx.from_graph6_bytes(line.encode())
        n = G.number_of_nodes()
        c = nx.bipartite.color(G)
        A0 = [v for v in G if c[v] == 0]; A1 = [v for v in G if c[v] == 1]
        U, W = (A0, A1) if len(A0) < len(A1) else (A1, A0)
        deg = dict(G.degree())
        if len(W) != len(U) + 1 or sum(6 - deg[v] for v in U) != 1 or sum(6 - deg[v] for v in W) != 7 \
                or G.number_of_edges() != 3 * n - 4 or max(deg.values()) > 6:
            stats["notC1"] += 1
            continue
        idx = {v: i for i, v in enumerate(G)}
        adjm = [0] * n
        for u, v in G.edges():
            adjm[idx[u]] |= 1 << idx[v]; adjm[idx[v]] |= 1 << idx[u]
        # sparsity of X by brute force
        ok = True
        for S in range(1, 1 << n):
            sz = bin(S).count("1")
            if 2 <= sz <= n - 1:
                e2 = sum(bin(adjm[i] & S).count("1") for i in range(n) if S >> i & 1)
                if 6 * sz - e2 < 10:
                    ok = False; break
        if not ok:
            stats["notsparse"] += 1
            continue
        stats["inst"] += 1
        u1 = [v for v in U if deg[v] == 5]
        assert len(u1) == 1
        u1 = u1[0]
        for y in W:
            if deg[y] not in (4, 5):
                continue
            stats["ports"] += 1
            Yv = [v for v in G if v != y]
            m = len(Yv)
            yi = {v: i for i, v in enumerate(Yv)}
            Ny = set(G[y])
            degY = {v: deg[v] - (1 if v in Ny else 0) for v in Yv}
            isQ = [v in set(U) for v in Yv]
            DY = [6 - degY[v] for v in Yv]
            adjY = [0] * m
            for v in Yv:
                for w in G[v]:
                    if w != y:
                        adjY[yi[v]] |= 1 << yi[w]
            d = 1 + deg[y]
            if sum(DY[i] for i in range(m) if isQ[i]) != d or sum(DY[i] for i in range(m) if not isQ[i]) != d:
                stats["fail_i"] += 1
            nyb = 0
            for v in Ny:
                nyb |= 1 << yi[v]
            u1b = 1 << yi[u1]
            Qmask = sum(1 << i for i in range(m) if isQ[i])
            full = (1 << m) - 1
            for S in range(1, full):
                stats["sets"] += 1
                SQ = S & Qmask; SP = S & ~Qmask
                sq = bin(SQ).count("1"); sp = bin(SP).count("1"); sz = sq + sp
                eS2 = sum(bin(adjY[i] & S).count("1") for i in range(m) if S >> i & 1)
                eS = eS2 // 2
                g = 6 * sz - 2 * eS
                nyS = bin(nyb & S).count("1")
                j = sq - sp
                DSQ = sum(DY[i] for i in range(m) if SQ >> i & 1)
                DSP = sum(DY[i] for i in range(m) if SP >> i & 1)
                degSQ = sum(degY[Yv[i]] for i in range(m) if SQ >> i & 1)
                degSP = sum(degY[Yv[i]] for i in range(m) if SP >> i & 1)
                dQ = degSQ - eS; dP = degSP - eS
                s = 4 * sp - 4 * sq + dQ
                inU1 = 1 if S & u1b else 0
                if g < 4 + 2 * nyS or s < 2 - inU1 - j or 2 * s != g - 2 * j - 2 * DSQ or nyS != DSQ - inU1:
                    stats["fail_iii"] += 1
                if sp == sq and 2 <= sz <= m - 2 and dQ <= 1:
                    stats["thin"] += 1
                    gX = g + 6 - 2 * nyS
                    if not (inU1 and dQ == 1 and DSQ >= 4 and gX == 10):
                        stats["fail_thin"] += 1
                if s == 0 and dP >= 1:
                    stats["forced_excl"] += 1
                    if not (j >= 2 - inU1 and DSQ >= 2 * j + 1):
                        stats["fail_forced"] += 1
    print("file", path, stats)


if __name__ == "__main__":
    main()
