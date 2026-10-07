"""identities_own.py (referee's own code): random tests of PAPER Identity 6.2, the H-balance of
Remark 6.4, (1.1), (1.2), Lemma 1.1 (s = out-degree, F-independent), and the claim that reversing a
directed cycle of D(F) gives a 4-factor, on sparse E4 instances read from graph6 files.
4-factors: max-flow b-matching (networkx), then random alternating-cycle walks.
Usage: python identities_own.py file.g6 ninst ntests seed
"""
import random
import sys

import networkx as nx


def read_g6(path, k, rnd):
    lines = [l.strip() for l in open(path) if l.strip()]
    rnd.shuffle(lines)
    return [nx.from_graph6_bytes(l.encode()) for l in lines[:k]]


def colour(G):
    c = nx.bipartite.color(G)
    P = sorted(v for v in G if c[v] == 0); Q = sorted(v for v in G if c[v] == 1)
    return P, Q


def four_factor(G, P, Q):
    N = nx.DiGraph()
    for p in P:
        N.add_edge("s", ("P", p), capacity=4)
        for q in G[p]:
            N.add_edge(("P", p), ("Q", q), capacity=1)
    for q in Q:
        N.add_edge(("Q", q), "t", capacity=4)
    val, flow = nx.maximum_flow(N, "s", "t")
    if val != 4 * len(P):
        return None
    return {(p, q) for p in P for q in G[p] if flow[("P", p)][("Q", q)] == 1}


def digraph(G, P, F):
    Pset = set(P)
    D = {v: [] for v in G}
    for u, v in G.edges():
        p, q = (u, v) if u in Pset else (v, u)
        if (p, q) in F:
            D[p].append(q)
        else:
            D[q].append(p)
    return D


def random_cycle(D, rnd):
    v = rnd.choice(list(D))
    seen = {}
    path = []
    while v not in seen:
        seen[v] = len(path); path.append(v)
        if not D[v]:
            return None
        v = rnd.choice(D[v])
    return path[seen[v]:]  # cycle v0 -> v1 -> ... -> v0


def flip(F, cyc, Pset):
    F = set(F)
    for i in range(len(cyc)):
        u, w = cyc[i], cyc[(i + 1) % len(cyc)]
        p, q = (u, w) if u in Pset else (w, u)
        if (p, q) in F:
            F.remove((p, q))
        else:
            F.add((p, q))
    return F


def main():
    path, k, ntests, seed = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    rnd = random.Random(seed)
    fails = {"id62": 0, "hbal": 0, "out_eq_s": 0, "eq11": 0, "eq12": 0, "flip4": 0}
    counts = {key: 0 for key in fails}
    counts["id62_runs"] = 0; counts["id62_nonzero"] = 0
    for G in read_g6(path, k, rnd):
        P, Q = colour(G); Pset = set(P); V = list(G)
        n = len(V); e = G.number_of_edges()
        deg = dict(G.degree()); Dv = {v: 6 - deg[v] for v in V}
        F = four_factor(G, P, Q)
        if F is None:
            continue
        for _t in range(ntests):
            D = digraph(G, P, F)
            # random set S (any), random balanced U
            S = {v for v in V if rnd.random() < 0.5}
            SP = S & Pset; SQ = S - Pset
            eS = sum(1 for u, v in G.edges() if u in S and v in S)
            g = 6 * len(S) - 2 * eS
            j = len(SQ) - len(SP)
            dQ = sum(1 for p in P if p not in S for q in G[p] if q in SQ)
            dP = sum(1 for p in SP for q in G[p] if q not in S)
            DSQ = sum(Dv[v] for v in SQ); DSP = sum(Dv[v] for v in SP)
            s = 4 * len(SP) - 4 * len(SQ) + dQ
            out = sum(1 for u in S for w in D[u] if w not in S)
            counts["out_eq_s"] += 1
            if out != s or 2 * s != g - 2 * j - 2 * DSQ:
                fails["out_eq_s"] += 1
            counts["eq11"] += 1
            if 2 * dQ != g + 6 * j - 2 * DSQ or 2 * dP != g - 6 * j - 2 * DSP:
                fails["eq11"] += 1
            C = set(V) - S
            eC = sum(1 for u, v in G.edges() if u in C and v in C)
            counts["eq12"] += 1
            if g + (6 * len(C) - 2 * eC) != (6 * n - 2 * e) + 2 * (dQ + dP):
                fails["eq12"] += 1
            # H-balance (Remark 6.4) for S: H-in - H-out = D(S_Q) - D(S_P) - 2 j
            Hin = sum(1 for u in V if u not in S for w in D[u] if w in S and u not in Pset)
            Hout = sum(1 for u in SQ for w in D[u] if w not in S)
            counts["hbal"] += 1
            if Hin - Hout != DSQ - DSP - 2 * j:
                fails["hbal"] += 1
            # Identity 6.2 on a random balanced U and a random directed cycle Z
            Z = random_cycle(D, rnd)
            if Z is None:
                continue
            m = rnd.randint(1, len(P) - 1)
            U = set(rnd.sample(P, m)) | set(rnd.sample(Q, m))
            if rnd.random() < 0.5:  # bias U towards meeting Z in runs
                U |= set(Z[: rnd.randint(1, len(Z))])
                UP = U & Pset; UQ = U - Pset
                while len(UP) > len(UQ):
                    UQ.add(rnd.choice([q for q in Q if q not in UQ]))
                while len(UQ) > len(UP):
                    UP.add(rnd.choice([p for p in P if p not in UP]))
                U = UP | UQ
            UQ = U - Pset

            def c(Fx):
                return sum(1 for (p, q) in Fx if q in UQ and p not in U)
            F2 = flip(F, Z, Pset)
            L = len(Z)
            inside = [Z[i] in U for i in range(L)]
            delta_pred = 0
            if 0 < sum(inside) < L:
                # runs: maximal segments inside U; entering arc is (prev -> first), leaving (last -> next)
                for i in range(L):
                    if inside[i] and not inside[i - 1]:
                        a_in = (Z[i - 1], Z[i])
                        jdx = i
                        while inside[(jdx + 1) % L]:
                            jdx = (jdx + 1) % L
                        a_out = (Z[jdx], Z[(jdx + 1) % L])
                        in_F = a_in[0] in Pset   # F-arcs go P -> Q
                        out_H = a_out[0] not in Pset  # H-arcs go Q -> P
                        delta_pred += (1 if out_H else 0) - (1 if in_F else 0)
            counts["id62"] += 1
            if 0 < sum(inside) < L:
                counts["id62_runs"] += 1
            if delta_pred != 0:
                counts["id62_nonzero"] += 1
            if c(F2) - c(F) != delta_pred:
                fails["id62"] += 1
            # F2 is a 4-factor
            counts["flip4"] += 1
            dF = {v: 0 for v in V}
            for (p, q) in F2:
                dF[p] += 1; dF[q] += 1
                if not G.has_edge(p, q):
                    fails["flip4"] += 1
            if any(dF[v] != 4 for v in V):
                fails["flip4"] += 1
            F = F2  # random walk over 4-factors
    print("file", path, "tests", counts, "failures", fails)


if __name__ == "__main__":
    main()
