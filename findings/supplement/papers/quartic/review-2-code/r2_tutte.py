"""Referee 2: Tutte form and budget identity used by REPORT.md Theorem 5 (c = 2) (own code).

For random simple graphs with min degree >= 4 and max degree <= 6 (n = 7..9):
  T1  delta(S,T) = f(S) + 4|T| - e(S,T) - q(S,T), q = #components C of G - S - T with e(C,S) odd,
      agrees with the textbook form f(S) - f(T) + sum_T deg_{G-S} - q', q' = #C with f(C)+e(C,T) odd;
  T2  3 delta + 2D = 2e(S) + 4e(T) + 4D_T + sum_C w(C), w(C) = 2D_C + e(C,S) + 2e(C,T) - 3[e(C,S) odd];
  T3  min over all 3^n pairs of delta >= 0  iff  a spanning 4-regular subgraph exists (SAT);
  T4  for D = 4 graphs without a spanning 4-factor: every barrier has delta = -2 is NOT claimed
      in general (sparsity is a minimality property); we only record the barrier types seen.
Exit 1 on a mismatch in T1-T3. Writes out_tutte.json.
"""
import itertools
import json
import os
import random
import sys
import networkx as nx
from pysat.solvers import Solver

HERE = os.path.dirname(os.path.abspath(__file__))


def spanning_4factor_sat(n, edges):
    inc = [[] for _ in range(n)]
    for i, (a, b) in enumerate(edges):
        inc[a].append(i + 1)
        inc[b].append(i + 1)
    cl = []
    for v in range(n):
        lits = inc[v]
        for pat in itertools.product((0, 1), repeat=len(lits)):
            if sum(pat) != 4:
                cl.append([(-l if b else l) for l, b in zip(lits, pat)])
    with Solver(name="cadical153", bootstrap_with=cl) as S:
        ok = S.solve()
        if ok:
            model = set(l for l in S.get_model() if l > 0)
            H = [edges[i] for i in range(len(edges)) if i + 1 in model]
            dg = [0] * n
            for a, b in H:
                dg[a] += 1
                dg[b] += 1
            assert all(d == 4 for d in dg)
        return ok


def rand_graph(n, rng):
    for _ in range(5000):
        if rng.random() < 0.5:
            G = nx.gnm_random_graph(n, rng.randint(2 * n, 3 * n), seed=rng.randrange(10 ** 9))
        else:
            # near-bipartite: sides a, n - a (a = n // 2), dense bipartite part plus a few extra edges
            a = n // 2
            G = nx.Graph()
            G.add_nodes_from(range(n))
            for i in range(a):
                for j in range(a, n):
                    if rng.random() < 0.85:
                        G.add_edge(i, j)
            for _k in range(rng.randint(0, 3)):
                x, y = rng.sample(range(n), 2)
                G.add_edge(x, y)
        dg = [d for _, d in G.degree()]
        if min(dg) >= 4 and max(dg) <= 6:
            return G
    return None


def main(seed=5, ngraphs=60):
    rng = random.Random(seed)
    bad = []
    stats = dict(graphs=0, pairs=0, with4f=0, without4f=0, D4_without=0)
    barrier_types_D4 = {}
    while stats["graphs"] < ngraphs:
        n = rng.choice([7, 8, 9])
        G = rand_graph(n, rng)
        if G is None:
            continue
        stats["graphs"] += 1
        deg = dict(G.degree())
        D = sum(6 - deg[v] for v in G)
        f = {v: deg[v] - 4 for v in G}
        mindelta = 10 ** 9
        V = list(G.nodes())
        for assign in itertools.product((0, 1, 2), repeat=n):
            S = [V[i] for i in range(n) if assign[i] == 1]
            T = [V[i] for i in range(n) if assign[i] == 2]
            Ss, Ts = set(S), set(T)
            R = [v for v in V if v not in Ss and v not in Ts]
            eS = G.subgraph(S).number_of_edges()
            eT = G.subgraph(T).number_of_edges()
            eST = sum(1 for a, b in G.edges() if (a in Ss and b in Ts) or (a in Ts and b in Ss))
            comps = list(nx.connected_components(G.subgraph(R)))
            q = 0
            qp = 0
            wsum = 0
            for C in comps:
                eCS = sum(1 for c in C for x in G[c] if x in Ss)
                eCT = sum(1 for c in C for x in G[c] if x in Ts)
                DC = sum(6 - deg[c] for c in C)
                fC = sum(f[c] for c in C)
                q += eCS % 2
                qp += (fC + eCT) % 2
                wsum += 2 * DC + eCS + 2 * eCT - 3 * (eCS % 2)
            fS = sum(f[v] for v in S)
            fT = sum(f[v] for v in T)
            degGminusS_T = sum(1 for t in T for x in G[t] if x not in Ss)
            d1 = fS + 4 * len(T) - eST - q
            d2 = fS - fT + degGminusS_T - qp
            DT = sum(6 - deg[t] for t in T)
            stats["pairs"] += 1
            if d1 != d2:
                bad.append(("T1", n, list(G.edges()), S, T))
            if 3 * d1 + 2 * D != 2 * eS + 4 * eT + 4 * DT + wsum:
                bad.append(("T2", n, list(G.edges()), S, T))
            mindelta = min(mindelta, d1)
            if D == 4 and d1 < 0:
                key = str((d1, len(S) - len(T), eS, eT, DT, len(comps)))
                barrier_types_D4[key] = barrier_types_D4.get(key, 0) + 1
        has = spanning_4factor_sat(n, list(G.edges()))
        stats["with4f" if has else "without4f"] += 1
        if D == 4 and not has:
            stats["D4_without"] += 1
        if (mindelta >= 0) != has:
            bad.append(("T3", n, list(G.edges()), mindelta, has))
    res = dict(seed=seed, stats=stats, n_mismatch=len(bad), mismatches=bad[:10],
               barrier_types_D4=barrier_types_D4)
    with open(os.path.join(HERE, "out_tutte.json"), "w") as fh:
        json.dump(res, fh)
    print(json.dumps(dict(stats=stats, n_mismatch=len(bad), barrier_types_D4=barrier_types_D4)))
    return 1 if bad else 0


if __name__ == "__main__":
    a = sys.argv[1:]
    sys.exit(main(int(a[0]) if a else 5, int(a[1]) if len(a) > 1 else 60))
