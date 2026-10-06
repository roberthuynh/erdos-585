"""E5 pair analysis (lane qb5, round 2).

For a sparse E5 graph G without a 4-factor: find the block pair X = A u C, Y = B u D and the 7 cut
edges from a minimum cut, then for every pair (p, q) decide whether G - p - q has a 4-factor, and
check the identities of NOTES.md section 6:
  (I1) a good pair has p in A and q in D;
  (I2) min over Z containing p, q of Psi(Z) = 5 + (maxflow(G - p - q) - 4|P'|), where
       Psi(Z) = 4|Z_big| + 2|Z_small| - e(Z) - cr(Z), big = A u D, small = B u C,
       cr(Z) = cut edges with exactly one end in Z (spot-checked on random Z);
  (I3) good(p, q) iff some set M of 4 cut edges is realizable in X - p and in Y - q
       (matroid form: M avoids p, q; X - p has a subgraph with degree 4 on C and 4 - m_a on A - p).
Usage: e5pairs.py FILE.g6 [limit]   prints one summary line per graph and a total.
"""
import random
import sys
from itertools import combinations

import networkx as nx

from g6 import decode


def bip(n, adj):
    side = [-1] * n
    for r in range(n):
        if side[r] >= 0:
            continue
        side[r] = 0
        st = [r]
        while st:
            v = st.pop()
            for u in adj[v]:
                if side[u] < 0:
                    side[u] = 1 - side[v]
                    st.append(u)
    return side


def flow_net(adj, keep, side, demand):
    """Network for a subgraph of G[keep] with degree demand[v] at every v in keep (bipartite)."""
    F = nx.DiGraph()
    for v in keep:
        if side[v] == 0:
            F.add_edge('s', v, capacity=demand[v])
            for u in adj[v]:
                if u in keep:
                    F.add_edge(v, u, capacity=1)
        else:
            F.add_edge(v, 't', capacity=demand[v])
    return F


def factor_deficit(adj, keep, side, demand):
    """Return (maxflow, total P-demand, total Q-demand, source side of a min cut)."""
    F = flow_net(adj, keep, side, demand)
    tp = sum(demand[v] for v in keep if side[v] == 0)
    tq = sum(demand[v] for v in keep if side[v] == 1)
    if 's' not in F or 't' not in F:
        return 0, tp, tq, {'s'}
    val, (S, _) = nx.minimum_cut(F, 's', 't')
    return val, tp, tq, S


def structure(n, adj, side):
    """Find X = A u C (P-demanding violation of G) via the min cut; P = side 0."""
    keep = set(range(n))
    dem = {v: 4 for v in keep}
    val, tp, tq, S = factor_deficit(adj, keep, side, dem)
    assert tp == tq
    if val == tp:
        return None
    A = {v for v in S if v != 's' and side[v] == 0}
    C = {v for v in S if v != 's' and side[v] == 1}
    B = {v for v in range(n) if side[v] == 0} - A
    D = {v for v in range(n) if side[v] == 1} - C
    return A, C, B, D, tp - val


def psi(Z, adj, big, small, cutset):
    eZ = sum(1 for v in Z for u in adj[v] if u in Z) // 2
    cr = sum(1 for (a, d) in cutset if (a in Z) != (d in Z))
    return 4 * len(Z & big) + 2 * len(Z & small) - eZ - cr


def realizable(adj, side, block, removed, small, m):
    """block minus removed has a subgraph: degree 4 on small vertices, 4 - m[v] on big ones."""
    keep = set(block) - {removed}
    dem = {}
    for v in keep:
        dem[v] = 4 if v in small else 4 - m.get(v, 0)
        if dem[v] < 0:
            return False
    val, tp, tq, _ = factor_deficit(adj, keep, side, dem)
    return tp == tq and val == tp


def analyse(line, rng, nspot=30):
    n, adj = decode(line)
    side = bip(n, adj)
    st = structure(n, adj, side)
    if st is None:
        return None
    A, C, B, D, defi = st
    X, Y = A | C, B | D
    cut = [(a, d) for a in A for d in adj[a] if d in D]
    cutset = set(cut)
    big, small = A | D, B | C
    P = {v for v in range(n) if side[v] == 0}
    Q = set(range(n)) - P
    allv = set(range(n))
    good = set()
    minpsi = {}
    for p in P:
        for q in Q:
            keep = allv - {p, q}
            val, tp, tq, S = factor_deficit(adj, keep, side, {v: 4 for v in keep})
            if val == tp:
                good.add((p, q))
            if p in A and q in D:
                minpsi[(p, q)] = 5 + val - tp
    i1 = all(p in A and q in D for (p, q) in good)
    # I2 spot check: random Z containing p, q never goes below the flow value; the min-cut set attains it
    i2 = True
    for (p, q), mv in minpsi.items():
        for _ in range(nspot):
            Z = {v for v in range(n) if rng.random() < rng.random()} | {p, q}
            if psi(Z, adj, big, small, cutset) < mv:
                i2 = False
        # witness from the min cut: source side (A', C') of G - p - q, T = complement in H, R = T + p,
        # Z = (R & X) | (Y - R)
        keep = allv - {p, q}
        val, tp, tq, S = factor_deficit(adj, keep, side, {v: 4 for v in keep})
        Ap = {v for v in S if v != 's' and side[v] == 0}
        Cp = {v for v in S if v != 's' and side[v] == 1}
        T = keep - Ap - Cp
        R = T | {p}
        Z = (R & X) | (Y - R)
        if psi(Z, adj, big, small, cutset) != mv:
            i2 = False
    # I3 matroid form
    i3 = True
    accX = {}
    for p in A:
        accX[p] = set()
        for M in combinations(range(len(cut)), 4):
            if any(cut[i][0] == p for i in M):
                continue
            m = {}
            for i in M:
                m[cut[i][0]] = m.get(cut[i][0], 0) + 1
            if realizable(adj, side, X, p, C, m):
                accX[p].add(M)
    accY = {}
    for q in D:
        accY[q] = set()
        for M in combinations(range(len(cut)), 4):
            if any(cut[i][1] == q for i in M):
                continue
            m = {}
            for i in M:
                m[cut[i][1]] = m.get(cut[i][1], 0) + 1
            if realizable(adj, side, Y, q, B, m):
                accY[q].add(M)
    for p in A:
        for q in D:
            if bool(accX[p] & accY[q]) != ((p, q) in good):
                i3 = False
    return dict(n=n, A=len(A), C=len(C), B=len(B), D=len(D), defi=defi, ncut=len(cut),
                good=len(good), i1=i1, i2=i2, i3=i3,
                rankX=[len(accX[p]) for p in sorted(A)], rankY=[len(accY[q]) for q in sorted(D)])


def main():
    fn = sys.argv[1]
    lim = int(sys.argv[2]) if len(sys.argv) > 2 else 10 ** 9
    rng = random.Random(1)
    ok = tot = 0
    with open(fn) as fh:
        for k, line in enumerate(fh):
            if k >= lim:
                break
            line = line.strip()
            if not line:
                continue
            r = analyse(line, rng)
            tot += 1
            if r is None:
                print(k, 'has a 4-factor')
                continue
            print(k, r)
            ok += r['i1'] and r['i2'] and r['i3']
    print('TOTAL', tot, 'all identities hold in', ok)


if __name__ == '__main__':
    main()
