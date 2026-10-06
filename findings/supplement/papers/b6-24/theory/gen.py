"""Random instance generators for wave4/theory experiments.

realize(dp, dq, rng): random simple bipartite graph with degree lists dp (P side), dq (Q side),
by a randomized Gale-Ryser greedy plus random switches; None if not realizable.
"""
import random
import networkx as nx

def realize(dp, dq, rng, switches=None, forbid=None):
    """dp: dict p->deg, dq: dict q->deg. forbid: set of (p,q) pairs not allowed."""
    forbid = forbid or set()
    if sum(dp.values()) != sum(dq.values()):
        return None
    rem = dict(dq)
    E = set()
    order = sorted(dp, key=lambda p: (-dp[p], rng.random()))
    for p in order:
        need = dp[p]
        cands = [q for q in rem if rem[q] > 0 and (p, q) not in forbid]
        if len(cands) < need:
            return None
        # prefer high remaining degree, random tie-break (Havel-Hakimi style)
        cands.sort(key=lambda q: (-rem[q], rng.random()))
        for q in cands[:need]:
            E.add((p, q)); rem[q] -= 1
    if any(rem.values()):
        return None
    E = list(E)
    S = set(E)
    nsw = switches if switches is not None else 20 * len(E)
    for _ in range(nsw):
        a, b = rng.sample(range(len(E)), 2)
        (p1, q1), (p2, q2) = E[a], E[b]
        if p1 == p2 or q1 == q2:
            continue
        if (p1, q2) in S or (p2, q1) in S or (p1, q2) in forbid or (p2, q1) in forbid:
            continue
        S.discard((p1, q1)); S.discard((p2, q2))
        S.add((p1, q2)); S.add((p2, q1))
        E[a] = (p1, q2); E[b] = (p2, q1)
    return E

def random_e4(a, rng, pdef=None, qdef=None):
    """Random E4 instance with a vertices per side. pdef/qdef: list of deficiencies of the
    deficient vertices on each side (sum 4), default random among [2,2],[2,1,1],[1,1,1,1]."""
    pats = [[2, 2], [2, 1, 1], [1, 1, 1, 1]]
    pdef = pdef or rng.choice(pats)
    qdef = qdef or rng.choice(pats)
    P = list(range(a)); Q = list(range(a, 2 * a))
    dp = {p: 6 for p in P}; dq = {q: 6 for q in Q}
    for i, d in enumerate(pdef):
        dp[P[i]] -= d
    for i, d in enumerate(qdef):
        dq[Q[i]] -= d
    E = realize(dp, dq, rng)
    if E is None:
        return None
    Y = nx.Graph(); Y.add_nodes_from(range(2 * a)); Y.add_edges_from(E)
    return Y, set(P)

def blocks_instance(spec, rng, tries=200):
    """spec: dict with
         'blocks': list of (bP, bQ) sizes,
         'pdef': dict (block, index) -> deficiency on P side, 'qdef' similarly,
         'links': list of (i, side, k, count): count edges from block i's `side` class
                  ('P' or 'Q') to block k's other class.
       Builds inter-block edges at random, then fills each block. Returns (Y, Pset) or None."""
    blocks = spec['blocks']
    vid = 0
    BP, BQ = [], []
    for (bp, bq) in blocks:
        BP.append(list(range(vid, vid + bp))); vid += bp
    for (bp, bq) in blocks:
        BQ.append(list(range(vid, vid + bq))); vid += bq
    n = vid
    deg = {}
    for i in range(len(blocks)):
        for t, p in enumerate(BP[i]):
            deg[p] = 6 - spec.get('pdef', {}).get((i, t), 0)
        for t, q in enumerate(BQ[i]):
            deg[q] = 6 - spec.get('qdef', {}).get((i, t), 0)
    for _ in range(tries):
        rem = dict(deg)
        E = set()
        ok = True
        for (i, side, k, cnt) in spec['links']:
            A = BP[i] if side == 'P' else BQ[i]
            B = BQ[k] if side == 'P' else BP[k]
            for _c in range(cnt):
                ca = [x for x in A if rem[x] > 0]
                cb = [y for y in B if rem[y] > 0]
                if not ca or not cb:
                    ok = False; break
                # spread: prefer vertices with more remaining degree
                x = max(ca, key=lambda v: (rem[v], rng.random()))
                choices = [y for y in cb if ((x, y) if side == 'P' else (y, x)) not in E]
                if not choices:
                    ok = False; break
                y = max(choices, key=lambda v: (rem[v], rng.random()))
                e = (x, y) if side == 'P' else (y, x)
                E.add(e); rem[x] -= 1; rem[y] -= 1
            if not ok:
                break
        if not ok:
            continue
        for i in range(len(blocks)):
            dp = {p: rem[p] for p in BP[i]}
            dq = {q: rem[q] for q in BQ[i]}
            Ei = realize(dp, dq, rng)
            if Ei is None:
                ok = False; break
            E |= set(Ei)
        if not ok:
            continue
        Y = nx.Graph(); Y.add_nodes_from(range(n)); Y.add_edges_from(E)
        Pset = set(x for L in BP for x in L)
        return Y, Pset
    return None
