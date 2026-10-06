"""Referee lane M3-R helpers. Own code; nothing imported from c1checks/, checks/ or review/.

Vertices 0..n-1. A bipartite instance is (s_u, s_w, adj) with U = range(s_u), W = range(s_u, s_u+s_w),
adj[v] an int bitmask of neighbors. All quantities are recomputed from adjacency, never from formulas
under test.
"""
import random
from collections import deque

FULL6 = 6


def popc(x):
    return x.bit_count()


def mask_of(it):
    m = 0
    for v in it:
        m |= 1 << v
    return m


def bits(m):
    out = []
    while m:
        low = m & -m
        out.append(low.bit_length() - 1)
        m ^= low
    return out


class Bip:
    def __init__(self, su, sw, edges):
        self.su, self.sw = su, sw
        self.n = su + sw
        self.adj = [0] * self.n
        for (u, w) in edges:
            assert 0 <= u < su <= w < self.n, (u, w)
            assert not (self.adj[u] >> w) & 1, "multi-edge"
            self.adj[u] |= 1 << w
            self.adj[w] |= 1 << u
        self.Umask = (1 << su) - 1
        self.Wmask = ((1 << self.n) - 1) ^ self.Umask
        self.Vmask = (1 << self.n) - 1
        self.deg = [popc(a) for a in self.adj]
        assert max(self.deg) <= 6

    def edges(self):
        return [(u, w) for u in range(self.su) for w in bits(self.adj[u])]

    def e_in(self, S):
        """edges of G[S], computed by scanning U-vertices of S"""
        tot = 0
        for u in bits(S & self.Umask):
            tot += popc(self.adj[u] & S)
        return tot

    def e_between(self, X, Y):
        """edges between disjoint vertex sets X and Y (any sides)"""
        tot = 0
        for v in bits(X):
            tot += popc(self.adj[v] & Y)
        return tot

    def g(self, S):
        return 6 * popc(S) - 2 * self.e_in(S)

    def kappa(self, S):
        return popc(S & self.Umask) - popc(S & self.Wmask)

    def defG(self, Z):
        return sum(6 - self.deg[v] for v in bits(Z))

    def defIn(self, Z, S):
        """deficiency of Z inside G[S], Z subset of S, from in-S degrees"""
        return sum(6 - popc(self.adj[v] & S) for v in bits(Z))


def gen_bip_degseq(du, dw, rng, switches=None):
    """Random simple bipartite graph with U-degrees du, W-degrees dw (sums equal).
    Greedy Gale-Ryser start plus random degree-preserving switches. Returns edge list or None."""
    su, sw = len(du), len(dw)
    if sum(du) != sum(dw):
        return None
    cap = list(dw)
    edges = set()
    order = sorted(range(su), key=lambda i: -du[i])
    for u in order:
        cand = sorted(range(sw), key=lambda j: (-cap[j], rng.random()))
        if sum(1 for j in cand if cap[j] > 0) < du[u]:
            return None
        chosen = cand[:du[u]]
        if any(cap[j] <= 0 for j in chosen):
            return None
        for j in chosen:
            cap[j] -= 1
            edges.add((u, su + j))
    if any(c != 0 for c in cap):
        return None
    el = list(edges)
    es = set(el)
    nsw = switches if switches is not None else 20 * len(el)
    for _ in range(nsw):
        i, j = rng.randrange(len(el)), rng.randrange(len(el))
        (u1, w1), (u2, w2) = el[i], el[j]
        if u1 == u2 or w1 == w2:
            continue
        if (u1, w2) in es or (u2, w1) in es:
            continue
        es.discard((u1, w1)); es.discard((u2, w2))
        es.add((u1, w2)); es.add((u2, w1))
        el[i], el[j] = (u1, w2), (u2, w1)
    return el


def random_c1(s, DU, wmin, rng, tries=200):
    """C1(s) instance: U-degrees 6 except DU of them (DU in {0,1}) of degree 5; W-degrees in [wmin,6]."""
    for _ in range(tries):
        du = [6] * s
        if DU == 1:
            du[rng.randrange(s)] = 5
        tot = sum(du)
        dw = [6] * (s + 1)
        defic = 6 * (s + 1) - tot
        ok = True
        while defic > 0:
            j = rng.randrange(s + 1)
            if dw[j] > wmin:
                dw[j] -= 1
                defic -= 1
            elif all(d <= wmin for d in dw):
                ok = False
                break
        if not ok:
            continue
        el = gen_bip_degseq(du, dw, rng)
        if el is not None:
            return Bip(s, s + 1, el)
    return None


# ---------------- max flow (Dinic), small graphs ----------------
class Dinic:
    def __init__(self, N):
        self.N = N
        self.g = [[] for _ in range(N)]

    def add(self, a, b, c):
        self.g[a].append([b, c, len(self.g[b])])
        self.g[b].append([a, 0, len(self.g[a]) - 1])

    def maxflow(self, s, t, limit=None):
        flow = 0
        INF = float('inf')
        while True:
            if limit is not None and flow >= limit:
                return flow
            level = [-1] * self.N
            level[s] = 0
            dq = deque([s])
            while dq:
                v = dq.popleft()
                for b, c, _ in self.g[v]:
                    if c > 0 and level[b] < 0:
                        level[b] = level[v] + 1
                        dq.append(b)
            if level[t] < 0:
                return flow
            it = [0] * self.N

            def dfs(v, f):
                if v == t:
                    return f
                while it[v] < len(self.g[v]):
                    e = self.g[v][it[v]]
                    b, c, r = e
                    if c > 0 and level[b] == level[v] + 1:
                        d = dfs(b, min(f, c))
                        if d > 0:
                            e[1] -= d
                            self.g[b][r][1] += d
                            return d
                    it[v] += 1
                return 0
            while True:
                f = dfs(s, INF if limit is None else limit - flow)
                if f == 0:
                    break
                flow += f
                if limit is not None and flow >= limit:
                    return flow

    def source_side(self, s):
        seen = [False] * self.N
        seen[s] = True
        dq = deque([s])
        while dq:
            v = dq.popleft()
            for b, c, _ in self.g[v]:
                if c > 0 and not seen[b]:
                    seen[b] = True
                    dq.append(b)
        return seen


def fourfactor_flow(G, P, Q):
    """max flow of the 4-factor network for balanced sides P, Q (bitmasks) of G; returns (value, size)."""
    Pl, Ql = bits(P), bits(Q)
    assert len(Pl) == len(Ql)
    idx = {v: i + 1 for i, v in enumerate(Pl + Ql)}
    N = len(Pl) + len(Ql) + 2
    s, t = 0, N - 1
    D = Dinic(N)
    for p in Pl:
        D.add(s, idx[p], 4)
        for q in bits(G.adj[p] & Q):
            D.add(idx[p], idx[q], 1)
    for q in Ql:
        D.add(idx[q], t, 4)
    return D.maxflow(s, t), len(Pl)


def has_4factor_minus(G, y):
    """does G - y (y in W) have a spanning 4-regular subgraph? (sides W - y and U)"""
    P = G.Wmask & ~(1 << y)
    val, sz = fourfactor_flow(G, P, G.Umask)
    return val == 4 * sz, val


# ---------------- exact min of g over proper sets with |S| >= 2 ----------------
def min_g_forced(G, inside, outside, limit=None):
    """min over S with inside ⊆ S, S ∩ outside = ∅ of g(S) = 6|S| - 2e(S).
    Network: source -> forced-in (inf); v -> sink with capacity def(v) = 6 - deg(v); each edge both
    ways capacity 1; forced-out -> sink (inf). Cut with source side S has capacity
    sum_{v in S} def(v) + e(S, V-S) = 6|S| - 2e(S) = g(S)."""
    n = G.n
    s, t = n, n + 1
    D = Dinic(n + 2)
    BIG = 10 ** 6
    for v in range(n):
        dv = 6 - G.deg[v]
        if (outside >> v) & 1:
            D.add(v, t, BIG)
        elif dv > 0:
            D.add(v, t, dv)
        if (inside >> v) & 1:
            D.add(s, v, BIG)
    for u in range(G.su):
        for w in bits(G.adj[u]):
            D.add(u, w, 1)
            D.add(w, u, 1)
    return D.maxflow(s, t, limit)


def min_proper_g(G, cap=10):
    """min of g(S) over S ⊆ V with 2 <= |S| <= n-1, capped: returns min(true_min, cap).
    A set with no edge has g = 6|S| >= 12. A set with an edge contains some edge uv; force u, v in and
    some x out."""
    best = 12 if G.n >= 3 else 99  # an edgeless pair exists when n >= 3 (two vertices on one side)
    best = min(best, cap)
    E = G.edges()
    for (u, w) in E:
        ins = (1 << u) | (1 << w)
        for x in range(G.n):
            if x == u or x == w:
                continue
            val = min_g_forced(G, ins, 1 << x, limit=best)
            if val < best:
                best = val
                if best <= 0:
                    return best
    return best


def min_proper_g_brute(G):
    """brute force over all subsets (Gray code), for validation on small n"""
    n = G.n
    best = 10 ** 9
    S = 0
    e = 0
    for i in range(1, 1 << n):
        v = (i & -i).bit_length() - 1
        if (S >> v) & 1:
            S ^= 1 << v
            e -= popc(G.adj[v] & S)
        else:
            e += popc(G.adj[v] & S)
            S ^= 1 << v
        k = popc(S)
        if 2 <= k <= n - 1:
            gv = 6 * k - 2 * e
            if gv < best:
                best = gv
    return best


# ---------------- quartic subgraph decider (SAT) ----------------
def quartic_sat(G, forbid_witnesses=None):
    """Return a validated quartic subgraph (list of edges) or None. Own CNF: for each vertex, forbid
    every assignment of its incident edges whose weight is not in {0,4}; plus one clause 'nonempty'."""
    from pysat.solvers import Solver
    from itertools import product
    E = G.edges()
    if not E:
        return None
    var = {e: i + 1 for i, e in enumerate(E)}
    inc = [[] for _ in range(G.n)]
    for (u, w) in E:
        inc[u].append(var[(u, w)])
        inc[w].append(var[(u, w)])
    clauses = [[var[e] for e in E]]
    for v in range(G.n):
        xs = inc[v]
        d = len(xs)
        for pat in product((0, 1), repeat=d):
            wgt = sum(pat)
            if wgt in (0, 4):
                continue
            clauses.append([(-x if b else x) for x, b in zip(xs, pat)])
    with Solver(name='cadical153', bootstrap_with=clauses) as S:
        if not S.solve():
            return None
        model = set(l for l in S.get_model() if l > 0)
    F = [e for e in E if var[e] in model]
    dg = [0] * G.n
    for (u, w) in F:
        dg[u] += 1
        dg[w] += 1
    assert F and all(d in (0, 4) for d in dg), "witness failed validation"
    return F


def g6decode(line):
    """graph6 decoder (same as in rc_census.py)"""
    b = line.strip().encode()
    if b.startswith(b'>>graph6<<'):
        b = b[10:]
    data = [c - 63 for c in b]
    if data[0] < 63:
        n = data[0]; p = 1
    else:
        n = (data[1] << 12) | (data[2] << 6) | data[3]; p = 4
    bl = []
    for x in data[p:]:
        for i in range(5, -1, -1):
            bl.append((x >> i) & 1)
    edges = []
    k = 0
    for j in range(1, n):
        for i in range(j):
            if bl[k]:
                edges.append((i, j))
            k += 1
    return n, edges
