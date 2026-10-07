"""Referee 2 helpers (own code; nothing imported from G110/c1checks or G110/checks).

Graph convention: vertices 0..n-1, U = 0..s-1 (smaller side, size s), W = s..2s (size s+1).
adj[v] is an int bitmask of neighbours. Edges always join U and W.
"""
import random
import itertools
import networkx as nx
from pysat.solvers import Solver


def popcount(x):
    return bin(x).count("1")


class BG:
    """Simple bipartite graph with sides U (0..s-1) and W (s..s+r-1)."""

    def __init__(self, s, r, edges):
        self.s = s
        self.r = r
        self.n = s + r
        self.U = list(range(s))
        self.W = list(range(s, s + r))
        self.Umask = (1 << s) - 1
        self.Wmask = ((1 << (s + r)) - 1) ^ self.Umask
        self.adj = [0] * self.n
        self.edges = []
        for (u, w) in edges:
            assert 0 <= u < s <= w < s + r, (u, w)
            assert not (self.adj[u] >> w) & 1, "multi-edge"
            self.adj[u] |= 1 << w
            self.adj[w] |= 1 << u
            self.edges.append((u, w))
        self.deg = [popcount(a) for a in self.adj]
        assert max(self.deg) <= 6

    def e_in(self, S):
        """number of edges of G[S], S a bitmask"""
        tot = 0
        Su = S & self.Umask
        while Su:
            low = Su & -Su
            v = low.bit_length() - 1
            tot += popcount(self.adj[v] & S)
            Su ^= low
        return tot

    def g(self, S):
        return 6 * popcount(S) - 2 * self.e_in(S)

    def kappa(self, S):
        return popcount(S & self.Umask) - popcount(S & self.Wmask)

    def defic(self, Z):
        """G-deficiency of vertex set Z (bitmask)"""
        tot = 0
        while Z:
            low = Z & -Z
            v = low.bit_length() - 1
            tot += 6 - self.deg[v]
            Z ^= low
        return tot

    def defic_in(self, Z, S):
        """deficiency of Z inside G[S] (Z subset of S)"""
        tot = 0
        while Z:
            low = Z & -Z
            v = low.bit_length() - 1
            tot += 6 - popcount(self.adj[v] & S)
            Z ^= low
        return tot

    def e_between(self, X, Y):
        """edges between disjoint vertex sets X and Y"""
        tot = 0
        while X:
            low = X & -X
            v = low.bit_length() - 1
            tot += popcount(self.adj[v] & Y)
            X ^= low
        return tot

    def full(self):
        return (1 << self.n) - 1

    def DU(self):
        return self.defic(self.Umask)

    def DW(self):
        return self.defic(self.Wmask)

    def ports(self):
        return [w for w in self.W if self.deg[w] <= 5]

    def nx_graph(self):
        G = nx.Graph()
        G.add_nodes_from(range(self.n))
        G.add_edges_from(self.edges)
        return G


def bits(mask):
    out = []
    while mask:
        low = mask & -mask
        out.append(low.bit_length() - 1)
        mask ^= low
    return out


def mask_of(vs):
    m = 0
    for v in vs:
        m |= 1 << v
    return m


# ---------------------------------------------------------------- generation

def random_bip_degseq(s, r, udeg, wdeg, rng, tries=2000):
    """Random simple bipartite graph with U-degrees udeg (len s) and W-degrees wdeg (len r).
    Randomized greedy with restarts, then degree-preserving swaps. Returns BG or None."""
    assert sum(udeg) == sum(wdeg)
    for _ in range(tries):
        cap = list(wdeg)
        edges = []
        order = sorted(range(s), key=lambda u: (-udeg[u], rng.random()))
        ok = True
        for u in order:
            need = udeg[u]
            cand = [j for j in range(r) if cap[j] > 0]
            if len(cand) < need:
                ok = False
                break
            # weight by remaining capacity (helps feasibility)
            chosen = []
            pool = cand[:]
            for _k in range(need):
                wts = [cap[j] for j in pool]
                tot = sum(wts)
                x = rng.random() * tot
                acc = 0
                for idx, j in enumerate(pool):
                    acc += wts[idx]
                    if x < acc:
                        break
                chosen.append(j)
                pool.pop(idx)
            for j in chosen:
                cap[j] -= 1
                edges.append((u, s + j))
        if ok:
            G = BG(s, r, edges)
            return randomize_swaps(G, rng, 10 * len(edges))
    return None


def randomize_swaps(G, rng, nswaps):
    """degree-preserving double edge swaps keeping the graph simple and bipartite"""
    edges = list(G.edges)
    eset = set(edges)
    m = len(edges)
    if m < 2:
        return G
    for _ in range(nswaps):
        i, j = rng.randrange(m), rng.randrange(m)
        if i == j:
            continue
        (u1, w1), (u2, w2) = edges[i], edges[j]
        if u1 == u2 or w1 == w2:
            continue
        if (u1, w2) in eset or (u2, w1) in eset:
            continue
        eset.discard((u1, w1)); eset.discard((u2, w2))
        eset.add((u1, w2)); eset.add((u2, w1))
        edges[i] = (u1, w2); edges[j] = (u2, w1)
    return BG(G.s, G.r, edges)


def random_C1(s, DU, wdef_choices, rng):
    """random C1(s) instance: U-degrees 6 except one 5 if DU = 1; W-degree deficiency
    6 + DU spread over W (each W-vertex deficiency drawn so that degrees stay in range)."""
    udeg = [6] * s
    if DU == 1:
        udeg[s - 1] = 5
    r = s + 1
    total_def = 6 * r - sum(udeg)
    # distribute total_def over W with per-vertex max deficiency maxd
    for _ in range(1000):
        wdef = [0] * r
        left = total_def
        while left > 0:
            j = rng.randrange(r)
            if wdef[j] < wdef_choices:
                wdef[j] += 1
                left -= 1
        wdeg = [6 - d for d in wdef]
        G = random_bip_degseq(s, r, udeg, wdeg, rng)
        if G is not None:
            return G
    return None


# ---------------------------------------------------------------- deciders

def has_4factor_balanced(G, P, Q, removed=()):
    """spanning 4-regular subgraph of G restricted to P u Q (|P| = |Q|) by max flow"""
    P = [p for p in P if p not in removed]
    Q = [q for q in Q if q not in removed]
    assert len(P) == len(Q)
    F = nx.DiGraph()
    Pset = set(P)
    Qset = set(Q)
    for p in P:
        F.add_edge("s", ("v", p), capacity=4)
    for q in Q:
        F.add_edge(("v", q), "t", capacity=4)
    for (u, w) in G.edges:
        a, b = (u, w) if u in Pset else (w, u)
        if a in Pset and b in Qset:
            F.add_edge(("v", a), ("v", b), capacity=1)
    val = nx.maximum_flow_value(F, "s", "t")
    return val, 4 * len(P)


def bad_ports(G):
    """ports y with G - y having no spanning 4-regular subgraph"""
    out = []
    for y in G.ports():
        val, target = has_4factor_balanced(G, G.W, G.U, removed=(y,))
        if val < target:
            out.append(y)
    return out


def quartic_subgraph(n, edges, assumptions_in=None):
    """SAT: nonempty edge set with every degree in {0,4}. Returns list of edges or None.
    Exact encoding by forbidding every incident pattern with count not in {0,4}."""
    inc = [[] for _ in range(n)]
    for i, (a, b) in enumerate(edges):
        inc[a].append(i + 1)
        inc[b].append(i + 1)
    clauses = []
    for v in range(n):
        lits = inc[v]
        d = len(lits)
        assert d <= 8
        for pattern in itertools.product((0, 1), repeat=d):
            c = sum(pattern)
            if c in (0, 4):
                continue
            # forbid this exact pattern
            clauses.append([(-l if bit else l) for l, bit in zip(lits, pattern)])
    if not edges:
        return None
    clauses.append([i + 1 for i in range(len(edges))])
    with Solver(name="cadical153", bootstrap_with=clauses) as S:
        if not S.solve():
            return None
        model = set(l for l in S.get_model() if l > 0)
    H = [edges[i] for i in range(len(edges)) if (i + 1) in model]
    # witness check
    dg = [0] * n
    for (a, b) in H:
        dg[a] += 1
        dg[b] += 1
    assert H and all(d in (0, 4) for d in dg), "bad witness"
    return H


# ---------------------------------------------------------------- min g by flows

def min_g_proper_flow(G, budget=None):
    """min over S with 2 <= |S| <= n-1 of g(S) = 6|S| - 2e(S), via max-closure flows.
    WLOG G[S] has an edge (g(S) <= 8 forces that; and taking a component with >= 2
    vertices does not increase g). So: for each vertex x forced out and each edge uv forced
    in, max of 2e(S) - 6|S|. Returns the min g found among sets with g <= 10, else 12
    (meaning: no proper set with |S| >= 2 has g <= 10 ... reported value is exact if <= 10).
    Exactness argument: see REVIEW.md, section on own code."""
    best = 12
    n = G.n
    for x in range(n):
        keep = [v for v in range(n) if v != x]
        sub_edges = [(u, w) for (u, w) in G.edges if u != x and w != x]
        for (u0, w0) in sub_edges:
            F = nx.DiGraph()
            BIG = 10 ** 6
            for i, (u, w) in enumerate(sub_edges):
                F.add_edge("s", ("e", i), capacity=2)
                F.add_edge(("e", i), ("v", u), capacity=BIG)
                F.add_edge(("e", i), ("v", w), capacity=BIG)
            for v in keep:
                F.add_edge(("v", v), "t", capacity=6)
            F.add_edge("s", ("v", u0), capacity=BIG)
            F.add_edge("s", ("v", w0), capacity=BIG)
            cut, (src, _snk) = nx.minimum_cut(F, "s", "t")
            # value of closure = 2*|E'| - cut ... but forced arcs carry BIG; compute directly
            Sset = [v for v in keep if ("v", v) in src]
            S = mask_of(Sset)
            gv = G.g(S)
            if gv < best:
                best = gv
    return best
