"""Referee's own helpers for checking C1-PAPER.md. Written from scratch for this review;
nothing imported from G110/c1checks or G110/checks.

Bipartite graph: vertices 0..s-1 are U, s..s+m-1 are W (m = |W|). Adjacency as sets.
"""
import random
import itertools
import networkx as nx
from pysat.solvers import Solver


class Bip:
    def __init__(self, s, m, edges):
        self.s, self.m, self.n = s, m, s + m
        self.adj = [set() for _ in range(self.n)]
        for (u, w) in edges:
            assert 0 <= u < s and s <= w < self.n, (u, w, s, m)
            assert w not in self.adj[u], "parallel edge"
            self.adj[u].add(w)
            self.adj[w].add(u)
        self.edges = [(u, w) for u in range(s) for w in sorted(self.adj[u])]
        self.U = frozenset(range(s))
        self.W = frozenset(range(s, self.n))
        self.V = frozenset(range(self.n))

    def deg(self, v):
        return len(self.adj[v])

    def maxdeg(self):
        return max(len(a) for a in self.adj)

    # ---- set functions of the paper -------------------------------------------------
    def e_in(self, S):
        S = set(S)
        return sum(1 for (u, w) in self.edges if u in S and w in S)

    def e_between(self, X, Y):
        X, Y = set(X), set(Y)
        assert not (X & Y)
        return sum(1 for (u, w) in self.edges if (u in X and w in Y) or (u in Y and w in X))

    def g(self, S):
        return 6 * len(S) - 2 * self.e_in(S)

    def kappa(self, S):
        S = set(S)
        return len(S & self.U) - len(S & self.W)

    def D(self, Z):
        return sum(6 - self.deg(v) for v in Z)

    def D_in(self, S, Z):
        """Deficiency of Z inside G[S] (Z subset of S)."""
        S = set(S)
        return sum(6 - len(self.adj[v] & S) for v in Z)

    def deg_in(self, S, v):
        return len(self.adj[v] & set(S))

    # ---- class membership ----------------------------------------------------------
    def is_C1(self):
        """Sides U (size s) and W (size s+1), max degree <= 6, D_U <= 1."""
        return self.m == self.s + 1 and self.maxdeg() <= 6 and self.D(self.U) <= 1

    def graph6(self):
        return nx.to_graph6_bytes(self.to_nx(), header=False).decode().strip()

    def to_nx(self):
        G = nx.Graph()
        G.add_nodes_from(range(self.n))
        G.add_edges_from(self.edges)
        return G


# ---- deciders -------------------------------------------------------------------------

def quartic_subgraph(n, edges):
    """Nonempty edge set with every vertex degree in {0, 4}, via SAT with an exact
    forbidden-assignment encoding per vertex (degrees <= 7 assumed). Returns the edge list or None.
    The witness is re-validated here before being returned."""
    inc = [[] for _ in range(n)]
    for i, (a, b) in enumerate(edges):
        inc[a].append(i + 1)
        inc[b].append(i + 1)
    clauses = []
    for v in range(n):
        lits = inc[v]
        d = len(lits)
        assert d <= 7
        for r in range(d + 1):
            if r in (0, 4):
                continue
            for T in itertools.combinations(range(d), r):
                Ts = set(T)
                clauses.append([-lits[i] if i in Ts else lits[i] for i in range(d)])
    clauses.append([i + 1 for i in range(len(edges))])  # nonempty
    with Solver(name="cadical153", bootstrap_with=clauses) as sol:
        if not sol.solve():
            return None
        model = set(l for l in sol.get_model() if l > 0)
    F = [edges[i] for i in range(len(edges)) if (i + 1) in model]
    degs = [0] * n
    for (a, b) in F:
        degs[a] += 1
        degs[b] += 1
    assert F and all(x in (0, 4) for x in degs), "SAT witness failed validation"
    return F


def has_4factor_balanced(P, Q, adj):
    """Spanning 4-regular subgraph of a balanced bipartite graph with sides P, Q (lists), by
    max flow. Independent of the SAT route."""
    assert len(P) == len(Q)
    if len(P) == 0:
        return True
    G = nx.DiGraph()
    src, snk = "s", "t"
    for p in P:
        G.add_edge(src, ("p", p), capacity=4)
        for q in adj[p]:
            if q in Q:
                G.add_edge(("p", p), ("q", q), capacity=1)
    for q in Q:
        G.add_edge(("q", q), snk, capacity=4)
    val = nx.maximum_flow_value(G, src, snk)
    return val == 4 * len(P)


def maxflow_balanced(P, Q, adj):
    assert len(P) == len(Q)
    G = nx.DiGraph()
    for p in P:
        G.add_edge("s", ("p", p), capacity=4)
        for q in adj[p]:
            if q in Q:
                G.add_edge(("p", p), ("q", q), capacity=1)
    for q in Q:
        G.add_edge(("q", q), "t", capacity=4)
    return nx.maximum_flow_value(G, "s", "t")


# ---- random instances -------------------------------------------------------------------

def random_bip_with_degrees(s, m, degU, degW, rng, tries=200):
    """Simple bipartite graph with the given degree sequences, or None. Randomized greedy:
    serve the U-vertex of largest remaining demand first, choosing among W-vertices of largest
    remaining demand (ties random), which is the Gale-Ryser greedy and succeeds when realizable."""
    assert sum(degU) == sum(degW)
    for _ in range(tries):
        remW = list(degW)
        edges = []
        order = list(range(s))
        rng.shuffle(order)
        order.sort(key=lambda u: -degU[u])
        ok = True
        for u in order:
            cands = [w for w in range(m) if remW[w] > 0]
            rng.shuffle(cands)
            cands.sort(key=lambda w: -remW[w])
            if len(cands) < degU[u]:
                ok = False
                break
            # randomize among equal-demand groups a little: take top degU[u]
            chosen = cands[:degU[u]]
            for w in chosen:
                remW[w] -= 1
                edges.append((u, s + w))
        if ok and all(r == 0 for r in remW):
            # random relabeling of W for extra randomness
            perm = list(range(m))
            rng.shuffle(perm)
            edges = [(u, s + perm[w - s]) for (u, w) in edges]
            return Bip(s, m, edges)
    return None


def random_C1(s, rng, DU=None, wlo=1, whi=6):
    """Random C1(s) instance: U-degrees all 6 except possibly one of degree 5 (DU in {0,1}),
    W-degrees in [wlo, whi] summing to 6s - DU."""
    if DU is None:
        DU = rng.choice([0, 1])
    m = s + 1
    degU = [6] * s
    if DU == 1:
        degU[rng.randrange(s)] = 5
    total = 6 * s - DU
    for _ in range(1000):
        degW = [wlo] * m
        rest = total - wlo * m
        if rest < 0:
            return None
        slots = [w for w in range(m) for _ in range(whi - wlo)]
        rng.shuffle(slots)
        if rest > len(slots):
            return None
        for w in slots[:rest]:
            degW[w] += 1
        B = random_bip_with_degrees(s, m, degU, degW, rng)
        if B is not None and B.is_C1():
            return B
    return None


def all_subsets_bits(n):
    return range(1 << n)


def bits_to_set(bits, n):
    return {i for i in range(n) if (bits >> i) & 1}
