"""wave4/theory tools: sparse E4 instances, 4-factors, rigidity, 2-edge cuts, 2EC' search.

Conventions: Y is a networkx Graph on vertices 0..n-1, bipartite; P = colour class 0 of a fixed
2-colouring (the class containing the smallest vertex of each component), Q = the other class.
For a vertex set S (python set/frozenset): g(S) = 6|S| - 2e(S), j(S) = |S_Q| - |S_P|,
D(Z) = sum (6 - deg). A 4-factor is a list/set of edges as frozensets.
"""
import itertools, random, sys
import networkx as nx
from networkx.algorithms.flow import edmonds_karp
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
from pysat.solvers import Cadical153

def ekey(u, v):
    return (u, v) if u < v else (v, u)

class Inst:
    def __init__(self, Y, P=None):
        self.Y = Y
        self.n = Y.number_of_nodes()
        if P is None:
            col = nx.bipartite.color(Y)
            P = {v for v in Y if col[v] == 0}
        self.P = frozenset(P)
        self.Q = frozenset(set(Y) - self.P)
        self.deg = dict(Y.degree())
        self.edges = [ekey(u, v) for u, v in Y.edges()]
        for (u, v) in self.edges:
            assert (u in self.P) != (v in self.P), "not bipartite w.r.t. P"
        # orient each edge as (p, q)
        self.pq = [(u, v) if u in self.P else (v, u) for (u, v) in self.edges]

    # ---------- basic set functions ----------
    def e_in(self, S):
        return sum(1 for (u, v) in self.edges if u in S and v in S)
    def g(self, S):
        return 6 * len(S) - 2 * self.e_in(S)
    def j(self, S):
        return len(S & self.Q) - len(S & self.P)
    def D(self, Z):
        return sum(6 - self.deg[v] for v in Z)
    def dQ(self, S):  # e(S_Q, P - S)
        return sum(1 for (p, q) in self.pq if q in S and p not in S)
    def dP(self, S):  # e(S_P, Q - S)
        return sum(1 for (p, q) in self.pq if p in S and q not in S)
    def s(self, S):   # flow slack = out-degree of S in any valid orientation
        return 4 * (len(S & self.P) - len(S & self.Q)) + self.dQ(S)
    def E0(self, T):  # edges from T_Q to P - T, as (p, q)
        return [(p, q) for (p, q) in self.pq if q in T and p not in T]
    def E1(self, T):  # edges from T_P to Q - T
        return [(p, q) for (p, q) in self.pq if p in T and q not in T]

    # ---------- sparsity: min g over 2 <= |S| <= n-1 ----------
    def min_g_proper(self, want_witness=False):
        """Exact: for every edge uv and every w not in {u,v}, min cut with u,v on the source side
        and w on the sink side; cut(S) = boundary(S) + D(S) = g(S). An inclusion-minimal
        violator of any bound with >= 2 vertices contains an edge (g of an independent set
        S is 6|S| >= 12, and removing a vertex of S-degree <= 2 lowers g), so this is exact
        for the minimum over sets with >= 2 vertices, provided the minimum is <= 12; we only
        rely on it for deciding g >= 10."""
        best, wit = 10 ** 9, None
        Y = self.Y
        for (u, v) in self.edges:
            for w in Y:
                if w in (u, v):
                    continue
                G = nx.DiGraph()
                for (a, b) in self.edges:
                    G.add_edge(a, b, capacity=1)
                    G.add_edge(b, a, capacity=1)
                for x in Y:
                    d = 6 - self.deg[x]
                    if d > 0:
                        G.add_edge(x, 't', capacity=d)
                G.add_edge('s', u, capacity=10 ** 6)
                G.add_edge('s', v, capacity=10 ** 6)
                G.add_edge(w, 't', capacity=10 ** 6)
                val, (S, _) = nx.minimum_cut(G, 's', 't', flow_func=edmonds_karp)
                if val < best:
                    best = val
                    wit = frozenset(x for x in S if x != 's')
        return (best, wit) if want_witness else best

    # ---------- 4-factors ----------
    def _flow_graph(self, cost=None):
        G = nx.DiGraph()
        for p in self.P:
            G.add_edge('s', p, capacity=4, weight=0)
        for q in self.Q:
            G.add_edge(q, 't', capacity=4, weight=0)
        for (p, q) in self.pq:
            c = 0 if cost is None else cost.get((p, q), 0)
            G.add_edge(p, q, capacity=1, weight=c)
        return G

    def four_factor(self, cost=None):
        """A 4-factor (min cost if cost given: dict (p,q)->int), or None."""
        G = self._flow_graph(cost)
        if cost is None:
            val, fl = nx.maximum_flow(G, 's', 't')
        else:
            fl = nx.max_flow_min_cost(G, 's', 't')
            val = sum(fl['s'][p] for p in self.P)
        if val != 4 * len(self.P):
            return None
        return frozenset((p, q) for (p, q) in self.pq if fl[p][q] == 1)

    def random_four_factor(self, rng, spread=1000):
        cost = {e: rng.randrange(spread) for e in self.pq}
        return self.four_factor(cost)

    def max_in(self, E0):
        """max over 4-factors F of |F ∩ E0| (E0 list of (p,q)); returns (value, F)."""
        E0 = set(E0)
        cost = {e: (-1 if e in E0 else 0) for e in self.pq}
        F = self.four_factor(cost)
        if F is None:
            return None, None
        return len(F & E0), F

    def is_rigid(self, T):
        T = frozenset(T)
        v, _ = self.max_in(self.E0(T))
        return v <= 1

    # ---------- cuts of a 4-factor ----------
    def bad_sets(self, F, limit=100000):
        """All balanced T (2 <= |T| <= n-2, T containing vertex min(V) excluded: we return
        both T and V-T normalised so that the smaller-index side is listed once) with
        boundary_F(T) <= 2. Returned as frozensets T with min(V) not in T (canonical)."""
        V = frozenset(self.Y)
        v0 = min(V)
        Fg = nx.Graph()
        Fg.add_nodes_from(V)
        Fg.add_edges_from(F)
        comps = [frozenset(c) for c in nx.connected_components(Fg)]
        out = set()
        Fl = list(F)
        if len(comps) > 1:
            # all unions of components (0-cuts) plus 2-cuts inside components unioned with others
            if len(comps) > 12:
                raise RuntimeError("too many components")
            base = []
            for r in range(1, len(comps)):
                for sub in itertools.combinations(comps, r):
                    base.append(frozenset().union(*sub))
            for B in base:
                T = B if v0 not in B else V - B
                out.add(T)
        # 2-edge cuts inside each component, combined with unions of other components
        for C in comps:
            Ce = [e for e in Fl if e[0] in C]
            H = Fg.subgraph(C).copy()
            for a in range(len(Ce)):
                H.remove_edge(*Ce[a])
                for b in range(a + 1, len(Ce)):
                    H.remove_edge(*Ce[b])
                    if not nx.is_connected(H):
                        parts = [frozenset(x) for x in nx.connected_components(H)]
                        if len(parts) == 2:
                            A = parts[0]
                            others = [c for c in comps if c != C]
                            for r in range(0, len(others) + 1):
                                for sub in itertools.combinations(others, r):
                                    B = A.union(*sub) if sub else A
                                    T = B if v0 not in B else V - B
                                    if 2 <= len(T) <= len(V) - 2:
                                        out.add(T)
                    H.add_edge(*Ce[b])
                H.add_edge(*Ce[a])
                if len(out) > limit:
                    raise RuntimeError("too many bad sets")
        return out

    def is_good(self, F):
        """F connected and no 2-edge cut (4-edge-connected)."""
        Fg = nx.Graph()
        Fg.add_nodes_from(self.Y)
        Fg.add_edges_from(F)
        return nx.edge_connectivity(Fg) >= 4

    def a_bad_set(self, F):
        Fg = nx.Graph()
        Fg.add_nodes_from(self.Y)
        Fg.add_edges_from(F)
        if not nx.is_connected(Fg):
            return frozenset(next(iter(nx.connected_components(Fg))))
        cut = nx.minimum_edge_cut(Fg)
        if len(cut) >= 4:
            return None
        H = Fg.copy()
        H.remove_edges_from(cut)
        return frozenset(next(iter(nx.connected_components(H))))

    # ---------- exact search: a 4-factor with no 2-edge cut ----------
    def search_good(self, max_iter=100000, verbose=False):
        """SAT with lazy cut constraints. Returns (F, n_cuts) or (None, n_cuts) if none exists."""
        pool = IDPool()
        var = {e: pool.id(('x', e)) for e in self.pq}
        S = Cadical153()
        for v in self.Y:
            lits = [var[e] for e in self.pq if v in e]
            cnf = CardEnc.equals(lits=lits, bound=4, vpool=pool, encoding=EncType.seqcounter)
            for cl in cnf.clauses:
                S.add_clause(cl)
        added = 0
        for it in range(max_iter):
            if not S.solve():
                S.delete()
                return None, added
            m = set(l for l in S.get_model() if l > 0)
            F = frozenset(e for e in self.pq if var[e] in m)
            T = self.a_bad_set(F)
            if T is None:
                S.delete()
                return F, added
            lits = [var[e] for e in self.E0(T)]
            if len(lits) < 2:
                S.delete()
                return None, added  # thin set: no 4-factor can have c >= 2
            cnf = CardEnc.atleast(lits=lits, bound=2, vpool=pool, encoding=EncType.seqcounter)
            for cl in cnf.clauses:
                S.add_clause(cl)
            added += 1
            if verbose and added % 50 == 0:
                print('cuts', added, file=sys.stderr)
        raise RuntimeError("max_iter")

    # ---------- rigid sets ----------
    def rigid_sets(self, rng=None, n_factors=6):
        """All rigid T (canonical side): rigid T is bad for every 4-factor, so intersect the bad
        families of a few 4-factors, then test each survivor exactly."""
        rng = rng or random.Random(1)
        F0 = self.four_factor()
        if F0 is None:
            return None
        cand = self.bad_sets(F0)
        for _ in range(n_factors):
            if not cand:
                break
            F = self.random_four_factor(rng)
            Fg = nx.Graph(); Fg.add_nodes_from(self.Y); Fg.add_edges_from(F)
            keep = set()
            for T in cand:
                if 2 * sum(1 for (p, q) in F if q in T and p not in T) <= 2:
                    keep.add(T)
            cand = keep
        return [T for T in cand if self.is_rigid(T)]

def from_g6(s, P=None):
    Y = nx.from_graph6_bytes(s.strip().encode())
    return Inst(Y, P)

def to_g6(Y):
    return nx.to_graph6_bytes(Y, nodes=sorted(Y), header=False).decode().strip()
