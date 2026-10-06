"""Shared helpers for the C1 checks (lane M3). Own code; nothing imported from G110/checks.

Convention: a bipartite graph is given by sizes (nu, nw) and an edge list of pairs (u, w) with
0 <= u < nu (side U) and 0 <= w < nw (side W). Internally vertices are numbered U = 0..nu-1 and
W = nu..nu+nw-1, and vertex sets are bitmasks over these n = nu + nw vertices.
"""
import itertools
import random

import networkx as nx
from pysat.solvers import Cadical153


class BG:
    """Simple bipartite graph with sides U (0..nu-1) and W (nu..nu+nw-1)."""

    def __init__(self, nu, nw, edges):
        self.nu, self.nw = nu, nw
        self.n = nu + nw
        es = set()
        for (u, w) in edges:
            assert 0 <= u < nu and 0 <= w < nw
            assert (u, w) not in es, "not simple"
            es.add((u, w))
        self.edges = sorted(es)
        self.adj = [set() for _ in range(self.n)]
        for (u, w) in self.edges:
            self.adj[u].add(nu + w)
            self.adj[nu + w].add(u)
        self.deg = [len(a) for a in self.adj]
        self.U = list(range(nu))
        self.W = list(range(nu, nu + nw))
        self.Umask = (1 << nu) - 1
        self.Wmask = ((1 << nw) - 1) << nu
        self.full = (1 << self.n) - 1
        # edge list in global numbering
        self.gedges = [(u, nu + w) for (u, w) in self.edges]

    def defic(self, v):
        return 6 - self.deg[v]

    def e_inside(self, mask):
        return sum(1 for (a, b) in self.gedges if (mask >> a) & 1 and (mask >> b) & 1)

    def e_between(self, m1, m2):
        return sum(1 for (a, b) in self.gedges
                   if ((m1 >> a) & 1 and (m2 >> b) & 1) or ((m2 >> a) & 1 and (m1 >> b) & 1))

    def g(self, mask):
        return 6 * popcount(mask) - 2 * self.e_inside(mask)

    def kappa(self, mask):
        return popcount(mask & self.Umask) - popcount(mask & self.Wmask)

    def D(self, mask):
        return sum(self.defic(v) for v in members(mask))

    def Din(self, mask, sub):
        """deficiency of the vertex set `sub` inside G[mask] (sub subset of mask)."""
        tot = 0
        for v in members(sub):
            tot += 6 - sum(1 for x in self.adj[v] if (mask >> x) & 1)
        return tot

    def deg_in(self, v, mask):
        return sum(1 for x in self.adj[v] if (mask >> x) & 1)

    def max_deg(self):
        return max(self.deg) if self.deg else 0


def popcount(x):
    return bin(x).count("1")


def members(mask):
    out = []
    i = 0
    while mask:
        if mask & 1:
            out.append(i)
        mask >>= 1
        i += 1
    return out


def mask_of(vs):
    m = 0
    for v in vs:
        m |= 1 << v
    return m


# ---------------------------------------------------------------- random graphs

def random_bipartite_degrees(du, dw, rng, swaps_factor=20, tries=200):
    """Random simple bipartite graph with U-degrees du and W-degrees dw (lists), or None.
    Greedy construction (largest remaining W-degree first, random ties), then degree-preserving
    double-edge swaps."""
    nu, nw = len(du), len(dw)
    if sum(du) != sum(dw):
        return None
    for _ in range(tries):
        rem = list(dw)
        edges = set()
        ok = True
        order = list(range(nu))
        rng.shuffle(order)
        order.sort(key=lambda u: -du[u])
        for u in order:
            cand = list(range(nw))
            rng.shuffle(cand)
            cand.sort(key=lambda w: -rem[w])
            chosen = [w for w in cand if rem[w] > 0][:du[u]]
            if len(chosen) < du[u]:
                ok = False
                break
            for w in chosen:
                rem[w] -= 1
                edges.add((u, w))
        if not ok or any(rem):
            continue
        edges = list(edges)
        eset = set(edges)
        for _ in range(swaps_factor * len(edges)):
            i, j = rng.randrange(len(edges)), rng.randrange(len(edges))
            (u1, w1), (u2, w2) = edges[i], edges[j]
            if u1 == u2 or w1 == w2:
                continue
            if (u1, w2) in eset or (u2, w1) in eset:
                continue
            eset.discard((u1, w1)); eset.discard((u2, w2))
            eset.add((u1, w2)); eset.add((u2, w1))
            edges[i], edges[j] = (u1, w2), (u2, w1)
        return BG(nu, nw, edges)
    return None


def random_c1(s, rng, DU=1, wmin=4, wmax=6):
    """Random C1(s) instance with U-deficiency DU (0 or 1) and W-degrees in [wmin, wmax]."""
    du = [6] * s
    if DU == 1:
        du[-1] = 5
    total = sum(du)
    for _ in range(1000):
        dw = [rng.randint(wmin, wmax) for _ in range(s + 1)]
        diff = total - sum(dw)
        # adjust randomly toward the total
        idx = list(range(s + 1))
        guard = 0
        while diff != 0 and guard < 10000:
            guard += 1
            i = rng.choice(idx)
            if diff > 0 and dw[i] < wmax:
                dw[i] += 1; diff -= 1
            elif diff < 0 and dw[i] > wmin:
                dw[i] -= 1; diff += 1
        if diff != 0:
            continue
        G = random_bipartite_degrees(du, dw, rng)
        if G is not None:
            return G
    return None


# ---------------------------------------------------------------- subset tables (pure Python DP)

class Tables:
    """Per-subset lists over all 2^n vertex subsets (n <= 17), built by DP on the lowest bit:
    size, nU, nW, DU (G-deficiency of S_U), DW (G-deficiency of S_W), sdegW (sum of G-degrees
    over S_W), eS (edges of G[S]), g = 6|S| - 2 eS, kappa = |S_U| - |S_W|."""

    def __init__(self, G):
        n = G.n
        assert n <= 17
        self.G = G
        N = 1 << n
        nb = [0] * n
        for v in range(n):
            for x in G.adj[v]:
                nb[v] |= 1 << x
        size = [0] * N; nU = [0] * N; nW = [0] * N
        DU = [0] * N; DW = [0] * N; sdegW = [0] * N; eS = [0] * N
        nu = G.nu
        deg = G.deg
        for m in range(1, N):
            low = m & (-m)
            v = low.bit_length() - 1
            r = m ^ low
            size[m] = size[r] + 1
            eS[m] = eS[r] + (nb[v] & r).bit_count()
            if v < nu:
                nU[m] = nU[r] + 1; nW[m] = nW[r]
                DU[m] = DU[r] + 6 - deg[v]; DW[m] = DW[r]; sdegW[m] = sdegW[r]
            else:
                nU[m] = nU[r]; nW[m] = nW[r] + 1
                DU[m] = DU[r]; DW[m] = DW[r] + 6 - deg[v]; sdegW[m] = sdegW[r] + deg[v]
        self.size, self.nU, self.nW = size, nU, nW
        self.DU, self.DW, self.sdegW, self.eS = DU, DW, sdegW, eS
        self.g = [6 * size[m] - 2 * eS[m] for m in range(N)]
        self.kappa = [nU[m] - nW[m] for m in range(N)]
        self.nb = nb


# ---------------------------------------------------------------- SAT: quartic subgraphs

def _atleast_direct(L, k, guard=None):
    """clauses saying at least k of literals L are true (guarded by literal `guard` if given)."""
    cls = []
    if k <= 0:
        return cls
    if k > len(L):
        return [[-guard]] if guard is not None else [[]]
    for sub in itertools.combinations(L, len(L) - k + 1):
        c = list(sub)
        if guard is not None:
            c = c + [-guard]
        cls.append(c)
    return cls


def _atmost_direct(L, k, guard=None):
    cls = []
    if k >= len(L):
        return cls
    for sub in itertools.combinations(L, k + 1):
        c = [-x for x in sub]
        if guard is not None:
            c = c + [-guard]
        cls.append(c)
    return cls


def quartic_sat(n, edges, forced=None, require_nonempty=True, forbid_edges=()):
    """Find F subset of `edges` (list of vertex pairs, parallel edges allowed as repeats) with
    deg_F(v) + forced.get(v, 0) in {0, 4} for all v. Returns list of edge indices or None.
    If require_nonempty, F must be nonempty (only meaningful when forced is empty)."""
    forced = forced or {}
    inc = [[] for _ in range(n)]
    for i, (a, b) in enumerate(edges):
        inc[a].append(i + 1)
        inc[b].append(i + 1)
    nv = len(edges)
    z = [nv + 1 + v for v in range(n)]
    cls = []
    for i in forbid_edges:
        cls.append([-(i + 1)])
    for v in range(n):
        L = inc[v]
        t = forced.get(v, 0)
        if t > 0:
            need = 4 - t
            if need < 0:
                return None
            cls += _atleast_direct(L, need)
            cls += _atmost_direct(L, need)
        else:
            for x in L:
                cls.append([-x, z[v]])
            cls += _atleast_direct(L, 4, guard=z[v])
            cls += _atmost_direct(L, 4)
    if require_nonempty and not forced:
        cls.append([i + 1 for i in range(nv)])
    with Cadical153(bootstrap_with=cls) as S:
        if not S.solve():
            return None
        model = set(l for l in S.get_model() if l > 0)
    F = [i for i in range(nv) if (i + 1) in model]
    # validate
    degs = [0] * n
    for i in F:
        a, b = edges[i]
        degs[a] += 1
        degs[b] += 1
    for v in range(n):
        assert degs[v] + forced.get(v, 0) in (0, 4), "bad witness"
    if require_nonempty and not forced:
        assert F
    return F


def has_quartic(G, vmask=None):
    """Quartic subgraph of G[vmask] (default: all of G). Returns edge list or None."""
    if vmask is None:
        vmask = G.full
    es = [(a, b) for (a, b) in G.gedges if (vmask >> a) & 1 and (vmask >> b) & 1]
    F = quartic_sat(G.n, es)
    return None if F is None else [es[i] for i in F]


# ---------------------------------------------------------------- flows: 4-factors

def has_4factor(G, delete=()):
    """Spanning 4-regular subgraph of G minus the vertices in `delete` (must be balanced)."""
    dl = set(delete)
    Us = [u for u in G.U if u not in dl]
    Ws = [w for w in G.W if w not in dl]
    if len(Us) != len(Ws):
        return False
    if not Us:
        return False
    H = nx.DiGraph()
    for u in Us:
        H.add_edge("s", u, capacity=4)
    for w in Ws:
        H.add_edge(w, "t", capacity=4)
    for (a, b) in G.gedges:
        if a in dl or b in dl:
            continue
        H.add_edge(a, b, capacity=1)
    val = nx.maximum_flow_value(H, "s", "t")
    return val == 4 * len(Us)


def max_flow_value(G, delete=()):
    dl = set(delete)
    Us = [u for u in G.U if u not in dl]
    Ws = [w for w in G.W if w not in dl]
    H = nx.DiGraph()
    H.add_node("s"); H.add_node("t")
    for u in Us:
        H.add_edge("s", u, capacity=4)
    for w in Ws:
        H.add_edge(w, "t", capacity=4)
    for (a, b) in G.gedges:
        if a in dl or b in dl:
            continue
        H.add_edge(a, b, capacity=1)
    return nx.maximum_flow_value(H, "s", "t")


def parse_genbg_line(line, nu, nw):
    """graph6 line from genbg (first class = first nu vertices) to a BG."""
    G = nx.from_graph6_bytes(line.strip().encode())
    edges = []
    for (a, b) in G.edges():
        if a > b:
            a, b = b, a
        assert a < nu <= b, "not bipartite in the expected classes"
        edges.append((a, b - nu))
    return BG(nu, nw, edges)


# ---------------------------------------------------------------- sparsity by max-closure flows

def min_g_proper(G, stop_below=None):
    """Exact min of g(S) = 6|S| - 2e(G[S]) over S with 2 <= |S| <= n - 1 that contain an edge
    (sets without an edge have g = 6|S| >= 12, so for the test 'g >= 10' this loses nothing).
    For each vertex c and each edge ab of G - c: max of e(S) - 3|S| over {a,b} <= S <= V - c is a
    max-weight closure (edge nodes profit 1, vertex nodes cost 3, a and b forced in), solved by a
    min cut. Returns (min_g, witness_mask). If stop_below is given, returns as soon as a set with
    g < stop_below is found."""
    best, wit = None, None
    for c in range(G.n):
        es = [(a, b) for (a, b) in G.gedges if a != c and b != c]
        for (a, b) in es:
            H = nx.DiGraph()
            H.add_node("s"); H.add_node("t")
            forced = {a, b}
            for i, (x, y) in enumerate(es):
                H.add_edge("s", ("e", i), capacity=1)
                H.add_edge(("e", i), ("v", x))
                H.add_edge(("e", i), ("v", y))
            for v in range(G.n):
                if v == c or v in forced:
                    continue
                H.add_edge(("v", v), "t", capacity=3)
            cut, (S_side, _) = nx.minimum_cut(H, "s", "t")
            val = len(es) - cut - 3 * len(forced)
            g = -2 * val
            if best is None or g < best:
                mask = (1 << a) | (1 << b)
                for node in S_side:
                    if isinstance(node, tuple) and node[0] == "v":
                        mask |= 1 << node[1]
                assert G.g(mask) == g, "closure value mismatch"
                best, wit = g, mask
                if stop_below is not None and best < stop_below:
                    return best, wit
    return best, wit


def min_cut_violation(G, y):
    """For a port y with no 4-factor in G - y: a minimum cut S = A u C (A = S_W, C = S_U) of the
    flow network, as a vertex mask, and its slack e(A, U - C) - 4(|A| - |C|)."""
    Us = list(G.U)
    Ws = [w for w in G.W if w != y]
    H = nx.DiGraph()
    for u in Us:
        H.add_edge("s", u, capacity=4)
    for w in Ws:
        H.add_edge(w, "t", capacity=4)
    for (a, b) in G.gedges:
        if b == y:
            continue
        H.add_edge(a, b, capacity=1)
    cut, (S_side, T_side) = nx.minimum_cut(H, "s", "t")
    # source side contains s, U - C, and the W-vertices A' reachable; our cut (A, C) has
    # A = W-vertices on the source side? In the network s->u->w->t, a cut with source side
    # {s} u U1 u W1 has capacity 4|U - U1| + e(U1, W - W1) + 4|W1|. Matching Lemma 0.1 with
    # P = W - y, Q = U (A subset of P, C subset of Q) we use the reversed network instead.
    U1 = {v for v in S_side if isinstance(v, int) and v < G.nu}
    W1 = {v for v in S_side if isinstance(v, int) and v >= G.nu}
    # capacity = 4|U - U1| + e(U1, W' - W1) + 4|W1| = 4s + [e(U1, W' - W1) - 4(|U1| - |W1|)]
    # i.e. a cut of the U-side form: A_U = U1 (subset of U), C_W = W1. Convert to the W-side form
    # used in the paper by complementing: S = (W' - W1) u (U - U1) gives the same slack (check below).
    A = set(Ws) - W1
    C = set(Us) - U1
    mask = 0
    for v in A | C:
        mask |= 1 << v
    Cs = C
    eAUC = sum(1 for a in A for x in G.adj[a] if x not in Cs)
    slack = eAUC - 4 * (len(A) - len(C))
    assert slack == cut - 4 * len(Us), (slack, cut - 4 * len(Us))
    return mask, slack
