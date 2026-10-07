#!/usr/bin/env python3
"""myspan.py -- the s6hunt lane's own exact deciders (wave5/s6hunt). Written from the definitions; it
shares no code with wave4/va6/tools/span_oracle.py or 585-fable-wildcard/tools/pair_oracle.py.

  span2hc(n, edges, seconds)   two edge-disjoint Hamilton cycles of the whole graph (a spanning pair).
                               SAT (Glucose 4.1): x[c][e] for colors c = 0, 1; every vertex has
                               exactly two edges of each color (direct clauses, degrees <= 8); no edge
                               has both colors; connectivity by lazy cut clauses: when color c splits
                               into components, for each component K and BOTH colors c' add
                               OR{x[c'][e] : e in delta(K)} (every Hamilton cycle crosses delta(K)).
                               SPAN comes with two cycles that verify_span() re-checks; NOSPAN is an
                               UNSAT answer over valid clauses (exact); TIMEOUT is inconclusive.
  find_pair(n, edges, seconds, max_support=None, assumptions)
                               a pair (two edge-disjoint cycles on one vertex set) anywhere in the graph:
                               support variables s[v]; colored edges have both ends in the support; a
                               support vertex has exactly two edges of each color; lazy cuts with
                               auxiliary a_K, b_K (support meets K, support meets V - K) imply a crossing
                               edge of each color.
  min_pair(n, edges, seconds)  smallest support by descending bounds (incremental totalizer); exact
                               when it ends with UNSAT inside the time limit.
  count_pairs(n, edges, size, cap, seconds)  number of distinct supports of exactly 'size' vertices that
                               carry a pair (up to cap), by blocking clauses.
"""
import itertools, threading, time

from pysat.card import ITotalizer
from pysat.solvers import Solver

SOLVER = "glucose4"


def canon(edges):
    out = set()
    for a, b in edges:
        a, b = int(a), int(b)
        assert a != b
        out.add((min(a, b), max(a, b)))
    return sorted(out)


class _UF:
    def __init__(self, items):
        self.p = {v: v for v in items}

    def f(self, v):
        while self.p[v] != v:
            self.p[v] = self.p[self.p[v]]
            v = self.p[v]
        return v

    def u(self, a, b):
        a, b = self.f(a), self.f(b)
        if a != b:
            self.p[a] = b


def _components(vertices, edge_list):
    uf = _UF(vertices)
    for a, b in edge_list:
        uf.u(a, b)
    comp = {}
    for v in vertices:
        comp.setdefault(uf.f(v), []).append(v)
    return list(comp.values())


def _solve(solver, deadline, assumptions=()):
    remaining = deadline - time.monotonic()
    if remaining <= 0:
        return None
    timer = threading.Timer(remaining, solver.interrupt)
    timer.daemon = True
    timer.start()
    try:
        ok = solver.solve_limited(assumptions=list(assumptions), expect_interrupt=True)
    finally:
        timer.cancel()
        solver.clear_interrupt()
    return ok


def _exactly2(lits):
    cl = []
    for t in itertools.combinations(lits, 3):
        cl.append([-l for l in t])
    for j in range(len(lits)):
        cl.append(lits[:j] + lits[j + 1:])
    return cl


def cycle_order(cyc_edges):
    adj = {}
    for a, b in cyc_edges:
        adj.setdefault(a, []).append(b)
        adj.setdefault(b, []).append(a)
    start = min(adj)
    order, prev, cur = [start], None, start
    while True:
        nb = adj[cur]
        nxt = nb[0] if nb[0] != prev else nb[1]
        if prev is None:
            nxt = min(nb)
        if nxt == start:
            break
        order.append(nxt)
        prev, cur = cur, nxt
    return order


def verify_cycles(edges, cycles, vertex_set=None):
    """cycles: two vertex sequences. True iff both are cycles of the graph on the same vertex set
    (equal to vertex_set if given), edge-disjoint, each simple."""
    E = set(canon(edges))
    sets, esets = [], []
    for c in cycles:
        if len(c) < 3 or len(set(c)) != len(c):
            return False
        es = set()
        for i in range(len(c)):
            a, b = c[i], c[(i + 1) % len(c)]
            e = (min(a, b), max(a, b))
            if e not in E or e in es:
                return False
            es.add(e)
        sets.append(set(c)); esets.append(es)
    if sets[0] != sets[1] or esets[0] & esets[1]:
        return False
    if vertex_set is not None and sets[0] != set(vertex_set):
        return False
    return True


def span2hc(n, edges, seconds=120.0, vertices=None, pool=None):
    """Two edge-disjoint Hamilton cycles on the vertex set (default range(n)).
    pool: optional list of vertex sets (frozensets) shared across calls on subgraphs of one host; each
    set S with both S and V - S meeting the vertex set gives the valid seed clause 'every Hamilton cycle
    crosses delta(S)' for both colors (speed only), and components found here are appended to it."""
    V = sorted(vertices) if vertices is not None else list(range(n))
    E = canon(edges)
    inc = {v: [] for v in V}
    for i, (a, b) in enumerate(E):
        inc[a].append(i); inc[b].append(i)
    if any(len(inc[v]) < 4 for v in V):
        return {"status": "NOSPAN", "rounds": 0, "reason": "degree<4"}
    m = len(E)
    X = [[1 + c * m + i for i in range(m)] for c in range(2)]
    cl = [[-X[0][i], -X[1][i]] for i in range(m)]
    for v in V:
        for c in range(2):
            cl.extend(_exactly2([X[c][i] for i in inc[v]]))
    nseed = 0
    if pool:
        Vs = set(V)
        for P in pool:
            inside = len(P & Vs)
            if inside == 0 or inside == len(V):
                continue
            cut = [i for i, (a, b) in enumerate(E) if (a in P) != (b in P)]
            if cut:
                nseed += 1
                for cc in range(2):
                    cl.append([X[cc][i] for i in cut])
    deadline = time.monotonic() + seconds
    rounds = 0
    with Solver(name=SOLVER, bootstrap_with=cl) as S:
        while True:
            ok = _solve(S, deadline)
            if ok is None:
                return {"status": "TIMEOUT", "rounds": rounds, "seeds": nseed}
            if ok is False:
                return {"status": "NOSPAN", "rounds": rounds, "seeds": nseed}
            rounds += 1
            model = S.get_model()
            pos = set(l for l in model if l > 0)
            col = [[E[i] for i in range(m) if X[c][i] in pos] for c in range(2)]
            split = False
            for c in range(2):
                comps = _components(V, col[c])
                if len(comps) == 1:
                    continue
                split = True
                for K in comps:
                    Ks = set(K)
                    cut = [i for i, (a, b) in enumerate(E) if (a in Ks) != (b in Ks)]
                    for cc in range(2):
                        S.add_clause([X[cc][i] for i in cut])
                    if pool is not None and 3 <= len(K) <= len(V) - 3:
                        pool.append(frozenset(K))
            if not split:
                cyc = [cycle_order(col[0]), cycle_order(col[1])]
                return {"status": "SPAN", "rounds": rounds, "cycles": cyc, "seeds": nseed,
                        "verified": verify_cycles(E, cyc, V)}


class PairSolver:
    """Incremental pair search on a fixed graph (support variables + lazy cuts)."""

    def __init__(self, n, edges, vertices=None):
        self.V = sorted(vertices) if vertices is not None else list(range(n))
        self.E = canon(edges)
        Vs = set(self.V)
        self.E = [e for e in self.E if e[0] in Vs and e[1] in Vs]
        self.m = len(self.E)
        self.top = 0
        self.s = {v: self._new() for v in self.V}
        self.X = [[self._new() for _ in range(self.m)] for _ in range(2)]
        self.inc = {v: [] for v in self.V}
        for i, (a, b) in enumerate(self.E):
            self.inc[a].append(i); self.inc[b].append(i)
        cl = [[self.s[v] for v in self.V]]
        for i, (a, b) in enumerate(self.E):
            cl.append([-self.X[0][i], -self.X[1][i]])
            for c in range(2):
                cl.append([-self.X[c][i], self.s[a]])
                cl.append([-self.X[c][i], self.s[b]])
        for v in self.V:
            for c in range(2):
                lits = [self.X[c][i] for i in self.inc[v]]
                if len(lits) < 2:
                    cl.append([-self.s[v]])
                    continue
                for t in itertools.combinations(lits, 3):
                    cl.append([-l for l in t])
                for j in range(len(lits)):
                    cl.append([-self.s[v]] + lits[:j] + lits[j + 1:])
        self.S = Solver(name=SOLVER, bootstrap_with=cl)
        self.tot = None
        self.rounds = 0
        self.cuts = 0

    def _new(self):
        self.top += 1
        return self.top

    def close(self):
        self.S.delete()

    def _bound_lits(self, k):
        """assumption literals forcing support size <= k."""
        if k is None or k >= len(self.V):
            return []
        if self.tot is None:
            self.tot = ITotalizer(lits=[self.s[v] for v in self.V], ubound=len(self.V), top_id=self.top)
            self.top = self.tot.top_id
            for c in self.tot.cnf.clauses:
                self.S.add_clause(c)
        return [-self.tot.rhs[k]]

    def block_support(self, supp):
        self.S.add_clause([-self.s[v] for v in supp])

    def solve(self, deadline, max_support=None):
        """Returns ("PAIR", support, cycles) / ("NOPAIR", ..) / ("TIMEOUT", ..)."""
        assum = self._bound_lits(max_support)
        while True:
            ok = _solve(self.S, deadline, assum)
            if ok is None:
                return "TIMEOUT", None, None
            if ok is False:
                return "NOPAIR", None, None
            self.rounds += 1
            pos = set(l for l in self.S.get_model() if l > 0)
            supp = [v for v in self.V if self.s[v] in pos]
            col = [[self.E[i] for i in range(self.m) if self.X[c][i] in pos] for c in range(2)]
            comps = [_components(supp, col[c]) for c in range(2)]
            if len(comps[0]) == 1 and len(comps[1]) == 1:
                cyc = [cycle_order(col[0]), cycle_order(col[1])]
                return "PAIR", supp, cyc
            for c in range(2):
                if len(comps[c]) == 1:
                    continue
                for K in comps[c]:
                    Ks = set(K)
                    a = self._new(); b = self._new()
                    for u in self.V:
                        self.S.add_clause([-self.s[u], a if u in Ks else b])
                    cut = [i for i, (p, q) in enumerate(self.E) if (p in Ks) != (q in Ks)]
                    for cc in range(2):
                        self.S.add_clause([-a, -b] + [self.X[cc][i] for i in cut])
                    self.cuts += 1


def find_pair(n, edges, seconds=60.0, max_support=None, vertices=None):
    P = PairSolver(n, edges, vertices)
    t0 = time.monotonic()
    try:
        st, supp, cyc = P.solve(t0 + seconds, max_support)
        out = {"status": st, "rounds": P.rounds, "t": round(time.monotonic() - t0, 3)}
        if st == "PAIR":
            out.update(support=supp, size=len(supp), cycles=cyc, verified=verify_cycles(P.E, cyc, supp))
        return out
    finally:
        P.close()


def min_pair(n, edges, seconds=120.0, vertices=None, start_bound=None):
    """Descending search. Returns dict with best size found, exact flag, witness, timings."""
    P = PairSolver(n, edges, vertices)
    t0 = time.monotonic()
    deadline = t0 + seconds
    best = None
    t_first = None
    k = start_bound
    try:
        while True:
            st, supp, cyc = P.solve(deadline, k)
            if st == "PAIR":
                if not verify_cycles(P.E, cyc, supp):
                    return {"status": "BADWITNESS"}
                best = (len(supp), supp, cyc)
                if t_first is None:
                    t_first = time.monotonic() - t0
                k = len(supp) - 1
                if k < 8:
                    return {"status": "EXACT", "min": best[0], "support": best[1], "cycles": best[2],
                            "t_first": round(t_first, 3), "t": round(time.monotonic() - t0, 3),
                            "rounds": P.rounds}
                continue
            if st == "NOPAIR":
                if best is None:
                    return {"status": "NOPAIR" if start_bound is None else "NOPAIR_UNDER_BOUND",
                            "t": round(time.monotonic() - t0, 3), "rounds": P.rounds}
                return {"status": "EXACT", "min": best[0], "support": best[1], "cycles": best[2],
                        "t_first": round(t_first, 3), "t": round(time.monotonic() - t0, 3), "rounds": P.rounds}
            # TIMEOUT
            if best is None:
                return {"status": "TIMEOUT", "t": round(time.monotonic() - t0, 3), "rounds": P.rounds,
                        "lower": None}
            return {"status": "UPPER", "min_upper": best[0], "support": best[1], "cycles": best[2],
                    "t_first": round(t_first, 3), "t": round(time.monotonic() - t0, 3), "rounds": P.rounds,
                    "open_below": k}
    finally:
        P.close()


def count_pairs(n, edges, size, cap=50, seconds=60.0, vertices=None):
    """Distinct supports of exactly `size` vertices carrying a pair (size must be the minimum, so that
    the bound <= size forces equality)."""
    P = PairSolver(n, edges, vertices)
    t0 = time.monotonic()
    found = 0
    try:
        while found < cap:
            st, supp, cyc = P.solve(t0 + seconds, size)
            if st != "PAIR":
                return {"count": found, "complete": st == "NOPAIR", "t": round(time.monotonic() - t0, 3)}
            found += 1
            P.block_support(supp)
        return {"count": found, "complete": False, "capped": True, "t": round(time.monotonic() - t0, 3)}
    finally:
        P.close()


if __name__ == "__main__":
    import json, sys
    d = json.load(open(sys.argv[1]))
    n, E = d["n"], d["edges"]
    print(json.dumps({k: v for k, v in span2hc(n, E).items() if k != "cycles"}))


def _paths_solver(V, E, colors, exact_cover=False):
    """CNF for `colors` edge-disjoint Hamiltonian paths on V (each color: every vertex has degree 1 or 2,
    exactly two vertices of degree 1). exact_cover: every edge gets exactly one color."""
    from pysat.card import CardEnc, EncType
    from pysat.formula import IDPool
    m = len(E)
    pool = IDPool()
    X = [[pool.id(("x", c, i)) for i in range(m)] for c in range(colors)]
    END = [{v: pool.id(("end", c, v)) for v in V} for c in range(colors)]
    inc = {v: [] for v in V}
    for i, (a, b) in enumerate(E):
        inc[a].append(i); inc[b].append(i)
    cl = []
    for i in range(m):
        for c1 in range(colors):
            for c2 in range(c1 + 1, colors):
                cl.append([-X[c1][i], -X[c2][i]])
        if exact_cover:
            cl.append([X[c][i] for c in range(colors)])
    for v in V:
        for c in range(colors):
            lits = [X[c][i] for i in inc[v]]
            if not lits:
                return None
            cl.append(lits)                                  # degree >= 1
            for t in itertools.combinations(lits, 3):        # degree <= 2
                cl.append([-l for l in t])
            e = END[c][v]
            for p, q in itertools.combinations(lits, 2):     # end -> degree <= 1
                cl.append([-e, -p, -q])
            for j in range(len(lits)):                       # not end -> degree >= 2
                cl.append([e] + lits[:j] + lits[j + 1:])
    for c in range(colors):
        enc = CardEnc.equals(lits=[END[c][v] for v in V], bound=2, vpool=pool, encoding=EncType.seqcounter)
        cl.extend(enc.clauses)
    return X, cl


def ham_paths(n, edges, k=2, seconds=120.0, vertices=None, exact_cover=False):
    """k edge-disjoint Hamiltonian paths on the vertex set (exact_cover: they partition the edge set).
    Lazy connectivity: a color class with several components gets, for each component K and every
    color, the clause 'some edge of delta(K) has this color' (a Hamiltonian path crosses every cut)."""
    V = sorted(vertices) if vertices is not None else list(range(n))
    E = canon(edges)
    Vs = set(V)
    E = [e for e in E if e[0] in Vs and e[1] in Vs]
    built = _paths_solver(V, E, k, exact_cover)
    if built is None:
        return {"status": "NOPATHS", "rounds": 0, "reason": "isolated vertex"}
    X, cl = built
    deadline = time.monotonic() + seconds
    rounds = 0
    with Solver(name=SOLVER, bootstrap_with=cl) as S:
        while True:
            ok = _solve(S, deadline)
            if ok is None:
                return {"status": "TIMEOUT", "rounds": rounds}
            if ok is False:
                return {"status": "NOPATHS", "rounds": rounds}
            rounds += 1
            pos = set(l for l in S.get_model() if l > 0)
            col = [[E[i] for i in range(len(E)) if X[c][i] in pos] for c in range(k)]
            split = False
            for c in range(k):
                comps = _components(V, col[c])
                if len(comps) == 1:
                    continue
                split = True
                for K in comps:
                    Ks = set(K)
                    cut = [i for i, (a, b) in enumerate(E) if (a in Ks) != (b in Ks)]
                    for cc in range(k):
                        S.add_clause([X[cc][i] for i in cut])
            if not split:
                ok2 = verify_paths(E, col, V, exact_cover)
                return {"status": "PATHS", "rounds": rounds, "paths": col, "verified": ok2}


def verify_paths(E, col, V, exact_cover=False):
    Es = set(E)
    used = set()
    for es in col:
        es = [tuple(e) for e in es]
        if len(es) != len(V) - 1 or len(set(es)) != len(es) or not set(es) <= Es or used & set(es):
            return False
        used |= set(es)
        deg = {v: 0 for v in V}
        for a, b in es:
            deg[a] += 1; deg[b] += 1
        if any(d not in (1, 2) for d in deg.values()) or sum(1 for d in deg.values() if d == 1) != 2:
            return False
        if len(_components(V, es)) != 1:
            return False
    if exact_cover and used != Es:
        return False
    return True


def ham_paths_ends(n, edges, ends, seconds=60.0, vertices=None):
    """len(ends) edge-disjoint Hamiltonian paths, path c with end vertices ends[c] = (a, b)."""
    V = sorted(vertices) if vertices is not None else list(range(n))
    E = canon(edges)
    Vs = set(V)
    E = [e for e in E if e[0] in Vs and e[1] in Vs]
    k = len(ends)
    built = _paths_solver(V, E, k, False)
    if built is None:
        return {"status": "NOPATHS", "rounds": 0}
    X, cl = built
    # END variables were created in order after X; recover them by rebuilding the id pool deterministically
    from pysat.formula import IDPool
    # re-derive END ids: _paths_solver uses IDPool with keys ("end", c, v)
    return _ham_paths_ends_solve(V, E, k, ends, seconds)


def _ham_paths_ends_solve(V, E, k, ends, seconds):
    from pysat.card import CardEnc, EncType
    from pysat.formula import IDPool
    m = len(E)
    pool = IDPool()
    X = [[pool.id(("x", c, i)) for i in range(m)] for c in range(k)]
    inc = {v: [] for v in V}
    for i, (a, b) in enumerate(E):
        inc[a].append(i); inc[b].append(i)
    cl = []
    for i in range(m):
        for c1 in range(k):
            for c2 in range(c1 + 1, k):
                cl.append([-X[c1][i], -X[c2][i]])
    for c in range(k):
        endset = set(ends[c])
        for v in V:
            lits = [X[c][i] for i in inc[v]]
            if v in endset:
                cl.append(lits)
                for p, q in itertools.combinations(lits, 2):
                    cl.append([-p, -q])
            else:
                cl.extend(_exactly2(lits))
    deadline = time.monotonic() + seconds
    rounds = 0
    with Solver(name=SOLVER, bootstrap_with=cl) as S:
        while True:
            ok = _solve(S, deadline)
            if ok is None:
                return {"status": "TIMEOUT", "rounds": rounds}
            if ok is False:
                return {"status": "NOPATHS", "rounds": rounds}
            rounds += 1
            pos = set(l for l in S.get_model() if l > 0)
            col = [[E[i] for i in range(m) if X[c][i] in pos] for c in range(k)]
            split = False
            for c in range(k):
                comps = _components(V, col[c])
                if len(comps) == 1:
                    continue
                split = True
                for K in comps:
                    Ks = set(K)
                    cut = [i for i, (a, b) in enumerate(E) if (a in Ks) != (b in Ks)]
                    # path c must cross delta(K) (K is a proper subset); other colors too
                    for cc in range(k):
                        S.add_clause([X[cc][i] for i in cut])
            if not split:
                return {"status": "PATHS", "rounds": rounds, "paths": col,
                        "verified": verify_paths(E, col, V)}


def min_pair_asc(n, edges, seconds=120.0, vertices=None, lb=8, step_seconds=None):
    """Ascending search: for k = lb, lb+2, ...: is there a pair with at most k vertices? The first PAIR
    answer after UNSAT answers for all smaller bounds (from lb) gives the exact minimum, provided lb is a
    valid lower bound (no pair below lb). Returns EXACT / LOWER (min >= k, time ran out) with the bound."""
    P = PairSolver(n, edges, vertices)
    t0 = time.monotonic(); deadline = t0 + seconds
    k = lb
    try:
        while True:
            dl = deadline if step_seconds is None else min(deadline, time.monotonic() + step_seconds)
            st, supp, cyc = P.solve(dl, k)
            if st == "PAIR":
                ok = verify_cycles(P.E, cyc, supp)
                return {"status": "EXACT" if ok else "BADWITNESS", "min": len(supp), "support": supp,
                        "cycles": cyc, "t": round(time.monotonic() - t0, 3), "rounds": P.rounds, "lb": lb}
            if st == "NOPAIR":
                if k >= len(P.V):
                    return {"status": "NOPAIR", "t": round(time.monotonic() - t0, 3)}
                k += 2
                continue
            return {"status": "LOWER", "lower": k, "t": round(time.monotonic() - t0, 3), "rounds": P.rounds, "lb": lb}
    finally:
        P.close()
