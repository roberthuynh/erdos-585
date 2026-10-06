#!/usr/bin/python3
"""Exact tools for "two edge-disjoint cycles on the same vertex set" (the pair).

Runs on /usr/bin/python3 (3.9) with numpy and scipy only. Graphs are (n, edges) with edges a list
of (u, v); repeated entries are parallel edges (multigraph), and an edge is identified by its index.
In a multigraph a cycle may have length 2 (two parallel edges).

Two independent exact methods:
  find_pair_ilp   integer program (HiGHS) with lazy subtour cuts; complete when it returns NONE.
  all_cycles / count_pairs_brute / find_pair_brute   plain enumeration of every cycle.
verify_pair checks a witness from first principles and is used by both.
"""
import time
from collections import defaultdict

import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp
from scipy.sparse import csr_matrix


def is_simple(edges):
    return len({(min(u, v), max(u, v)) for u, v in edges}) == len(edges) and all(u != v for u, v in edges)


def cycle_vertex_set(edges, c):
    """Vertex set of the edge-index list c if it is one simple cycle, else None."""
    if len(c) < 2 or len(set(c)) != len(c):
        return None
    adj = defaultdict(list)
    for i in c:
        u, v = edges[i]
        if u == v:
            return None
        adj[u].append(v)
        adj[v].append(u)
    if any(len(a) != 2 for a in adj.values()) or len(adj) != len(c):
        return None
    start = next(iter(adj))
    seen, stack = {start}, [start]
    while stack:
        x = stack.pop()
        for y in adj[x]:
            if y not in seen:
                seen.add(y)
                stack.append(y)
    return frozenset(adj) if len(seen) == len(adj) else None


def verify_pair(edges, c1, c2):
    a, b = cycle_vertex_set(edges, c1), cycle_vertex_set(edges, c2)
    return a is not None and a == b and not (set(c1) & set(c2))


def _components(edge_ids, edges):
    parent = {}

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    for i in edge_ids:
        for x in edges[i]:
            parent.setdefault(x, x)
    for i in edge_ids:
        a, b = find(edges[i][0]), find(edges[i][1])
        if a != b:
            parent[a] = b
    groups = defaultdict(list)
    for x in parent:
        groups[find(x)].append(x)
    return list(groups.values())


def find_pair_ilp(n, edges, min_size=None, time_limit=240, minimize=True, extra=None, verbose=False):
    """Return ("PAIR", (S, red_edge_ids, blue_edge_ids)), ("NONE", rounds) or ("UNKNOWN", msg).

    extra: optional list of (coef_dict, lb, ub) over variables ("r", e), ("b", e), ("s", v)."""
    m = len(edges)
    if min_size is None:
        min_size = 5 if is_simple(edges) else 2
    nv = 2 * m + n
    R = lambda e: e
    B = lambda e: m + e
    S = lambda v: 2 * m + v
    key = {"r": R, "b": B, "s": S}
    rows, lbs, ubs = [], [], []

    def add(coefs, lb, ub):
        rows.append(coefs)
        lbs.append(lb)
        ubs.append(ub)

    inc = [[] for _ in range(n)]
    for i, (u, v) in enumerate(edges):
        inc[u].append(i)
        inc[v].append(i)
    for v in range(n):
        d = {R(e): 1 for e in inc[v]}
        d[S(v)] = -2
        add(d, 0, 0)
        d = {B(e): 1 for e in inc[v]}
        d[S(v)] = -2
        add(d, 0, 0)
    for e in range(m):
        add({R(e): 1, B(e): 1}, -np.inf, 1)
    add({S(v): 1 for v in range(n)}, min_size, np.inf)
    for coefs, lb, ub in extra or []:
        add({key[k](i): c for (k, i), c in coefs.items()}, lb, ub)
    cost = np.zeros(nv)
    if minimize:
        cost[2 * m:] = 1
    t0 = time.time()
    rounds = 0
    while True:
        rounds += 1
        left = time_limit - (time.time() - t0)
        if left <= 0:
            return ("UNKNOWN", "time limit after %d rounds" % rounds)
        data, ri, ci = [], [], []
        for i, coefs in enumerate(rows):
            for j, val in coefs.items():
                ri.append(i)
                ci.append(j)
                data.append(val)
        A = csr_matrix((data, (ri, ci)), shape=(len(rows), nv))
        res = milp(cost, constraints=LinearConstraint(A, np.array(lbs, float), np.array(ubs, float)),
                   integrality=np.ones(nv), bounds=Bounds(0, 1), options={"time_limit": left})
        if res.status == 2:
            return ("NONE", rounds)
        if res.status != 0 or res.x is None:
            return ("UNKNOWN", "%s (round %d)" % (res.message, rounds))
        x = np.round(res.x).astype(int)
        red = [e for e in range(m) if x[R(e)]]
        blue = [e for e in range(m) if x[B(e)]]
        cr, cb = _components(red, edges), _components(blue, edges)
        if verbose:
            print("round", rounds, "S", int(x[2 * m:].sum()), "red comps", len(cr), "blue comps", len(cb), flush=True)
        if len(cr) == 1 and len(cb) == 1:
            if not verify_pair(edges, red, blue):
                return ("UNKNOWN", "solver output failed verification")
            return ("PAIR", (sorted(v for v in range(n) if x[S(v)]), red, blue))
        for comps in (cr, cb):
            if len(comps) < 2:
                continue
            for T in comps:
                Tset = set(T)
                delta = [e for e in range(m) if (edges[e][0] in Tset) != (edges[e][1] in Tset)]
                u = min(T)
                for T2 in comps:
                    if T2 is T:
                        continue
                    w = min(T2)
                    for col in (R, B):
                        d = {col(e): 1 for e in delta}
                        d[S(u)] = -2
                        d[S(w)] = -2
                        add(d, -2, np.inf)


def all_cycles(n, edges):
    """Yield (vertex frozenset, edge-id tuple) for every cycle, each exactly once."""
    adj = [[] for _ in range(n)]
    for i, (u, v) in enumerate(edges):
        if u != v:
            adj[u].append((v, i))
            adj[v].append((u, i))
    out = []
    for root in range(n):
        path_v, path_e, on = [root], [], {root}

        def dfs(head):
            for w, e in adj[head]:
                if w == root:
                    if path_e and e > path_e[0] and e != path_e[-1]:
                        out.append((frozenset(path_v), tuple(path_e + [e])))
                    continue
                if w < root or w in on:
                    continue
                on.add(w)
                path_v.append(w)
                path_e.append(e)
                dfs(w)
                path_e.pop()
                path_v.pop()
                on.discard(w)

        dfs(root)
    return out


def pairs_brute(n, edges, first_only=False):
    """All unordered pairs (c1, c2) by plain enumeration, or the first one found."""
    by_set = defaultdict(list)
    for vs, es in all_cycles(n, edges):
        by_set[vs].append(frozenset(es))
    found = []
    for vs, cyc in by_set.items():
        for i in range(len(cyc)):
            for j in range(i + 1, len(cyc)):
                if not (cyc[i] & cyc[j]):
                    if first_only:
                        return [(sorted(cyc[i]), sorted(cyc[j]))]
                    found.append((sorted(cyc[i]), sorted(cyc[j])))
    return found


# ---------- constructors ----------

def complete(n):
    return n, [(i, j) for i in range(n) for j in range(i + 1, n)]


def cycle_power(m, k):
    return m, sorted({(min(i, (i + d) % m), max(i, (i + d) % m)) for i in range(m) for d in range(1, k + 1)})


def join_two_hubs_cycle(k, hubs_adjacent=True):
    """C_k plus two hubs joined to every rim vertex (and to each other if hubs_adjacent)."""
    e = [(i, (i + 1) % k) for i in range(k)] + [(i, k) for i in range(k)] + [(i, k + 1) for i in range(k)]
    if hubs_adjacent:
        e.append((k, k + 1))
    return k + 2, [(min(a, b), max(a, b)) for a, b in e]


def regular_five_32():
    """The project's 5-regular 32-vertex avoider, as read from RegularFive.lean."""
    Bk = [(0, 3), (0, 4), (0, 5), (1, 3), (1, 4), (1, 6), (1, 7), (2, 3), (2, 5), (2, 6), (2, 7),
          (3, 6), (3, 7), (4, 5), (4, 6), (4, 7), (5, 6), (5, 7)]
    H = {(a + o, b + o) for o in (0, 8) for a, b in Bk} | {(0, 9), (0, 10), (1, 8)}
    E = {(a + o, b + o) for o in (0, 16) for a, b in H} | {(2, 18), (8, 24)}
    return 32, sorted(E)


def degrees(n, edges):
    d = [0] * n
    for u, v in edges:
        d[u] += 1
        d[v] += 1
    return d


if __name__ == "__main__":
    tests = [("K5", complete(5), True), ("K7", complete(7), True), ("octahedron", cycle_power(6, 2), True),
             ("C9^2", cycle_power(9, 2), True), ("K2vC5", join_two_hubs_cycle(5), False),
             ("P10^3", (10, [(i, j) for i in range(10) for j in range(i + 1, min(10, i + 4))]), False),
             ("regular5_32", regular_five_32(), False)]
    for name, (n, E), expect in tests:
        t = time.time()
        st, info = find_pair_ilp(n, E)
        line = "%-12s n=%d m=%d ilp=%s %.1fs" % (name, n, len(E), st, time.time() - t)
        if n <= 10:
            pb = pairs_brute(n, E)
            line += " brute_count=%d" % len(pb)
            assert (len(pb) > 0) == (st == "PAIR")
        assert (st == "PAIR") == expect, name
        print(line, flush=True)
    print("deg seq regular5_32:", sorted(set(degrees(*regular_five_32()))))


def multigraph_has_pair_underlying(n, edges):
    """Exact pair test for a loopless multigraph through its underlying simple graph.

    A pair exists iff some multiplicity is >= 4, or two cycles C1, C2 of the underlying simple graph
    (C1 = C2 allowed) have the same vertex set and every edge they share has multiplicity >= 2.
    Returns a witness description or None."""
    from collections import Counter, defaultdict
    mult = Counter((min(u, v), max(u, v)) for u, v in edges)
    for e, m in mult.items():
        if m >= 4:
            return ("digons", e)
    simple = sorted(mult)
    by_set = defaultdict(list)
    for vs, es in all_cycles(n, simple):
        by_set[vs].append(frozenset(simple[i] for i in es))
    for vs, cyc in by_set.items():
        for i in range(len(cyc)):
            for j in range(i, len(cyc)):
                if all(mult[e] >= 2 for e in cyc[i] & cyc[j]):
                    return ("cycles", sorted(vs), sorted(cyc[i]), sorted(cyc[j]))
    return None


def find_pair_flow(n, edges, min_size=None, time_limit=240):
    """Same question as find_pair_ilp, one integer program with no lazy cuts.

    Connectivity of each color class is enforced by a single-commodity flow from a free root:
    a source sends up to n units into exactly one chosen vertex, every chosen vertex absorbs one
    unit, and flow may only use edges of that color. Returns ("PAIR", ...), ("NONE", None) or
    ("UNKNOWN", msg)."""
    m = len(edges)
    if min_size is None:
        min_size = 5 if is_simple(edges) else 2
    # variables: r_e, b_e (2m) | s_v (n) | z_v (n) | fr: 2m | fb: 2m | gr_v (n) | gb_v (n)
    R0, B0, S0, Z0 = 0, m, 2 * m, 2 * m + n
    FR0 = 2 * m + 2 * n
    FB0 = FR0 + 2 * m
    GR0 = FB0 + 2 * m
    GB0 = GR0 + n
    nv = GB0 + n
    rows, lbs, ubs = [], [], []

    def add(coefs, lb, ub):
        rows.append(coefs)
        lbs.append(lb)
        ubs.append(ub)

    inc = [[] for _ in range(n)]
    for i, (u, v) in enumerate(edges):
        inc[u].append(i)
        inc[v].append(i)
    for v in range(n):
        d = {R0 + e: 1 for e in inc[v]}
        d[S0 + v] = -2
        add(d, 0, 0)
        d = {B0 + e: 1 for e in inc[v]}
        d[S0 + v] = -2
        add(d, 0, 0)
        add({Z0 + v: 1, S0 + v: -1}, -np.inf, 0)
        add({GR0 + v: 1, Z0 + v: -n}, -np.inf, 0)
        add({GB0 + v: 1, Z0 + v: -n}, -np.inf, 0)
        for F0, G0 in ((FR0, GR0), (FB0, GB0)):
            d = {G0 + v: 1, S0 + v: -1}
            for e in inc[v]:
                u, w = edges[e]
                # arc 2e is u->w, arc 2e+1 is w->u
                into, out = (2 * e + 1, 2 * e) if v == u else (2 * e, 2 * e + 1)
                d[F0 + into] = d.get(F0 + into, 0) + 1
                d[F0 + out] = d.get(F0 + out, 0) - 1
            add(d, 0, 0)
    for e in range(m):
        add({R0 + e: 1, B0 + e: 1}, -np.inf, 1)
        add({FR0 + 2 * e: 1, FR0 + 2 * e + 1: 1, R0 + e: -n}, -np.inf, 0)
        add({FB0 + 2 * e: 1, FB0 + 2 * e + 1: 1, B0 + e: -n}, -np.inf, 0)
    add({Z0 + v: 1 for v in range(n)}, 1, 1)
    add({S0 + v: 1 for v in range(n)}, min_size, np.inf)
    data, ri, ci = [], [], []
    for i, coefs in enumerate(rows):
        for j, val in coefs.items():
            ri.append(i)
            ci.append(j)
            data.append(val)
    A = csr_matrix((data, (ri, ci)), shape=(len(rows), nv))
    integrality = np.zeros(nv)
    integrality[:2 * m + 2 * n] = 1
    ub = np.full(nv, float(n))
    ub[:2 * m + 2 * n] = 1
    res = milp(np.zeros(nv), constraints=LinearConstraint(A, np.array(lbs, float), np.array(ubs, float)),
               integrality=integrality, bounds=Bounds(0, ub), options={"time_limit": time_limit})
    if res.status == 2:
        return ("NONE", None)
    if res.status != 0 or res.x is None:
        return ("UNKNOWN", res.message)
    x = np.round(res.x[:2 * m + n]).astype(int)
    red = [e for e in range(m) if x[R0 + e]]
    blue = [e for e in range(m) if x[B0 + e]]
    if not verify_pair(edges, red, blue):
        return ("UNKNOWN", "solution failed verification")
    return ("PAIR", (sorted(v for v in range(n) if x[S0 + v]), red, blue))
