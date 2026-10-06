"""deciders.py -- method B Python deciders (wave8/exb), written for this lane.

Question for each graph G: does G have a nonempty 4-regular subgraph H
(every vertex of H has degree exactly 4 in H)?

  sat_has_h4   CNF of our own, solved with PySAT (Minisat 2.2 by default).
               Variables: x_e for each edge, y_v for each vertex.
               x_e -> y_u and x_e -> y_w for e = uw;
               y_v -> at least 4 of the x_e at v: every (d-3)-subset of the
                      d edges at v has a true member (d < 4: not y_v);
               at most 4 of the x_e at v: every 5-subset has a false member;
               some y_v is true.
               A SAT answer is checked: the chosen edges are 4-regular.
  flow_has_h4  Third method, small graphs only.  H exists iff some vertex set
               S has a spanning 4-regular subgraph of G[S].  For a bipartite
               G[S] with sides P, Q that is a 4-factor, which exists iff
               |P| = |Q| and the network source->P (cap 4), P->Q along edges
               (cap 1), Q->sink (cap 4) has a flow of value 4|P|
               (integral max-flow).  S runs over the subsets of the 4-core
               that are balanced with every vertex of degree >= 4 inside S.
  brute_has_h4 Edge subsets, for tiny graphs (tests only).

graph6 is decoded and encoded by our own code (cross-checked against
networkx in selftest.py).
"""

from itertools import combinations


def parse_g6(line):
    s = line.strip()
    if s.startswith(">>graph6<<"):
        s = s[10:]
    n = ord(s[0]) - 63
    if not 0 <= n <= 62:
        raise ValueError("only n <= 62 supported")
    bits = []
    for ch in s[1:]:
        v = ord(ch) - 63
        if not 0 <= v <= 63:
            raise ValueError("bad graph6 byte")
        bits.extend((v >> (5 - i)) & 1 for i in range(6))
    need = n * (n - 1) // 2
    if len(s) - 1 != (need + 5) // 6:
        raise ValueError("bad graph6 length")
    edges = []
    k = 0
    for j in range(1, n):
        for i in range(j):
            if bits[k]:
                edges.append((i, j))
            k += 1
    return n, edges


def to_g6(n, edges):
    adj = set((min(u, w), max(u, w)) for u, w in edges)
    bits = []
    for j in range(1, n):
        for i in range(j):
            bits.append(1 if (i, j) in adj else 0)
    while len(bits) % 6:
        bits.append(0)
    out = [chr(n + 63)]
    for k in range(0, len(bits), 6):
        v = 0
        for b in bits[k:k + 6]:
            v = (v << 1) | b
        out.append(chr(v + 63))
    return "".join(out)


def incidence(n, edges):
    inc = [[] for _ in range(n)]
    for k, (u, w) in enumerate(edges):
        inc[u].append(k)
        inc[w].append(k)
    return inc


def is_4regular_subgraph(n, edges, chosen):
    """chosen: set of edge indices.  True iff nonempty and every touched
    vertex has exactly 4 chosen edges."""
    if not chosen:
        return False
    deg = [0] * n
    for k in chosen:
        u, w = edges[k]
        deg[u] += 1
        deg[w] += 1
    return all(d in (0, 4) for d in deg)


def cnf_h4(n, edges):
    m = len(edges)
    x = lambda k: k + 1          # edge variable
    y = lambda v: m + v + 1      # vertex variable
    clauses = []
    inc = incidence(n, edges)
    for k, (u, w) in enumerate(edges):
        clauses.append([-x(k), y(u)])
        clauses.append([-x(k), y(w)])
    for v in range(n):
        es = [x(k) for k in inc[v]]
        d = len(es)
        if d < 4:
            clauses.append([-y(v)])
            continue
        for sub in combinations(es, d - 3):
            clauses.append([-y(v)] + list(sub))
        for sub in combinations(es, 5):
            clauses.append([-lit for lit in sub])
    clauses.append([y(v) for v in range(n)])
    return m + n, clauses


def sat_has_h4(n, edges, solver="minisat22"):
    from pysat.solvers import Solver
    nv, clauses = cnf_h4(n, edges)
    with Solver(name=solver, bootstrap_with=clauses) as s:
        ok = s.solve()
        if not ok:
            return False, None
        model = s.get_model()
    chosen = {k for k in range(len(edges)) if model[k] > 0}
    if not is_4regular_subgraph(n, edges, chosen):
        raise RuntimeError("SAT model is not a 4-regular subgraph")
    return True, chosen


def core4(n, edges, alive):
    nb = [set() for _ in range(n)]
    for u, w in edges:
        nb[u].add(w)
        nb[w].add(u)
    alive = set(alive)
    changed = True
    while changed:
        changed = False
        for v in list(alive):
            if len(nb[v] & alive) < 4:
                alive.discard(v)
                changed = True
    return alive, nb


def bicolour(n, edges):
    nb = [[] for _ in range(n)]
    for u, w in edges:
        nb[u].append(w)
        nb[w].append(u)
    col = [-1] * n
    for s in range(n):
        if col[s] >= 0:
            continue
        col[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for w in nb[u]:
                if col[w] < 0:
                    col[w] = 1 - col[u]
                    stack.append(w)
                elif col[w] == col[u]:
                    return None
    return col


def maxflow(cap, s, t):
    """cap: dict of dicts, residual capacities (modified in place)."""
    flow = 0
    while True:
        parent = {s: None}
        queue = [s]
        for u in queue:
            if u == t:
                break
            for w, c in cap[u].items():
                if c > 0 and w not in parent:
                    parent[w] = u
                    queue.append(w)
        if t not in parent:
            return flow
        # bottleneck
        b = None
        w = t
        while parent[w] is not None:
            u = parent[w]
            b = cap[u][w] if b is None else min(b, cap[u][w])
            w = u
        w = t
        while parent[w] is not None:
            u = parent[w]
            cap[u][w] -= b
            cap[w].setdefault(u, 0)
            cap[w][u] += b
            w = u
        flow += b


def has_4factor(P, Q, nb):
    if len(P) != len(Q) or not P:
        return False
    S, T = "s", "t"
    cap = {S: {}, T: {}}
    for p in P:
        cap[S][("p", p)] = 4
        cap[("p", p)] = {}
    for q in Q:
        cap[("q", q)] = {T: 4}
    for p in P:
        for q in nb[p]:
            if q in Q:
                cap[("p", p)][("q", q)] = 1
    return maxflow(cap, S, T) == 4 * len(P)


def flow_has_h4(n, edges):
    col = bicolour(n, edges)
    if col is None:
        raise ValueError("flow_has_h4 needs a bipartite graph")
    K, nb = core4(n, edges, range(n))
    Kl = sorted(K)
    A = [v for v in Kl if col[v] == 0]
    B = [v for v in Kl if col[v] == 1]
    for k in range(4, min(len(A), len(B)) + 1):
        for P in combinations(A, k):
            Pset = set(P)
            # Q must give every p at least 4 neighbours: restrict to N(P) & B
            NB = sorted(set().union(*(nb[p] for p in P)) & set(B))
            if len(NB) < k:
                continue
            for Q in combinations(NB, k):
                Qset = set(Q)
                if any(len(nb[p] & Qset) < 4 for p in P):
                    continue
                if any(len(nb[q] & Pset) < 4 for q in Q):
                    continue
                if has_4factor(Pset, Qset, nb):
                    return True
    return False


def brute_has_h4(n, edges):
    m = len(edges)
    if m > 24:
        raise ValueError("too many edges for brute force")
    for mask in range(1, 1 << m):
        chosen = {k for k in range(m) if mask >> k & 1}
        if len(chosen) % 2:
            continue
        if is_4regular_subgraph(n, edges, chosen):
            return True
    return False
