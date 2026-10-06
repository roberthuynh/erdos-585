"""Shared utilities for the R1 review. Written from scratch; imports nothing from tools/.

Conventions: a simple graph is given as (n, edges) with edges a list of (u, v), u != v.
A multigraph is a dict {(u, v): multiplicity} with u < v.
"""
import itertools
import os
from collections import defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
EDGES_104 = os.path.join(ROOT, "data", "bip5-avoider-104.edges")


def load_edges(path):
    edges = []
    for line in open(path):
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        a, b = line.split()
        edges.append((int(a), int(b)))
    return edges


def adjacency(n, edges):
    adj = [[] for _ in range(n)]
    for i, (u, v) in enumerate(edges):
        adj[u].append((v, i))
        adj[v].append((u, i))
    return adj


def simple_cycles_undirected(n, edges):
    """Yield every simple cycle (length >= 3) of a simple graph exactly once,
    as a tuple of edge indices. Canonical form: start at the minimum vertex s,
    only visit vertices > s, and keep the direction whose second vertex is smaller
    than the last vertex."""
    adj = adjacency(n, edges)
    for s in range(n):
        path = [s]
        epath = []
        onpath = [False] * n
        onpath[s] = True

        def dfs(v):
            for (w, ei) in adj[v]:
                if w == s and len(path) >= 3:
                    if path[1] < path[-1]:
                        yield tuple(epath + [ei])
                elif w > s and not onpath[w]:
                    onpath[w] = True
                    path.append(w)
                    epath.append(ei)
                    yield from dfs(w)
                    path.pop()
                    epath.pop()
                    onpath[w] = False

        yield from dfs(s)


def brute_force_pair(n, edges):
    """Exact pair finder for small simple graphs: enumerate all cycles, group by
    vertex set, look for two edge-disjoint cycles in one group.
    Returns (cycle1_edge_indices, cycle2_edge_indices) or None."""
    groups = defaultdict(list)
    for cyc in simple_cycles_undirected(n, edges):
        vm = 0
        em = 0
        for ei in cyc:
            u, v = edges[ei]
            vm |= (1 << u) | (1 << v)
            em |= 1 << ei
        groups[vm].append((em, cyc))
    for vm, lst in groups.items():
        for i in range(len(lst)):
            for j in range(i + 1, len(lst)):
                if lst[i][0] & lst[j][0] == 0:
                    return lst[i][1], lst[j][1]
    return None


def is_single_cycle(edge_list):
    """edge_list: list of (u, v) pairs (may contain parallel pairs, treated as
    distinct edges). True iff it is nonempty, connected and 2-regular."""
    if not edge_list:
        return False
    deg = defaultdict(int)
    nb = defaultdict(list)
    for (u, v) in edge_list:
        if u == v:
            return False
        deg[u] += 1
        deg[v] += 1
        nb[u].append(v)
        nb[v].append(u)
    if any(d != 2 for d in deg.values()):
        return False
    start = next(iter(deg))
    seen = {start}
    stack = [start]
    while stack:
        x = stack.pop()
        for y in nb[x]:
            if y not in seen:
                seen.add(y)
                stack.append(y)
    return len(seen) == len(deg)


def cycle_order(edge_list):
    """Vertex sequence of a single cycle given as a list of (u, v) edges."""
    nb = defaultdict(list)
    for (u, v) in edge_list:
        nb[u].append(v)
        nb[v].append(u)
    start = min(nb)
    order = [start]
    prev, cur = None, start
    while True:
        a, b = nb[cur]
        nxt = a if a != prev else b
        if nxt == start:
            break
        order.append(nxt)
        prev, cur = cur, nxt
    return order


def verify_pair(n, edges, red, blue):
    """red, blue: iterables of edge indices into `edges`. Independent check that
    (red, blue) is a pair. Returns (ok, message)."""
    red = list(red)
    blue = list(blue)
    eset = set()
    for (u, v) in edges:
        eset.add((min(u, v), max(u, v)))
    if len(set(red)) != len(red) or len(set(blue)) != len(blue):
        return False, "repeated edge inside one colour"
    if set(red) & set(blue):
        return False, "colours share an edge"
    re = [edges[i] for i in red]
    be = [edges[i] for i in blue]
    for (u, v) in re + be:
        if (min(u, v), max(u, v)) not in eset:
            return False, "edge not in graph"
    if not is_single_cycle(re):
        return False, "red is not a single cycle"
    if not is_single_cycle(be):
        return False, "blue is not a single cycle"
    vr = set(x for e in re for x in e)
    vb = set(x for e in be for x in e)
    if vr != vb:
        return False, "vertex sets differ"
    return True, "pair on %d vertices" % len(vr)


# ---------------------------------------------------------------- multigraphs

def multigraph_cycles(mult, nverts):
    """All cycles of a loopless multigraph given as {(u,v): m}. Returns a list of
    (vertex frozenset, tuple of (pair, copy_index)) for every cycle, counting
    2-cycles and every lift of every simple cycle of the underlying graph."""
    pairs = sorted(mult)
    out = []
    # 2-cycles
    for p in pairs:
        m = mult[p]
        for a, b in itertools.combinations(range(m), 2):
            out.append((frozenset(p), ((p, a), (p, b))))
    # longer cycles: lifts of simple cycles
    und = [p for p in pairs]
    for cyc in simple_cycles_undirected(nverts, und):
        ps = [und[i] for i in cyc]
        vs = frozenset(x for p in ps for x in p)
        for choice in itertools.product(*[range(mult[p]) for p in ps]):
            out.append((vs, tuple(zip(ps, choice))))
    return out


def multigraph_pair(mult, nverts):
    """Exact pair test for a small loopless multigraph by plain enumeration of all
    its cycles. Returns (c1, c2) or None, and the cycle count."""
    cycles = multigraph_cycles(mult, nverts)
    groups = defaultdict(list)
    for vs, es in cycles:
        groups[vs].append(frozenset(es))
    for vs, lst in groups.items():
        for i in range(len(lst)):
            for j in range(i + 1, len(lst)):
                if not (lst[i] & lst[j]):
                    return (sorted(lst[i]), sorted(lst[j])), len(cycles)
    return None, len(cycles)
