#!/usr/bin/env python3
"""Check the pair-free 5-regular graphs from their edge lists alone (Python 3, no packages).

A pair is two edge-disjoint cycles on the same vertex set. For each graph the script checks the
vertex and edge counts, that the graph is simple and 5-regular, the two-coloring of the 104-vertex
graph, and the number of 4-cycles. It then certifies that there is no pair. The two cycles of a pair
form a 4-edge-connected subgraph, because each cycle crosses every cut of it at least twice, so
every pair lies inside a maximal 4-edge-connected subgraph. The script finds those subgraphs by
peeling vertices of degree below 4 and splitting along minimum cuts of size at most 3, then searches
each one exhaustively.

Usage, from this folder: python3 verify_graphs.py
"""
import itertools
import os

HERE = os.path.dirname(os.path.abspath(__file__))


def load_edges(name):
    edges = []
    with open(os.path.join(HERE, name), encoding="utf-8") as fh:
        for line in fh:
            line = line.split("#", 1)[0].split()
            if line:
                edges.append((int(line[0]), int(line[1])))
    n = max(max(e) for e in edges) + 1
    return n, edges


def adjacency(n, edges):
    adj = [set() for _ in range(n)]
    for a, b in edges:
        assert a != b, f"loop at {a}"
        assert b not in adj[a], f"repeated edge {a}-{b}"
        adj[a].add(b)
        adj[b].add(a)
    return adj


def four_cycles(n, adj):
    total = 0
    for u, v in itertools.combinations(range(n), 2):
        k = len(adj[u] & adj[v])
        total += k * (k - 1) // 2
    return total // 2


def min_cut(nodes, adj):
    """Stoer-Wagner on the subgraph induced by `nodes`: (cut size, one side)."""
    nodes = list(nodes)
    inside = set(nodes)
    w = {u: {v: 1 for v in adj[u] if v in inside} for u in nodes}
    groups = {u: {u} for u in nodes}
    best = (len(nodes) ** 2, None)
    active = nodes[:]
    while len(active) > 1:
        order = [active[0]]
        weight = {u: w[active[0]].get(u, 0) for u in active}
        while len(order) < len(active):
            u = max((x for x in active if x not in order), key=lambda x: weight[x])
            order.append(u)
            for v, c in w[u].items():
                if v in weight:
                    weight[v] += c
        s, t = order[-2], order[-1]
        cut = sum(w[t].values())
        if cut < best[0]:
            best = (cut, set(groups[t]))
        groups[s] |= groups[t]
        for v, c in w[t].items():
            if v != s:
                w[s][v] = w[s].get(v, 0) + c
                w[v][s] = w[v].get(s, 0) + c
                del w[v][t]
        w[s].pop(t, None)
        del w[t]
        active.remove(t)
    return best


def four_edge_connected_pieces(nodes, adj):
    nodes = set(nodes)
    changed = True
    while changed:
        changed = False
        for u in list(nodes):
            if len(adj[u] & nodes) < 4:
                nodes.discard(u)
                changed = True
    pieces, seen = [], set()
    for s in nodes:
        if s in seen:
            continue
        comp, stack = {s}, [s]
        seen.add(s)
        while stack:
            x = stack.pop()
            for y in adj[x] & nodes:
                if y not in seen:
                    seen.add(y)
                    comp.add(y)
                    stack.append(y)
        if len(comp) < 2:
            continue
        cut, side = min_cut(comp, adj)
        if cut >= 4:
            pieces.append(sorted(comp))
        else:
            pieces += four_edge_connected_pieces(side, adj)
            pieces += four_edge_connected_pieces(comp - side, adj)
    return pieces


def hamilton_cycles(vertices, edges):
    """Every Hamilton cycle of the graph (vertices, edges), as a set of edges, through min(vertices)."""
    vertices = sorted(vertices)
    adj = {v: set() for v in vertices}
    for a, b in edges:
        adj[a].add(b)
        adj[b].add(a)
    start, n, found = vertices[0], len(vertices), []

    def walk(path, used):
        if len(path) == n:
            if start in adj[path[-1]] and path[1] < path[-1]:
                found.append(frozenset(frozenset(e) for e in zip(path, path[1:] + [start])))
            return
        for y in adj[path[-1]]:
            if y not in used:
                used.add(y)
                path.append(y)
                walk(path, used)
                path.pop()
                used.discard(y)

    walk([start], {start})
    return found


def has_pair(piece, adj):
    for size in range(5, len(piece) + 1):
        for S in itertools.combinations(piece, size):
            Sset = set(S)
            if any(len(adj[v] & Sset) < 4 for v in S):
                continue
            E = [(a, b) for a in S for b in adj[a] & Sset if a < b]
            for c1 in hamilton_cycles(S, E):
                rest = [e for e in E if frozenset(e) not in c1]
                if hamilton_cycles(S, rest):
                    return S
    return None


def check(name, expect_n, expect_bipartite):
    n, edges = load_edges(name)
    adj = adjacency(n, edges)
    assert n == expect_n, (name, n)
    assert len(edges) == 5 * n // 2, (name, len(edges))
    assert all(len(a) == 5 for a in adj), f"{name}: not 5-regular"
    color = [None] * n
    for s in range(n):
        if color[s] is None:
            color[s], stack = 0, [s]
            while stack:
                x = stack.pop()
                for y in adj[x]:
                    if color[y] is None:
                        color[y] = 1 - color[x]
                        stack.append(y)
    bipartite = all(color[a] != color[b] for a, b in edges)
    assert bipartite == expect_bipartite, (name, bipartite)
    pieces = four_edge_connected_pieces(range(n), adj)
    pairs = [has_pair(p, adj) for p in pieces]
    assert not any(pairs), (name, pairs)
    print(f"{name}: {n} vertices, {len(edges)} edges, simple, 5-regular, "
          f"{'bipartite' if bipartite else 'not bipartite'}, {four_cycles(n, adj)} four-cycles; "
          f"4-edge-connected subgraphs of sizes {[len(p) for p in pieces]}, none with a pair: no pair")
    return color


checked = 0
for name, n, bip in [("regular-five-32.edges", 32, False), ("bipartite-five-104.edges", 104, True),
                     ("bipartite-five-104-alt.edges", 104, True)]:
    if os.path.exists(os.path.join(HERE, name)):
        check(name, n, bip)
        checked += 1
if os.path.exists(os.path.join(HERE, "bipartite-five-104-sides.txt")):
    sides = {}
    with open(os.path.join(HERE, "bipartite-five-104-sides.txt"), encoding="utf-8") as fh:
        for line in fh:
            line = line.split("#", 1)[0].split()
            if line:
                sides[int(line[0])] = int(line[1])
    _, edges104 = load_edges("bipartite-five-104.edges")
    assert len(sides) == 104 and all(sides[a] != sides[b] for a, b in edges104)
    print("bipartite-five-104-sides.txt: a proper two-coloring of the 104-vertex graph")
assert checked >= 2, "expected at least the two graph files next to this script"
print("all checks passed")
