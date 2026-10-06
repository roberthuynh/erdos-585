#!/usr/bin/python3
"""A bipartite 5-regular graph with no pair, built by the unbalanced-gadget substitution (R1).

Gadget GAMMA5 (13 vertices): bipartite with sides I (6 vertices, all of degree 5) and O (7 vertices,
degrees 5,5,5,5,4,3,3). It is 3-degenerate: K_{3,3} plus seven vertices of back-degree 3. So it has no
subgraph of minimum degree 4, hence no pair.

Skeleton L5 (8 vertices): a loopless bipartite 5-regular multigraph with no pair.

Composite: every skeleton vertex becomes a copy of GAMMA5; every skeleton edge becomes an edge between
deficient O-vertices of the two copies. Checks done here:
  1. degrees, bipartiteness, simplicity of the composite;
  2. GAMMA5 has an empty 4-core;
  3. L5 has no pair: brute force over all cycles, and the ILP;
  4. the composite has no pair: ILP (independent of the proof in PROOF-R1.md).
Usage: bip5.py [--ilp-composite]
"""
import sys
import time

from pairlib import all_cycles, degrees, find_pair_ilp, is_simple, pairs_brute

# ---- gadget: names -> indices
I_SIDE = ["a1", "a2", "a3", "x4", "x5", "x6"]
O_SIDE = ["b1", "b2", "b3", "o4", "o5", "o6", "o7"]
NAMES = I_SIDE + O_SIDE
IX = {s: i for i, s in enumerate(NAMES)}
G_EDGES = [(a, b) for a in ("a1", "a2", "a3") for b in ("b1", "b2", "b3")]
G_EDGES += [("x4", "b1"), ("x4", "b2"), ("x4", "b3")]
G_EDGES += [("a1", "o4"), ("a2", "o4"), ("x4", "o4")]
G_EDGES += [("x5", "b1"), ("x5", "b2"), ("x5", "o4")]
G_EDGES += [("a3", "o5"), ("x4", "o5"), ("x5", "o5")]
G_EDGES += [("x6", "b3"), ("x6", "o4"), ("x6", "o5")]
G_EDGES += [("a1", "o6"), ("a2", "o6"), ("x6", "o6")]
G_EDGES += [("a3", "o7"), ("x5", "o7"), ("x6", "o7")]
GAMMA = (len(NAMES), [(IX[a], IX[b]) for a, b in G_EDGES])
UNITS = ["o5", "o6", "o6", "o7", "o7"]  # the five units of deficiency

# ---- skeleton: rows x0..x3, columns y0..y3
L5 = ((0, 0, 2, 3), (0, 1, 3, 1), (2, 3, 0, 0), (3, 1, 0, 1))


def skeleton_edges(M):
    k = len(M)
    return 2 * k, [(i, k + j) for i in range(k) for j in range(k) for _ in range(M[i][j])]


def four_core(n, edges):
    alive = set(range(n))
    while True:
        deg = {v: 0 for v in alive}
        for u, v in edges:
            if u in alive and v in alive:
                deg[u] += 1
                deg[v] += 1
        low = [v for v in alive if deg[v] < 4]
        if not low:
            return alive
        alive -= set(low)


def composite(M):
    """Assign each skeleton edge to a pair of unit vertices so that the result is simple."""
    k = len(M)
    ns, sedges = skeleton_edges(M)
    gn = GAMMA[0]
    cap = {(v, name): UNITS.count(name) for v in range(ns) for name in set(UNITS)}
    used_pairs = set()
    assign = []
    names = sorted(set(UNITS))

    def rec(t):
        if t == len(sedges):
            return True
        u, w = sedges[t]
        for nu in names:
            if cap[(u, nu)] == 0:
                continue
            for nw in names:
                if cap[(w, nw)] == 0 or (u, nu, w, nw) in used_pairs:
                    continue
                cap[(u, nu)] -= 1
                cap[(w, nw)] -= 1
                used_pairs.add((u, nu, w, nw))
                assign.append((u, nu, w, nw))
                if rec(t + 1):
                    return True
                assign.pop()
                used_pairs.discard((u, nu, w, nw))
                cap[(u, nu)] += 1
                cap[(w, nw)] += 1
        return False

    assert rec(0)
    edges = [(c * gn + a, c * gn + b) for c in range(ns) for a, b in GAMMA[1]]
    edges += [(u * gn + IX[nu], w * gn + IX[nw]) for u, nu, w, nw in assign]
    return ns * gn, edges


def is_bipartite(n, edges):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    col = [-1] * n
    for s in range(n):
        if col[s] >= 0:
            continue
        col[s] = 0
        st = [s]
        while st:
            x = st.pop()
            for y in adj[x]:
                if col[y] < 0:
                    col[y] = 1 - col[x]
                    st.append(y)
                elif col[y] == col[x]:
                    return False
    return True


if __name__ == "__main__":
    gn, ge = GAMMA
    d = degrees(gn, ge)
    print("GAMMA5: n=%d e=%d I-degrees=%s O-degrees=%s simple=%s bipartite=%s 4-core size=%d" % (
        gn, len(ge), [d[IX[s]] for s in I_SIDE], [d[IX[s]] for s in O_SIDE], is_simple(ge),
        is_bipartite(gn, ge), len(four_core(gn, ge))))
    ns, se = skeleton_edges(L5)
    print("L5: n=%d e=%d degrees=%s" % (ns, len(se), sorted(set(degrees(ns, se)))))
    cyc = all_cycles(ns, se)
    print("L5: cycles=%d pairs by brute force=%d ilp=%s" % (len(cyc), len(pairs_brute(ns, se)),
                                                         find_pair_ilp(ns, se)[0]))
    n, E = composite(L5)
    print("composite: n=%d e=%d degrees=%s simple=%s bipartite=%s" % (
        n, len(E), sorted(set(degrees(n, E))), is_simple(E), is_bipartite(n, E)))
    with open("../data/bip5-avoider-104.edges", "w") as f:
        f.write("# bipartite 5-regular, 104 vertices, 260 edges, no pair; one edge per line\n")
        for u, v in sorted((min(a, b), max(a, b)) for a, b in E):
            f.write("%d %d\n" % (u, v))
    if "--ilp-composite" in sys.argv:
        t = time.time()
        st, info = find_pair_ilp(n, E, time_limit=6000, verbose=True)
        print("composite ILP:", st, info if st != "PAIR" else "", "%.0fs" % (time.time() - t))
