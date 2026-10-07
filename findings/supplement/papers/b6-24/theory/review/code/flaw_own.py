"""flaw_own.py (referee's own check of FLAW.md F1 / randfail.txt, PAPER 6.2 remark).
Reads randfail.txt (graph6, P, F, T, Z_random, U_new, Z_shortest). Checks:
  instance: bipartite with classes P, Q, |P| = |Q|, Delta <= 6, e = 3n - 4, D(P) = D(Q) = 4;
  sparsity by max-closure flows: for every edge uv and every vertex w outside {u, v},
    min over S with {u, v} in S, w not in S of g(S) = 6|S| - 2e(S) is >= 10
    (every proper violator contains an edge and misses a vertex);
  F is a 4-factor; T balanced and bad for F; Z_random and Z_shortest are directed cycles of
  D^- = D(F) - {e1, e2} using an H-arc from T_Q to P - T; bad sets of F Delta Z for both cycles,
  found by brute force over all cuts of at most 2 edges (pairs of edges + bridges + components).
Usage: python flaw_own.py randfail.txt
"""
import ast
import itertools
import sys

import networkx as nx


def parse(path):
    d = {}
    for line in open(path):
        line = line.rstrip("\n")
        if not line:
            continue
        key, _, val = line.partition(" ")
        d[key] = val
    G = nx.from_graph6_bytes(d["g6"].encode())
    return G, {k: ast.literal_eval(v) for k, v in d.items() if k != "g6"}


def min_g_flow(G, u, v, w):
    """min over S containing u, v and not w of 6|S| - 2e(S), via max-weight closure."""
    N = nx.DiGraph()
    big = 10 ** 6
    for (a, b) in G.edges():
        if w in (a, b):
            continue
        en = ("e", a, b)
        N.add_edge("s", en, capacity=2)
        N.add_edge(en, ("v", a), capacity=big)
        N.add_edge(en, ("v", b), capacity=big)
    for x in G:
        if x == w:
            continue
        N.add_edge(("v", x), "t", capacity=6)
    N.add_edge("s", ("v", u), capacity=big)
    N.add_edge("s", ("v", v), capacity=big)
    cut, (S_side, _T_side) = nx.minimum_cut(N, "s", "t")
    S = {x[1] for x in S_side if isinstance(x, tuple) and x[0] == "v"}
    eS = G.subgraph(S).number_of_edges()
    return 6 * len(S) - 2 * eS, S


def bad_sets(V, Fedges):
    """all vertex sets W (one of each complementary pair) with |cut_F(W)| <= 2"""
    H = nx.Graph(); H.add_nodes_from(V); H.add_edges_from(Fedges)
    out = set()
    comps = list(nx.connected_components(H))
    if len(comps) > 1:
        for c in comps:
            out.add(frozenset(c))
        return out
    E = list(H.edges())
    for e in E:
        H.remove_edge(*e)
        if not nx.is_connected(H):
            out.add(frozenset(next(iter(nx.connected_components(H)))))
        H.add_edge(*e)
    for e, f in itertools.combinations(E, 2):
        H.remove_edge(*e); H.remove_edge(*f)
        if not nx.is_connected(H):
            for c in nx.connected_components(H):
                out.add(frozenset(c))
        H.add_edge(*e); H.add_edge(*f)
    V = frozenset(V)
    canon = set()
    for W in out:
        canon.add(min(W, V - W, key=lambda s: sorted(s)))
    return canon


def main():
    G, d = parse(sys.argv[1])
    V = sorted(G); n = len(V)
    P = set(d["P"]); Q = set(V) - P
    deg = dict(G.degree())
    res = {}
    res["bipartite_PQ"] = all((a in P) != (b in P) for a, b in G.edges())
    res["n,e,maxdeg"] = (n, G.number_of_edges(), max(deg.values()))
    res["e=3n-4"] = G.number_of_edges() == 3 * n - 4
    res["D(P),D(Q)"] = (sum(6 - deg[v] for v in P), sum(6 - deg[v] for v in Q))
    F = {(a, b) if a in P else (b, a) for (a, b) in d["F"]}
    res["F_in_G"] = all(G.has_edge(a, b) for a, b in F)
    fdeg = {v: 0 for v in V}
    for a, b in F:
        fdeg[a] += 1; fdeg[b] += 1
    res["F_4factor"] = all(fdeg[v] == 4 for v in V)
    T = set(d["T"])
    TQ = T & Q
    cF = sum(1 for (p, q) in F if q in TQ and p not in T)
    res["T_balanced,cF(T)"] = (len(T & P) == len(TQ), cF)
    e12 = {(p, q) for (p, q) in F if (p in T) != (q in T)}

    def check_cycle(Z):
        L = len(Z); ok = True; uses_E0H = False
        for i in range(L):
            a, b = Z[i], Z[(i + 1) % L]
            if not G.has_edge(a, b):
                return False, False
            pq = (a, b) if a in P else (b, a)
            if a in P:  # must be an F-arc, not e1/e2
                ok &= pq in F and pq not in e12
            else:       # H-arc
                ok &= pq not in F
                if a in TQ and b not in T:
                    uses_E0H = True
        return ok and len(set(Z)) == L, uses_E0H
    F_bad = bad_sets(V, F)
    res["bad_sets_F"] = [sorted(W) for W in F_bad]
    for name in ("Z_random", "Z_shortest"):
        Z = d[name]
        ok, e0h = check_cycle(Z)
        F2 = set(F)
        for i in range(len(Z)):
            a, b = Z[i], Z[(i + 1) % len(Z)]
            pq = (a, b) if a in P else (b, a)
            F2 ^= {pq}
        bad2 = bad_sets(V, F2)
        new = [sorted(W) for W in bad2 if W not in F_bad]
        res[name] = {"directed_cycle_of_Dminus": ok, "uses_E0_H_arc": e0h, "len": len(Z),
                     "bad_sets_after": [sorted(W) for W in bad2], "new_bad_sets": new}
    U = frozenset(d["U_new"])
    res["U_new_or_complement_new"] = any(W in (U, frozenset(V) - U) for W in bad_sets(V, set(F) ^ {
        ((d["Z_random"][i], d["Z_random"][(i + 1) % len(d["Z_random"])]) if d["Z_random"][i] in P else
         (d["Z_random"][(i + 1) % len(d["Z_random"])], d["Z_random"][i])) for i in range(len(d["Z_random"]))}))
    # sparsity
    worst = 99
    for (u, v) in G.edges():
        for w in V:
            if w in (u, v):
                continue
            g, S = min_g_flow(G, u, v, w)
            if g < worst:
                worst = g
    res["min_g_proper_sets_with_an_edge"] = worst
    for k, v in res.items():
        print(k, ":", v)


if __name__ == "__main__":
    main()
