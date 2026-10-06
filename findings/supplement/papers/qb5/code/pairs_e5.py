"""For E5 graphs: which pairs (p, q), p, q on opposite sides, leave G - p - q with a 4-factor (lane qb5).
4-factor of a balanced bipartite graph by max flow (networkx), capacities 4 at every vertex.
Usage: pairs_e5.py < e5.g6 ; prints per graph: number of good pairs, and whether G has a 4-factor."""
import sys
import networkx as nx
from g6 import decode

def has4factor(n, adj, side, keep):
    P = [v for v in keep if side[v] == 0]
    Q = [v for v in keep if side[v] == 1]
    if len(P) != len(Q) or not P:
        return False
    F = nx.DiGraph()
    for p in P:
        F.add_edge('s', p, capacity=4)
        for q in adj[p]:
            if q in keep:
                F.add_edge(p, q, capacity=1)
    for q in Q:
        F.add_edge(q, 't', capacity=4)
    return nx.maximum_flow_value(F, 's', 't') == 4 * len(P)

def main():
    tot = 0
    for line in sys.stdin:
        line = line.strip()
        if not line:
            continue
        n, adj = decode(line)
        side = [-1] * n; side[0] = 0; st = [0]
        while st:
            v = st.pop()
            for u in adj[v]:
                if side[u] < 0:
                    side[u] = 1 - side[v]; st.append(u)
        V = set(range(n))
        g4 = has4factor(n, adj, side, V)
        good = []
        for p in range(n):
            if side[p] != 0: continue
            for q in range(n):
                if side[q] != 1: continue
                if has4factor(n, adj, side, V - {p, q}):
                    good.append((p, q))
        tot += 1
        print(line, 'G_has_4factor=%d' % g4, 'good_pairs=%d' % len(good), 'example=%s' % (good[:1],))


if __name__ == "__main__":
    main()
