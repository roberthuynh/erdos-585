# Cross-check (Python + networkx, separate from rv.c): sparsity, 4-factor of G, cut structure for E5 lines.
import sys, networkx as nx
def load(s):
    n = ord(s[0]) - 63; bits = []
    for ch in s[1:]:
        v = ord(ch) - 63; bits += [(v >> k) & 1 for k in range(5, -1, -1)]
    G = nx.Graph(); G.add_nodes_from(range(n)); idx = 0
    for j in range(1, n):
        for i in range(j):
            if bits[idx]: G.add_edge(i, j)
            idx += 1
    return G
def sparse(G):
    n = G.number_of_nodes(); adj = [0]*n
    for a, b in G.edges(): adj[a] |= 1 << b; adj[b] |= 1 << a
    N = 1 << n; E = bytearray(N); worst = -99
    for S in range(1, N):
        v = (S & -S).bit_length() - 1; R = S & (S - 1)
        E[S] = E[R] + bin(adj[v] & R).count("1")
    pcs = [0]*N
    for S in range(1, N): pcs[S] = pcs[S >> 1] + (S & 1)
    for S in range(1, N - 1):
        k = pcs[S]
        if k >= 3 and E[S] > 3*k - 6: return False
    return True
def f4(G, P):
    F = nx.DiGraph()
    for v in G:
        if v in P: F.add_edge('s', v, capacity=4)
        else: F.add_edge(v, 't', capacity=4)
    for a, b in G.edges():
        x, y = (a, b) if a in P else (b, a); F.add_edge(x, y, capacity=1)
    return nx.maximum_flow_value(F, 's', 't') == 4*sum(1 for v in G if v in P)
for line in open(sys.argv[1]).read().split()[:int(sys.argv[2])]:
    G = load(line); col = nx.bipartite.color(G); P = {v for v in G if col[v] == 0}
    print(G.number_of_nodes(), G.number_of_edges(), "sparse", sparse(G), "sides", len(P), G.number_of_nodes() - len(P),
          "4-factor(G)", f4(G, P) if 2*len(P) == G.number_of_nodes() else "n/a")
