# Second, independent check (Python + networkx flow) of the n = 21 port-split certificate.
import sys, itertools, networkx as nx
s = open(sys.argv[1]).read().split()[0]
n = ord(s[0]) - 63; bits = []
for ch in s[1:]:
    v = ord(ch) - 63; bits += [(v >> k) & 1 for k in range(5, -1, -1)]
G = nx.Graph(); G.add_nodes_from(range(n)); idx = 0
for j in range(1, n):
    for i in range(j):
        if bits[idx]: G.add_edge(i, j)
        idx += 1
col = nx.bipartite.color(G); U = {v for v in G if col[v] == col[0]}; W = set(G) - U
if len(U) > len(W): U, W = W, U
deg = dict(G.degree()); e = G.number_of_edges()
print("n", n, "e", e, "3n-5", 3*n-5, "|U|", len(U), "|W|", len(W), "D(U)", sum(6-deg[u] for u in U), "maxdeg", max(deg.values()))
# sparsity: max over subsets of e(S) - 3|S| for 3 <= |S| <= n-1 (bitmask DP)
adj = [0]*n
for a, b in G.edges(): adj[a] |= 1 << b; adj[b] |= 1 << a
N = 1 << n; E = bytearray(N); worst = -99
for S in range(1, N):
    v = (S & -S).bit_length() - 1; R = S & (S - 1)
    E[S] = E[R] + bin(adj[v] & R).count("1")
for S in range(1, N - 1):
    k = bin(S).count("1")
    if k >= 3:
        d = E[S] - (3*k - 6)
        if d > worst: worst = d
print("sparse (max e(S)-(3|S|-6) <= 0):", worst <= 0, "worst", worst)
def has4factor(H):
    L = [v for v in H if v in W]; R = [v for v in H if v in U]
    if len(L) != len(R): return False
    F = nx.DiGraph()
    for v in L: F.add_edge('s', v, capacity=4)
    for v in R: F.add_edge(v, 't', capacity=4)
    for a, b in H.edges():
        x, y = (a, b) if a in W else (b, a)
        F.add_edge(x, y, capacity=1)
    return nx.maximum_flow_value(F, 's', 't') == 4*len(L)
T = set(range(10))
def g(S): return 6*len(S) - 2*G.subgraph(S).number_of_edges()
def kap(S): return len(S & U) - len(S & W)
print("T: g", g(T), "kappa", kap(T), "Z_U in T", all(u in T for u in U if deg[u] < 6))
for y in (14, 17):
    Q = T | {y}; A = W - Q; C = U - Q
    k = len(A) - len(C); sigma = sum(1 for a in A for c in (U - C) if G.has_edge(a, c)) - 4*k
    print("port", y, "deg", deg[y], "G-y has 4-factor:", has4factor(G.subgraph(set(G) - {y})),
          "petal T+y: g", g(Q), "kappa", kap(Q), "violation k", k, "sigma", sigma, "D(C)", sum(6-deg[c] for c in C))
Un = T | {14, 17}
print("union T+14+17: g", g(Un), "kappa", kap(Un), "; intersection = T, kappa", kap(T))
print("bad ports:", sorted(w for w in W if deg[w] < 6 and not has4factor(G.subgraph(set(G) - {w}))),
      "good ports:", sorted(w for w in W if deg[w] < 6 and has4factor(G.subgraph(set(G) - {w}))))
