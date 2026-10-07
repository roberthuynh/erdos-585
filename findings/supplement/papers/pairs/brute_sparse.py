# brute-force sparsity check: min over S with 2 <= |S| <= n-1 of g(S) = 6|S| - 2 e(S)
import sys, networkx as nx
def ming(G):
    n = G.number_of_nodes(); nodes = list(G.nodes()); idx = {v:i for i,v in enumerate(nodes)}
    adj = [0]*n
    for u,v in G.edges(): adj[idx[u]] |= 1<<idx[v]; adj[idx[v]] |= 1<<idx[u]
    best = 10**9
    # Gray code over all subsets, track size and e(S)
    S = 0; e = 0; size = 0
    for i in range(1, 1<<n):
        b = (i & -i).bit_length()-1
        if S >> b & 1:
            S &= ~(1<<b); size -= 1; e -= bin(adj[b] & S).count('1')
        else:
            e += bin(adj[b] & S).count('1'); S |= 1<<b; size += 1
        if 2 <= size <= n-1:
            g = 6*size - 2*e
            if g < best: best = g
    return best
bad = 0; tot = 0
for line in sys.stdin:
    line=line.strip()
    if not line: continue
    G = nx.from_graph6_bytes(line.encode())
    m = ming(G); tot += 1
    print(line, m)
