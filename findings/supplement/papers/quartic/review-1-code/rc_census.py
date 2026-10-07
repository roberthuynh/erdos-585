"""Census sanity check of QB(4): read graph6 lines (stdin), 2-color each graph (own BFS), check
bipartite, Delta <= 6, e >= 3n - 4, then decide 'has a quartic subgraph' with the own SAT encoding;
every witness is validated (degrees in {0,4}, nonempty), so a positive answer is a certificate.
Usage: genbg/geng ... | rc_census.py LABEL [first_class_size or 0 for 2-coloring]"""
import sys, json, time
from collections import deque
from rc_common import Bip, quartic_sat


def g6decode(line):
    b = line.strip().encode()
    if b.startswith(b'>>graph6<<'):
        b = b[10:]
    data = [c - 63 for c in b]
    if data[0] < 63:
        n = data[0]; p = 1
    else:
        n = (data[1] << 12) | (data[2] << 6) | data[3]; p = 4
    bitsl = []
    for x in data[p:]:
        for i in range(5, -1, -1):
            bitsl.append((x >> i) & 1)
    edges = []
    k = 0
    for j in range(1, n):
        for i in range(j):
            if bitsl[k]:
                edges.append((i, j))
            k += 1
    return n, edges


def two_color(n, edges):
    adj = [[] for _ in range(n)]
    for i, j in edges:
        adj[i].append(j); adj[j].append(i)
    col = [-1] * n
    for r in range(n):
        if col[r] >= 0:
            continue
        col[r] = 0
        dq = deque([r])
        while dq:
            v = dq.popleft()
            for w in adj[v]:
                if col[w] < 0:
                    col[w] = 1 - col[v]; dq.append(w)
                elif col[w] == col[v]:
                    return None
    return col


label = sys.argv[1]
n1 = int(sys.argv[2]) if len(sys.argv) > 2 else 0
t0 = time.time()
tot = 0; withq = 0; bad = []
for line in sys.stdin:
    if not line.strip() or line.startswith('>'):
        continue
    n, edges = g6decode(line)
    if n1 > 0:
        col = [0 if v < n1 else 1 for v in range(n)]
        assert all(col[i] != col[j] for i, j in edges)
    else:
        col = two_color(n, edges)
        assert col is not None, "not bipartite"
    U = [v for v in range(n) if col[v] == 0]
    W = [v for v in range(n) if col[v] == 1]
    rel = {v: i for i, v in enumerate(U)}
    rel.update({v: len(U) + i for i, v in enumerate(W)})
    el = []
    for i, j in edges:
        a, b = (i, j) if col[i] == 0 else (j, i)
        el.append((rel[a], rel[b]))
    G = Bip(len(U), len(W), el)
    assert len(el) >= 3 * n - 4 and max(G.deg) <= 6
    tot += 1
    F = quartic_sat(G)
    if F is None:
        bad.append(line.strip())
    else:
        withq += 1
res = {"label": label, "graphs": tot, "with_quartic_subgraph": withq, "without": len(bad),
       "counterexamples": bad[:5], "seconds": round(time.time() - t0, 1)}
print(json.dumps(res))
sys.exit(1 if bad else 0)
