#!/usr/bin/env python3
"""B-1 follow-up: 5-regular graphs on 18 vertices glued from two pair-free 9-vertex ladder blocks.

Each pair-free graph with 9 vertices, 21 edges and degrees in [3, 5] (level -1.5, total degree
deficiency 3) has one vertex of degree 3 (a1) and one of degree 4 (a2), all others degree 5 (the
census shows no (1,1,1) pattern: adding a degree-3 vertex to it would give a pair-free graph with
10 vertices and 24 edges, and there is none). Two such blocks A, B joined by a1b1, a1b2, a2b1 give a
5-regular graph on 18 vertices. A pair needs at least four edges across any cut it crosses, so the
3-edge cut keeps every pair inside A or inside B, which are pair-free.

Writes data/glue18/glue18-all.g6 (all 15 x 15 ordered block pairs) and prints a summary; the
pair tests are run separately with pairc and pair_oracle (see LOG.md).
"""
import os, sys
import networkx as nx

HERE = os.path.dirname(os.path.abspath(__file__))
src = os.path.join(HERE, "data/ladder/n9-e21-pairfree.g6")
blocks = [nx.from_graph6_bytes(l.strip().encode()) for l in open(src) if l.strip()]
assert len(blocks) == 15, len(blocks)
info = []
for G in blocks:
    deg = dict(G.degree())
    assert G.number_of_nodes() == 9 and G.number_of_edges() == 21
    d3 = [v for v in G if deg[v] == 3]
    d4 = [v for v in G if deg[v] == 4]
    assert len(d3) == 1 and len(d4) == 1 and all(deg[v] in (3, 4, 5) for v in G), sorted(deg.values())
    info.append((d3[0], d4[0]))
print("all 15 blocks have deficiency pattern (2,1): one degree-3 and one degree-4 vertex")

out_dir = os.path.join(HERE, "data/glue18")
os.makedirs(out_dir, exist_ok=True)
lines = []
for i, A in enumerate(blocks):
    for j, B in enumerate(blocks):
        H = nx.disjoint_union(A, B)  # A on 0..8, B on 9..17
        a1, a2 = info[i]
        b1, b2 = info[j][0] + 9, info[j][1] + 9
        H.add_edges_from([(a1, b1), (a1, b2), (a2, b1)])
        assert H.number_of_edges() == 45 and all(d == 5 for _, d in H.degree()), "not 5-regular"
        lines.append(nx.to_graph6_bytes(H, header=False).decode().strip())
open(os.path.join(out_dir, "glue18-all.g6"), "w").write("\n".join(lines) + "\n")
print("wrote %d glued graphs (18 vertices, 45 edges, 5-regular) to data/glue18/glue18-all.g6" % len(lines))
