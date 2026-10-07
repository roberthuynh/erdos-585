#!/usr/bin/env python3
"""Coverage check of the genbg F[B] class list (independent of genbg): random walk by degree-preserving
interchanges (Ryser: connected on matrices with fixed margins) over labelled 0/1 b x b matrices with row
and column sums (3, 4, ..., 4); every sample must be class-preserving isomorphic to one representative.
Also checks the representatives are pairwise non-isomorphic. Usage: fb_cover.py <b> <samples> <seed>"""
import os
import random
import sys

import networkx as nx
from networkx.algorithms.isomorphism import GraphMatcher

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import run_shape  # noqa: E402


def to_graph(b, pairs):
    G = nx.Graph()
    for k in range(b):
        G.add_node(('P', k), c='P')
    for j in range(b):
        G.add_node(('Q', j), c='Q')
    G.add_edges_from((('P', k), ('Q', j)) for (k, j) in pairs)
    return G


def key(G):
    return nx.weisfeiler_lehman_graph_hash(G, node_attr='c', iterations=4)


def iso(G, H):
    return GraphMatcher(G, H, node_match=lambda a, b: a['c'] == b['c']).is_isomorphic()


def main():
    b, nsamp, seed = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    rng = random.Random(seed)
    reps = run_shape.load_fb(b)
    buckets = {}
    for idx, pr in enumerate(reps):
        G = to_graph(b, pr)
        buckets.setdefault(key(G), []).append((idx, G))
    dup = 0
    for kk, lst in buckets.items():
        for i in range(len(lst)):
            for j in range(i + 1, len(lst)):
                if iso(lst[i][1], lst[j][1]):
                    dup += 1
    cur = set(reps[0])
    hit = set()
    missing = 0
    for t in range(nsamp):
        for _ in range(30):  # interchanges between samples
            (a1, b1), (a2, b2) = rng.sample(sorted(cur), 2)
            if a1 != a2 and b1 != b2 and (a1, b2) not in cur and (a2, b1) not in cur:
                cur -= {(a1, b1), (a2, b2)}
                cur |= {(a1, b2), (a2, b1)}
        G = to_graph(b, cur)
        found = None
        for idx, H in buckets.get(key(G), []):
            if iso(G, H):
                found = idx
                break
        if found is None:
            missing += 1
        else:
            hit.add(found)
    print('b=%d representatives=%d pairwise-isomorphic pairs=%d samples=%d not covered=%d classes hit=%d' % (
        b, len(reps), dup, nsamp, missing, len(hit)))


if __name__ == '__main__':
    main()
