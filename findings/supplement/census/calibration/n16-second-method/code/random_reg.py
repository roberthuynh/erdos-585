#!/usr/bin/env python3
"""Positive controls: random 5-regular graphs (networkx, seeds 1..k) written as graph6 to a file.
Usage: random_reg.py <n> <k> <out.g6>"""
import sys
import networkx as nx
n, k, out = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
with open(out, "wb") as f:
    for seed in range(1, k + 1):
        G = nx.random_regular_graph(5, n, seed=seed)
        f.write(nx.to_graph6_bytes(G, header=False))
