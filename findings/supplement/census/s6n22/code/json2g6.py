#!/usr/bin/env python3
"""json2g6.py: B_edges (+ M) from a lane JSON host/trap file -> graph6 line, vertex order kept
(A = 0..M-1, B = M..2M-1). Usage: json2g6.py file.json [...] > out.g6"""
import json, sys

def g6(n, E):
    adj = set((min(a, b), max(a, b)) for a, b in E)
    bits = []
    for j in range(1, n):
        for i in range(j):
            bits.append(1 if (i, j) in adj else 0)
    while len(bits) % 6:
        bits.append(0)
    out = chr(63 + n)
    for k in range(0, len(bits), 6):
        v = 0
        for b in bits[k:k + 6]:
            v = 2 * v + b
        out += chr(63 + v)
    return out

for f in sys.argv[1:]:
    d = json.load(open(f))
    E = d["B_edges"] if "B_edges" in d else d["edges"]
    n = 2 * d["M"] if "M" in d else d["n"]
    print(g6(n, E))
