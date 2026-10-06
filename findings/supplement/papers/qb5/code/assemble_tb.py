"""Assemble probe instances: 2-block T + block B + a cut graph (lane qb5).

Usage: python assemble_tb.py TU TW BU BW < cuts.g6 > out.g6
T = K_{TW,TU} (T_W saturated when TU = 6), B = K_{BU,BW} (B_U saturated when BW = 6).
Each cut graph (genbg output) has class 1 = TU vertices, class 2 = BW vertices.
Vertex order of the output: T_U, T_W, B_U, B_W.
"""
import sys
from g6 import decode, encode

TU, TW, BU, BW = (int(x) for x in sys.argv[1:5])
tu = list(range(TU))
tw = list(range(TU, TU + TW))
bu = list(range(TU + TW, TU + TW + BU))
bw = list(range(TU + TW + BU, TU + TW + BU + BW))
N = TU + TW + BU + BW
base = [(a, b) for a in tu for b in tw] + [(a, b) for a in bu for b in bw]
for line in sys.stdin:
    line = line.strip()
    if not line:
        continue
    n, adj = decode(line)
    assert n == TU + BW
    cut = [(tu[i], bw[j - TU]) for i in range(TU) for j in adj[i] if j >= TU]
    print(encode(N, base + cut))
