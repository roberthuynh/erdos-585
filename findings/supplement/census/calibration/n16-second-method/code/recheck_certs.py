#!/usr/bin/env python3
"""Re-verify every PAIR certificate in a pairsat --certs file with brute.check_witness,
on the graph as decoded by networkx. Prints counts; exit 1 on any failure."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from brute import read_graph, check_witness
ok = bad = nopair = 0
for line in open(sys.argv[1]):
    f = line.split()
    if len(f) < 2:
        continue
    if f[1] == "NOPAIR":
        nopair += 1
        continue
    n, adj = read_graph(f[0].encode())
    c1 = [int(t) for t in f[2][3:].split(",")]
    c2 = [int(t) for t in f[3][3:].split(",")]
    if check_witness(n, adj, c1, c2):
        ok += 1
    else:
        bad += 1
        print("BAD", f[0])
print("certificates_ok=%d bad=%d nopair_lines=%d" % (ok, bad, nopair))
sys.exit(1 if bad else 0)
