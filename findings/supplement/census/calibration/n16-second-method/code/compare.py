#!/usr/bin/env python3
"""Compare per-graph verdicts of pairsat.py (--certs file) and brute.py (output file)."""
import sys
def load(p):
    d = {}
    for line in open(p):
        f = line.split()
        if len(f) >= 2:
            d[f[0]] = f[1]
    return d
a, b = load(sys.argv[1]), load(sys.argv[2])
keys = set(a) | set(b)
mism = [k for k in keys if a.get(k) != b.get(k)]
na = sum(1 for v in a.values() if v == "NOPAIR")
nb = sum(1 for v in b.values() if v == "NOPAIR")
print("graphs_sat=%d graphs_brute=%d nopair_sat=%d nopair_brute=%d mismatches=%d" % (len(a), len(b), na, nb, len(mism)))
for k in sorted(mism)[:10]:
    print("MISMATCH", k, a.get(k), b.get(k))
sys.exit(1 if mism else 0)
