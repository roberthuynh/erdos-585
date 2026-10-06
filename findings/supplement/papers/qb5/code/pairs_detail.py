"""Classify good pairs (p, q) of an E5 block pair by block membership and cut degree (lane qb5)."""
import sys
from collections import Counter
from g6 import decode
from pairs_e5 import has4factor

def blocks(n, adj, side):
    # X = complement of the violation: find A, C via the cut structure is not given; recompute by brute force
    # over sets? Instead use the min-cut: the set S of a min violation of G (exhaustive is too slow at n=24),
    # so rely on the generator's vertex order: X = 0..11, Y = rest.
    return set(range(12))

for line in sys.stdin:
    line = line.strip()
    if not line: continue
    n, adj = decode(line)
    side = [-1]*n; side[0] = 0; st = [0]
    while st:
        v = st.pop()
        for u in adj[v]:
            if side[u] < 0: side[u] = 1-side[v]; st.append(u)
    X = blocks(n, adj, side)
    cutdeg = [sum(1 for u in adj[v] if (u in X) != (v in X)) for v in range(n)]
    def lab(v):
        blk = 'X' if v in X else 'Y'
        # big side of X is A (side of vertex 5), big side of Y is D (side of vertex n-1)
        part = {('X', side[5]): 'A', ('X', 1-side[5]): 'C', ('Y', side[n-1]): 'D', ('Y', 1-side[n-1]): 'B'}[(blk, side[v])]
        return '%s(c%d,d%d)' % (part, cutdeg[v], len(adj[v]))
    V = set(range(n))
    good = Counter(); allc = Counter()
    for p in range(n):
        if side[p] != side[5]: continue
        for q in range(n):
            if side[q] == side[5]: continue
            key = (lab(p), lab(q), 'adj' if q in adj[p] else 'non')
            allc[key] += 1
            if has4factor(n, adj, side, V - {p, q}): good[key] += 1
    print(line)
    for key in sorted(allc):
        print('  ', key, 'good %d/%d' % (good[key], allc[key]))
    break
