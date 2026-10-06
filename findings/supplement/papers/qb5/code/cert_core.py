"""Readable certificate for the n = 28 core instance (lane qb5, round 2; PAPER2.md §6).

Prints the block structure, the cut, in-block degrees, the non-generic relevant group of p, the generic
rule's verdict on (p, q) and the max-flow verdict (networkx), and a demand witness (A1, D1) with
dem_X(A1) + dem_Y(D1) - e(A1, D1) >= 5.
Usage: cert_core.py FILE.g6 p q
"""
import sys
from itertools import combinations

from g6 import decode
from e5pairs import bip, structure, factor_deficit
from generic_check import bad as rule_bad


def dem(small, S, adj):
    S = set(S)
    return 4 * len(S) - sum(min(4, len(adj[c] & S)) for c in small)


def main():
    g = open(sys.argv[1]).read().split()[0]
    p, q = int(sys.argv[2]), int(sys.argv[3])
    n, adj = decode(g)
    side = bip(n, adj)
    A, C, B, D, _ = structure(n, adj, side)
    cut = sorted((a, d) for a in A for d in adj[a] if d in D)
    c = {v: sum(1 for e in cut if v in e) for v in A | D}
    din = {v: len(adj[v]) - c[v] for v in A | D}
    LA = [a for a in sorted(A) if din[a] == 3]
    LD = [d for d in sorted(D) if din[d] == 3]
    print('graph6', g, 'n', n, 'edges', sum(len(x) for x in adj) // 2)
    print('A', sorted(A), 'C', sorted(C))
    print('B', sorted(B), 'D', sorted(D))
    for x in sorted(C):
        print('  N(%d) = %s' % (x, sorted(adj[x])))
    print('cut', cut)
    print('in-block degree on A', {a: din[a] for a in sorted(A)})
    print('in-block degree on D', {d: din[d] for d in sorted(D)})
    print('cut degree', {v: c[v] for v in sorted(A | D) if c[v]})
    print('L_A', LA, 'L_D', LD)
    print('pair', (p, q), 'c_p + c_q - [p~q] =', c[p] + c[q] - (q in adj[p]),
          'generic rule says', 'bad' if rule_bad(p, q, set(cut), c, LA, LD) else 'good')
    keep = set(range(n)) - {p, q}
    val, tp, tq, _ = factor_deficit(adj, keep, side, {v: 4 for v in keep})
    print('max flow in G - p - q:', val, 'of', tp, '->', 'no 4-factor' if val < tp else '4-factor')
    best = None
    Al, Dl = sorted(A - {p}), sorted(D - {q})
    for k1 in range(len(Al) + 1):
        for A1 in combinations(Al, k1):
            d1 = dem(C, A1, adj)
            if d1 <= 0:
                continue
            for k2 in range(len(Dl) + 1):
                for D1 in combinations(Dl, k2):
                    d2 = dem(B, D1, adj)
                    if d2 <= 0:
                        continue
                    val2 = d1 + d2 - sum(1 for (a, d) in cut if a in A1 and d in D1)
                    if best is None or val2 > best[0] or (val2 == best[0] and len(A1) + len(D1) < len(best[1]) + len(best[2])):
                        best = (val2, A1, D1, d1, d2)
    v, A1, D1, d1, d2 = best
    print('witness A1 =', list(A1), 'dem_X =', d1, '|A1 n L_A| =', len(set(A1) & set(LA)),
          'c(A - p - A1) =', sum(c[a] for a in A - {p} - set(A1)))
    print('        D1 =', list(D1), 'dem_Y =', d2, 'e(A1, D1) =', d1 + d2 - v, 'total', v, '(bad iff >= 5)')


if __name__ == '__main__':
    main()
