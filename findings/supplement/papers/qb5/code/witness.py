"""Demand witnesses for bad pairs (lane qb5, round 2; NOTES.md section 6).

For an E5 block pair given with the pairsearch.c vertex layout (C = 0..nc-1, A next nc+2, B next nb,
D next nb+2) or found by min cut, compute dem_X, dem_Y and, for a pair (p, q), the maximum of
dem_X(A1) + dem_Y(D1) - e(A1, D1) over A1 in A - p, D1 in D - q (bad iff >= 5, Theorem 6.1),
and cross-check against max flow.
Usage: witness.py FILE [nc nb]   (lines: graph6 [anything]); prints per line the witnesses of bad
c = 0 pairs and of every bad pair if -all is given.
"""
import sys
from itertools import combinations

from g6 import decode
from e5pairs import bip, structure, factor_deficit


def dem(small, big_subset, adj):
    s = set(big_subset)
    return 4 * len(s) - sum(min(4, len(adj[c] & s)) for c in small)


def analyse(line, show_all=False):
    n, adj = decode(line.split()[0])
    side = bip(n, adj)
    A, C, B, D, _ = structure(n, adj, side)
    cut = [(a, d) for a in A for d in adj[a] if d in D]
    cdeg = {v: sum(1 for e in cut if v in e) for v in A | D}
    dIn = {v: len(adj[v]) - cdeg[v] for v in A | D}
    A_l, D_l = sorted(A), sorted(D)
    demX = {}
    for k in range(len(A_l) + 1):
        for S in combinations(A_l, k):
            demX[frozenset(S)] = dem(C, S, adj)
    demY = {}
    for k in range(len(D_l) + 1):
        for S in combinations(D_l, k):
            demY[frozenset(S)] = dem(B, S, adj)
    out = []
    allv = set(range(n))
    for p in A_l:
        for q in D_l:
            best, wit = -99, None
            for S1, d1 in demX.items():
                if p in S1 or d1 <= 0:
                    continue
                for S2, d2 in demY.items():
                    if q in S2 or d2 <= 0:
                        continue
                    val = d1 + d2 - sum(1 for (a, d) in cut if a in S1 and d in S2)
                    if val > best:
                        best, wit = val, (S1, S2, d1, d2)
            keep = allv - {p, q}
            val, tp, tq, _ = factor_deficit(adj, keep, side, {v: 4 for v in keep})
            good = (val == tp)
            assert good == (best < 5), (line, p, q, best, good)
            if not good and (show_all or (cdeg[p] == 0 and cdeg[q] == 0)):
                S1, S2, d1, d2 = wit
                out.append('p=%d(c%d,d%d) q=%d(c%d,d%d) A1=%s dem %d  D1=%s dem %d  e=%d' % (
                    p, cdeg[p], dIn[p], q, cdeg[q], dIn[q], sorted(S1), d1, sorted(S2), d2,
                    sum(1 for (a, d) in cut if a in S1 and d in S2)))
    return A, C, B, D, cut, cdeg, dIn, out


def main():
    fn = sys.argv[1]
    show_all = '-all' in sys.argv
    seen = set()
    for line in open(fn):
        g = line.split()[0] if line.strip() else ''
        if not g or g in seen:
            continue
        seen.add(g)
        A, C, B, D, cut, cdeg, dIn, out = analyse(g, show_all)
        print(g)
        print('  A', sorted(A), 'C', sorted(C), 'B', sorted(B), 'D', sorted(D))
        print('  cut', sorted(cut))
        print('  A in-deg', {a: dIn[a] for a in sorted(A)}, 'D in-deg', {d: dIn[d] for d in sorted(D)})
        for o in out:
            print('   ', o)


if __name__ == '__main__':
    main()
