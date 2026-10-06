"""Generic vertices and the (a)-(d) rule on concrete instances (lane qb5, round 2; NOTES.md section 6).

A vertex p in A is X-generic if dem_X(A1) <= |A1 n L_A| for every p-relevant A1 in A - p with
|A1| <= |A| - 2 (relevant: dem_X(A1) > 4 - c(A - p - A1); an irrelevant witness group can be replaced by A - p)
(L_A = big-side vertices of in-block degree 3); same for q in D.  For generic p, q the pair is bad iff
(a), (b), (c) or (d) of generic_check.py holds.  For every instance this script
  - computes all bad pairs from the demand criterion (Theorem 6.1) and checks them against max flow,
  - checks that the (a)-(d) rule agrees with the truth on every generic pair,
  - reports whether some generic pair is good, and profiles (c, delta) of non-generic vertices.
Usage: generic_inst.py FILE.g6
"""
import sys
from collections import Counter
from itertools import combinations

from g6 import decode
from e5pairs import bip, structure, factor_deficit
from generic_check import bad as rule_bad


def subsets(s):
    s = list(s)
    for k in range(len(s) + 1):
        for c in combinations(s, k):
            yield frozenset(c)


def dem(small, S, adj):
    return 4 * len(S) - sum(min(4, len(adj[c] & S)) for c in small)


def main():
    fn = sys.argv[1]
    stats = Counter()
    prof = Counter()
    for line in open(fn):
        g = line.split()[0] if line.strip() else ''
        if not g:
            continue
        n, adj = decode(g)
        side = bip(n, adj)
        A, C, B, D, _ = structure(n, adj, side)
        cut = {(a, d) for a in A for d in adj[a] if d in D}
        c = {v: sum(1 for e in cut if v in e) for v in A | D}
        din = {v: len(adj[v]) - c[v] for v in A | D}
        LA = [a for a in A if din[a] == 3]
        LD = [d for d in D if din[d] == 3]
        dX = {S: dem(C, S, adj) for S in subsets(A)}
        dY = {S: dem(B, S, adj) for S in subsets(D)}
        def cA(S):
            return sum(c[a] for a in S)
        # refined: only p-relevant groups count (dem > 4 - c(A - p - A1)); others reduce to A - p
        genA = {p for p in A if all(dX[S] <= len(S & set(LA)) for S in dX
                                    if p not in S and len(S) <= len(A) - 2
                                    and dX[S] > 4 - cA(A - {p} - S))}
        genD = {q for q in D if all(dY[S] <= len(S & set(LD)) for S in dY
                                    if q not in S and len(S) <= len(D) - 2
                                    and dY[S] > 4 - cA(D - {q} - S))}
        posX = [(S, v) for S, v in dX.items() if v >= 1]
        posY = [(S, v) for S, v in dY.items() if v >= 1]
        allv = set(range(n))
        good_gen = 0
        for p in A:
            for q in D:
                badT = any(v1 + v2 - sum(1 for (a, d) in cut if a in S1 and d in S2) >= 5
                           for S1, v1 in posX if p not in S1 for S2, v2 in posY if q not in S2)
                if stats['inst'] < 60:  # flow cross-check on the first instances
                    keep = allv - {p, q}
                    val, tp, tq, _ = factor_deficit(adj, keep, side, {v: 4 for v in keep})
                    assert (val == tp) == (not badT), (g, p, q)
                r = rule_bad(p, q, cut, c, LA, LD)
                if p in genA and q in genD:
                    assert (r is not None) == badT, (g, p, q, r, badT)
                    if not badT:
                        good_gen += 1
                elif (r is None) and badT:
                    stats['rule_says_good_but_bad'] += 1
                    if stats['rule_says_good_but_bad'] <= 5:
                        print('MISMATCH (non-generic pair)', g, 'p', p, 'q', q)
                if not badT:
                    stats['good_pairs_total'] += 1
        stats['inst'] += 1
        stats['nongenericX'] += (len(genA) < len(A))
        stats['nongenericY'] += (len(genD) < len(D))
        if good_gen == 0:
            stats['no_good_generic_pair'] += 1
            print('NO GOOD GENERIC PAIR', g, 'genA', sorted(genA), 'genD', sorted(genD))
        for v in (A - genA) | (D - genD):
            prof[(c[v], 6 - din[v])] += 1
    print(dict(stats))
    print('non-generic vertex profiles (c, delta):', dict(prof))


if __name__ == '__main__':
    main()
