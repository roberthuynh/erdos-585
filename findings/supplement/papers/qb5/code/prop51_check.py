"""Assert Proposition 5.1 (a)-(d) of PAPER2.md on every relevant non-generic group of the given instances.
Usage: prop51_check.py FILE.g6 ...  (lane qb5, round 2)."""
import sys
from itertools import combinations
from g6 import decode
from e5pairs import bip, structure


def subsets(s):
    s = list(s)
    for k in range(len(s) + 1):
        for c in combinations(s, k):
            yield frozenset(c)


def main():
    groups = 0
    for fn in sys.argv[1:]:
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
            for big, small in ((A, C), (D, B)):
                L = {v for v in big if din[v] == 3}
                K = big | small
                for A1 in subsets(big):
                    if len(A1) > len(big) - 2:
                        continue
                    k = 4 * len(A1) - sum(min(4, len(adj[x] & A1)) for x in small)
                    if k <= len(A1 & L):
                        continue
                    for p in big - A1:
                        if k + sum(c[a] for a in big - {p} - A1) < 5:
                            continue
                        groups += 1
                        T = big - A1
                        Cp = {x for x in small if len(adj[x] & T) >= 3}
                        Cpp = small - Cp
                        t, kap = len(T), len(T) - len(Cp)
                        eCppT = sum(len(adj[x] & T) for x in Cpp)
                        eCpA1 = sum(len(adj[x] & A1) for x in Cp)
                        dT = sum(6 - din[x] for x in T)
                        dp = 6 - din[p]
                        assert 1 <= k <= 3 and -1 <= kap <= 2 - k, (g, p)
                        assert eCpA1 == 8 - 4 * kap - k and len(A1) == len(Cpp) + 2 - kap, (g, p)
                        assert dT == 2 * kap + 8 - k - eCppT and eCppT + dp <= 2 * kap + 3, (g, p)
                        assert sum(c[x] for x in T - {p}) >= 5 - k and len(A1 & L) <= k - 1, (g, p)
                        assert len(Cpp) >= 3 and eCppT >= 3 * kap, (g, p)
                        assert t >= 5 + kap and len(K) == 2 * t + 2 * len(Cpp) + 2 - 2 * kap >= 18, (g, p)
    print('relevant non-generic (p, A1) checked:', groups, 'all of Proposition 5.1 (a)-(d) hold')


if __name__ == '__main__':
    main()
