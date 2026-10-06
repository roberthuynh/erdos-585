"""M-form of the pair criterion (lane qb5, round 3; NOTES.md section 7).

For a 4-set M of cut edges let m be its endpoint multiplicity on A (resp. D).  A set A1 of A is
*under-supplied* by M if m(A1) < dem_X(A1).  I_X(M) = intersection of all under-supplied A1 (A itself is
always under-supplied, and so is A - a for every A-end a of M).  Claim (Theorem 2.2 + converse of
Corollary 2.3): (p, q) is good iff p in I_X(M) and q in I_Y(M) for some M.  So the pair statement holds
iff some M has I_X(M) and I_Y(M) both nonempty: the two blocks decouple once M is fixed.

This script checks the claim against max flow and prints, per instance, the number of 4-sets M with
I_X(M) nonempty, with I_Y(M) nonempty, and with both.
Usage: mform.py FILE.g6 [limit] [flowcheck]
"""
import sys
from itertools import combinations

import numpy as np

from g6 import decode
from e5pairs import bip, structure, factor_deficit


def dem_table(small, big, adj):
    """dem(S) for every subset S of big (bitmask over the list big)."""
    nb = len(big)
    idx = {v: i for i, v in enumerate(big)}
    masks = np.arange(1 << nb, dtype=np.int64)
    pop = np.zeros(1 << nb, dtype=np.int64)
    for i in range(nb):
        pop += (masks >> i) & 1
    tot = 4 * pop
    for c in small:
        cm = 0
        for v in adj[c]:
            if v in idx:
                cm |= 1 << idx[v]
        e = np.zeros(1 << nb, dtype=np.int64)
        for i in range(nb):
            if (cm >> i) & 1:
                e += (masks >> i) & 1
        tot -= np.minimum(4, e)
    return tot, masks


def m_table(mult, nb, masks):
    out = np.zeros(1 << nb, dtype=np.int64)
    for i, w in mult.items():
        if w:
            out += w * ((masks >> i) & 1)
    return out


def analyse(n, adj, flowcheck=False):
    side = bip(n, adj)
    st = structure(n, adj, side)
    if st is None:
        return None
    A, C, B, D, defic = st
    A = sorted(A); C = sorted(C); B = sorted(B); D = sorted(D)
    ia = {v: i for i, v in enumerate(A)}; idd = {v: i for i, v in enumerate(D)}
    cut = sorted((a, d) for a in A for d in adj[a] if d in set(D))
    demX, mX = dem_table(C, A, adj)
    demY, mY = dem_table(B, D, adj)
    fullA = (1 << len(A)) - 1; fullD = (1 << len(D)) - 1
    res = []
    good = set()
    for M in combinations(range(len(cut)), 4):
        ma = {}; md = {}
        for j in M:
            a, d = cut[j]
            ma[ia[a]] = ma.get(ia[a], 0) + 1
            md[idd[d]] = md.get(idd[d], 0) + 1
        under = demX > m_table(ma, len(A), mX)
        IX = fullA
        for s in mX[under]:
            IX &= int(s)
        under = demY > m_table(md, len(D), mY)
        IY = fullD
        for s in mY[under]:
            IY &= int(s)
        PX = [A[i] for i in range(len(A)) if (IX >> i) & 1]
        PY = [D[i] for i in range(len(D)) if (IY >> i) & 1]
        res.append((M, PX, PY))
        for p in PX:
            for q in PY:
                good.add((p, q))
    if flowcheck:
        keepall = set(range(n))
        for p in range(n):
            for q in range(p + 1, n):
                if side[p] == side[q]:
                    continue
                keep = keepall - {p, q}
                val, tp, tq, _ = factor_deficit(adj, keep, side, {v: 4 for v in keep})
                isgood = (val == tp)
                pp, qq = (p, q) if p in set(A) or q in set(D) and p not in set(D) else (q, p)
                key = (p, q) if (p in set(A) and q in set(D)) else ((q, p) if (q in set(A) and p in set(D)) else None)
                if key is None:
                    assert not isgood, ('good pair outside A x D', p, q)
                else:
                    assert isgood == (key in good), ('mismatch', key, isgood)
    return dict(A=A, C=C, B=B, D=D, cut=cut, res=res, good=good)


def main():
    fn = sys.argv[1]
    limit = int(sys.argv[2]) if len(sys.argv) > 2 else 10 ** 9
    flowcheck = len(sys.argv) > 3 and sys.argv[3] == 'flowcheck'
    cnt = 0
    for line in open(fn):
        g = line.split()[0] if line.strip() else ''
        if not g:
            continue
        n, adj = decode(g)
        r = analyse(n, adj, flowcheck)
        if r is None:
            print(g, 'has a 4-factor')
            continue
        nx_ = sum(1 for _, PX, _ in r['res'] if PX)
        ny_ = sum(1 for _, _, PY in r['res'] if PY)
        nb_ = sum(1 for _, PX, PY in r['res'] if PX and PY)
        print(n, 'Mx', nx_, 'My', ny_, 'Mboth', nb_, 'good pairs', len(r['good']))
        cnt += 1
        if cnt >= limit:
            break


if __name__ == '__main__':
    main()
