"""Theorem 2.1 (M-form) against max flow on every P x Q pair, own code.
usage: thm21.py FILE [N]   (first N lines)
"""
import sys
from itertools import combinations
from r3lib import parse_g6, two_color, has_k_factor, decompositions, block_demands, I_of

fn = sys.argv[1]
N = int(sys.argv[2]) if len(sys.argv) > 2 else 10 ** 9
lines = [l.strip() for l in open(fn) if l.strip()][:N]
tot_pairs = 0
dis = 0
for li, s in enumerate(lines):
    n, adj = parse_g6(s)
    col = two_color(n, adj)
    decs = decompositions(n, adj)
    assert decs, 'no decomposition'
    # 4-factor of G itself must not exist
    assert not has_k_factor(n, adj, col, set())
    for dec in decs:
        A, C, B, D, cut = dec['A'], dec['C'], dec['B'], dec['D'], dec['cut']
        side = [0 if v in dec['P'] else 1 for v in range(n)]
        demX = block_demands(A, C, adj)
        demY = block_demands(D, B, adj)
        ia = {v: i for i, v in enumerate(A)}
        id_ = {v: i for i, v in enumerate(D)}
        good_pred = set()
        allgood = True
        for M in combinations(range(7), 4):
            mA = [0] * len(A)
            mD = [0] * len(D)
            for e in M:
                a, d = cut[e]
                mA[ia[a]] += 1
                mD[id_[d]] += 1
            IX = I_of(demX, mA, len(A))
            IY = I_of(demY, mD, len(D))
            if IX == 0 or IY == 0:
                allgood = False
            for i in range(len(A)):
                if IX >> i & 1:
                    for j in range(len(D)):
                        if IY >> j & 1:
                            good_pred.add((A[i], D[j]))
        ngood = 0
        for p in dec['P']:
            for q in dec['Q']:
                g = has_k_factor(n, adj, side, {p, q})
                tot_pairs += 1
                ngood += g
                if g != ((p, q) in good_pred):
                    dis += 1
                    print('DISAGREE', li, p, q, g)
        print(f'inst {li}: n={n} decs={len(decs)} |A|={len(A)} |D|={len(D)} good={ngood} pred={len(good_pred)} all35Mgood={allgood}')
print(f'file {fn}: instances={len(lines)} pairs={tot_pairs} disagreements={dis}')
