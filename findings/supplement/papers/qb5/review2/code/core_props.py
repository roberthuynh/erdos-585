#!/usr/bin/env python3
"""Referee's own check of Proposition 5.1 (a)-(d) on every actual core, and of Remark 5.4
(dem_X(A1) <= c(A1) + 1 for all A1; <= c(A1) for A1 proper when the violation is unique),
on graph6 files given as arguments.  Both blocks (X and the mirror Y) are checked."""
import sys
from itertools import combinations
from e5lib import g6_decode, bipartition, decompositions, Block

def check_block(blk, side):
    """side 'X': big = A, small = C; side 'Y': big = D, small = B (mirror)."""
    adj = blk.adj
    if side == 'X':
        big, small, L, dem = blk.A, blk.C, blk.LA, blk.demX
    else:
        big, small, L, dem = blk.D, blk.B, blk.LD, blk.demY
    cvec = blk.c
    din = blk.din
    ncores = 0
    bad = []
    # Remark 5.4
    r54_1 = r54_2 = True
    for r in range(0, len(big) + 1):
        for A1 in combinations(sorted(big), r):
            A1 = set(A1)
            d = dem(A1)
            cA1 = sum(cvec[a] for a in A1)
            if d > cA1 + 1:
                r54_1 = False
            if len(A1) < len(big) and d > cA1:
                r54_2 = False
    for p in sorted(big):
        for A1, k in blk.nongeneric_witnesses(side, p):
            ncores += 1
            T = big - A1
            Cp = {c for c in small if len(adj[c] & T) >= 3}
            Cpp = small - Cp
            t = len(T)
            kap = t - len(Cp)
            eCpA1 = sum(len(adj[c] & A1) for c in Cp)
            eCppT = sum(len(adj[c] & T) for c in Cpp)
            deltaT = sum(6 - din[a] for a in T)
            delta_p = 6 - din[p]
            cTp = sum(cvec[a] for a in T - {p})
            X = len(big) + len(small)
            conds = {
                'a_k': 1 <= k <= 3, 'a_kappa': -1 <= kap <= 2 - k,
                'a_eCpA1': eCpA1 == 8 - 4 * kap - k, 'a_A1': len(A1) == len(Cpp) + 2 - kap,
                'b_deltaT': deltaT == 2 * kap + 8 - k - eCppT, 'b_rel': eCppT + delta_p <= 2 * kap + 3,
                'b_cTp': cTp >= 5 - k, 'b_L': len(A1 & L) <= k - 1,
                'c_Cpp': len(Cpp) >= 3, 'c_eCppT': eCppT >= 3 * kap,
                'd_t': t >= 5 + kap, 'd_X': X == 2 * t + 2 * len(Cpp) + 2 - 2 * kap and X >= 18,
                'r54_core': (sum(cvec[a] for a in A1) >= k),
            }
            failed = [kk for kk, v in conds.items() if not v]
            if failed:
                bad.append((p, sorted(A1), k, failed))
    return ncores, bad, r54_1, r54_2

tot_cores = 0
tot_bad = []
r1 = r2 = True
ninst = 0
for fn in sys.argv[1:]:
    for line in open(fn):
        if not line.strip():
            continue
        n, adj = g6_decode(line)
        col = bipartition(n, adj)
        decs = decompositions(n, adj, col)
        for (A, C, B, D, sl) in decs:
            blk = Block(n, adj, A, C, B, D)
            for side in ('X', 'Y'):
                nc, bad, a1, a2 = check_block(blk, side)
                tot_cores += nc
                tot_bad += [(fn, ninst, side) + b for b in bad]
                r1 &= a1
                r2 &= a2 or len(decs) > 1
        ninst += 1
print(f"instances={ninst} cores (p, A1) found={tot_cores} failing Prop 5.1 conditions={len(tot_bad)}")
for b in tot_bad[:20]:
    print("  ", b)
print("Remark 5.4: dem <= c(A1)+1 for all A1:", r1, "; dem <= c(A1) for proper A1 (unique violation):", r2)
