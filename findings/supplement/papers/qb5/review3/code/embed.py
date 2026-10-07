"""Embed a block X (masks over A) into a full E5 instance with Y = K_{4,6} and given cut edges;
check sparsity of the whole graph (own S_P enumeration), E5 properties, no 4-factor, and evaluate
I_X(M), I_Y(M) for every 4-set M; report the pair statement.

usage: embed.py "nA nC masks..." "a1-d1 a2-d2 ..." [Mlist]
  cut edges as A-index - D-index (D = 0..5 of K_{4,6})
"""
import sys
from itertools import combinations
from r3lib import has_k_factor, block_demands, I_of, to_g6

blk = list(map(int, sys.argv[1].split()))
nA, nC = blk[0], blk[1]
masks = blk[2:2 + nC]
cut = [tuple(map(int, e.split('-'))) for e in sys.argv[2].split()]
assert len(cut) == 7 and len(set(cut)) == 7
nB, nD = 4, 6
# vertex numbering: A 0..nA-1, C nA..nA+nC-1, B next, D next
oA, oC, oB, oD = 0, nA, nA + nC, nA + nC + nB
n = oD + nD
adj = [set() for _ in range(n)]


def E(u, v):
    adj[u].add(v)
    adj[v].add(u)


for j, m in enumerate(masks):
    for a in range(nA):
        if m >> a & 1:
            E(oC + j, oA + a)
for b in range(nB):
    for d in range(nD):
        E(oB + b, oD + d)
for a, d in cut:
    E(oA + a, oD + d)
side = [0] * n  # 0 = P (A, B), 1 = Q (C, D)
for v in range(oC, oC + nC):
    side[v] = 1
for v in range(oD, oD + nD):
    side[v] = 1
P = [v for v in range(n) if side[v] == 0]
Q = [v for v in range(n) if side[v] == 1]
deg = [len(adj[v]) for v in range(n)]
e = sum(deg) // 2
print('n', n, 'e', e, '3n-5', 3 * n - 5, 'maxdeg', max(deg), 'mindeg', min(deg))
print('D(P)', sum(6 - deg[v] for v in P), 'D(Q)', sum(6 - deg[v] for v in Q))
# sparsity: for every S_P subset of P: best S_Q = {q : e(q,S_P) >= 4}; value sum (e-3)^+ - 3|S_P| <= -6
pidx = {v: i for i, v in enumerate(P)}
qmask = []
for q in Q:
    m = 0
    for u in adj[q]:
        m |= 1 << pidx[u]
    qmask.append(m)
full = (1 << len(P)) - 1
worst = -10 ** 9
viol = 0
for S in range(full):
    k = S.bit_count()
    if k < 4:
        continue
    val = -3 * k
    for m in qmask:
        x = (m & S).bit_count()
        if x > 3:
            val += x - 3
    if val > worst:
        worst = val
    if val > -6:
        viol += 1
okdeg = all(d >= 4 for d in deg)
print('sparse:', viol == 0 and okdeg, 'max over proper S of e(S)-3|S| (S_P != P, |S_P|>=4):', worst, 'deg>=4:', okdeg)
print('4-factor of G:', has_k_factor(n, adj, side, set()))
A = list(range(oA, oA + nA))
C = list(range(oC, oC + nC))
B = list(range(oB, oB + nB))
D = list(range(oD, oD + nD))
demX = block_demands(A, C, adj)
demY = block_demands(D, B, adj)
cutl = [(oA + a, oD + d) for a, d in cut]
LA = [a for a in A if len([c for c in adj[a] if c in set(C)]) == 3]
print('L_A', [a - oA for a in LA])
goodM = 0
for M in combinations(range(7), 4):
    mA = [0] * nA
    mD = [0] * nD
    for i in M:
        a, d = cutl[i]
        mA[a - oA] += 1
        mD[d - oD] += 1
    IX = I_of(demX, mA, nA)
    IY = I_of(demY, mD, nD)
    unc = [a - oA for a in LA if mA[a - oA] == 0]
    ends = sorted(set(cutl[i][0] - oA for i in M))
    if len(unc) == 1 and IX == 0:
        print('  M with A-ends', ends, 'misses only L-vertex', unc, 'and I_X(M) = empty  (case (b) in the full instance)')
    if IX and IY:
        goodM += 1
print('M with I_X and I_Y nonempty:', goodM, 'of 35')
good_pairs = sum(1 for p in A for q in D if has_k_factor(n, adj, side, {p, q}))
print('good pairs (flow):', good_pairs)
print('g6', to_g6(n, adj))
