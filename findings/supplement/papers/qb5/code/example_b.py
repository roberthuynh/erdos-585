"""Type (b) example of NOTES 7.3 / PAPER3 (lane qb5, round 3): a 22-vertex 2-block X and a 4-set M of
cut edges that misses exactly one in-degree-3 vertex a, with a not in I_X(M).
A = T u U, T = {a=0, t2..t6 = 1..5}, U = {6..11}; C' = {c1..c6}, C'' = {c7..c10} (C'' complete to U).
Prints the block line (blockkl format), sparsity, dem(U), I_X(m) for m = {t2, t3, t4, u1}.
"""
from itertools import combinations
A = list(range(12)); a, t2, t3, t4, t5, t6 = 0, 1, 2, 3, 4, 5; U = list(range(6, 12))
T = [a, t2, t3, t4, t5, t6]
N = {}
N['c1'] = [t3, t4, t5, t6, 6, 7]
N['c2'] = [t2, t4, t5, t6, 8, 9]
N['c3'] = [t2, t3, t5, t6, 10, 11]
for c in ('c4', 'c5', 'c6'):
    N[c] = [a, t2, t3, t4, t5, t6]
for c in ('c7', 'c8', 'c9', 'c10'):
    N[c] = U[:]
masks = [sum(1 << v for v in N[c]) for c in sorted(N, key=lambda s: int(s[1:]))]
print('block line:', 12, 10, ' '.join(map(str, masks)))
din = [sum(1 for m in masks if m >> v & 1) for v in A]
print('in-block degrees', din)
# sparsity inside the block: every S with 3 <= |S| < |X| spans <= 3|S| - 6 edges
nc = len(masks); worst = -99
for s in range(1, 1 << nc):
    k = bin(s).count('1')
    gain = {v: sum(1 for j in range(nc) if s >> j & 1 and masks[j] >> v & 1) - 3 for v in A}
    # best S_A for this S_C: all v with gain > 0 (and check sizes)
    pos = [v for v in A if gain[v] > 0]
    val = sum(gain[v] for v in pos) - 3 * k
    size = k + len(pos)
    if 3 <= size < 22 and val > worst:
        worst = val
print('max over S of e(S) - 3|S| (need <= -6):', worst)
def dem(S):
    return 4 * len(S) - sum(min(4, len(set(N[c]) & set(S))) for c in N)
print('dem(U) =', dem(U), ' dem(A - a) =', dem([v for v in A if v != a]))
m = {t2: 1, t3: 1, t4: 1, 6: 1}
I = set(A)
for r in range(1, 13):
    for S in combinations(A, r):
        if dem(S) > sum(m.get(v, 0) for v in S):
            I &= set(S)
print('I_X(m) for m = {t2,t3,t4,u1}:', sorted(I), '(a = 0 excluded => type (b))')
