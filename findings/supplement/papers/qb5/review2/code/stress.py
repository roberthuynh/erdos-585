#!/usr/bin/env python3
"""Referee's own random stress test of Corollary 5.2 / Theorem 4.1 (independent generator).
Builds random sparse E5 instances without a 4-factor from two random 2-blocks and a random
7-edge cut, n <= 26, and checks: every big-side vertex generic, some good pair (max flow),
covering rule = flow on every A x D pair.  Usage: stress.py SEED COUNT OUTFILE [lowmatch]"""
import sys
import random
import subprocess
from itertools import combinations
from e5lib import g6_encode, bipartition, has_4factor, Block

seed, count, outfn = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
lowmatch = 'lowmatch' in sys.argv[4:]
rng = random.Random(seed)
tmp = outfn + '.tmp.g6'


def sparse_check(n, adj):
    with open(tmp, 'w') as f:
        f.write(g6_encode(n, adj) + "\n")
    out = subprocess.run(['./sparse_gray'], stdin=open(tmp), capture_output=True, text=True).stdout
    return 'NOT SPARSE' not in out and 'SPARSE' in out


def random_block(c):
    """C = 0..c-1, A = c..2c+1; returns adjacency (local) or None."""
    na = c + 2
    for _ in range(2000):
        rows = [rng.sample(range(na), 6) for _ in range(c)]
        deg = [0] * na
        for r in rows:
            for a in r:
                deg[a] += 1
        if min(deg) < 3 or max(deg) > 6:
            continue
        n = c + na
        adj = [set() for _ in range(n)]
        for i, r in enumerate(rows):
            for a in r:
                adj[i].add(c + a)
                adj[c + a].add(i)
        if sparse_check(n, adj):
            return adj, deg
    return None


def matching_number(edges):
    best = 0
    for k in range(4, 0, -1):
        for M in combinations(edges, k):
            if len({a for a, _ in M}) == k and len({d for _, d in M}) == k:
                return k
    return 0


stats = {'built': 0, 'sparse': 0, 'nongeneric': 0, 'no_good_pair': 0, 'cover_mism': 0, 'min_good': 10 ** 9}
out = open(outfn, 'w')
tries = 0
while stats['sparse'] < count and tries < 50 * count:
    tries += 1
    c = rng.randint(4, 7)
    b = rng.randint(4, 7)
    if c + b > 11:
        continue
    X = random_block(c)
    Yb = random_block(b)
    if X is None or Yb is None:
        continue
    adjX, degA = X
    adjY, degD = Yb
    # global labels: A = 0..c+1, C = c+2..2c+1, D = 2c+2..2c+b+3, B = 2c+b+4..2c+2b+3
    nA, nC, nD, nB = c + 2, c, b + 2, b
    oA, oC, oD, oB = 0, nA, nA + nC, nA + nC + nD
    n = nA + nC + nD + nB
    adj = [set() for _ in range(n)]
    for i in range(nC):
        for a in adjX[i]:
            u, v = oC + i, oA + (a - c)
            adj[u].add(v); adj[v].add(u)
    for i in range(nB):
        for d in adjY[i]:
            u, v = oB + i, oD + (d - b)
            adj[u].add(v); adj[v].add(u)
    dA = degA
    dD = degD
    lo = lambda delta: max(0, delta - 2)
    hi = lambda delta: min(3, delta)
    # random cut: 7 edges A-D with c_v in [lo, hi]
    ok = False
    for _ in range(500):
        cA = [0] * nA
        cD = [0] * nD
        edges = set()
        cand = [(a, d) for a in range(nA) for d in range(nD)]
        rng.shuffle(cand)
        if lowmatch:
            # concentrate: pick a small vertex cover (two or three vertices) first
            cover_a = rng.sample(range(nA), rng.randint(1, 2))
            cover_d = rng.sample(range(nD), 3 - len(cover_a))
            cand = [(a, d) for (a, d) in cand if a in cover_a or d in cover_d]
        for (a, d) in cand:
            if len(edges) == 7:
                break
            if cA[a] < hi(6 - dA[a]) and cD[d] < hi(6 - dD[d]):
                edges.add((a, d)); cA[a] += 1; cD[d] += 1
        if len(edges) != 7:
            continue
        if all(cA[a] >= lo(6 - dA[a]) for a in range(nA)) and all(cD[d] >= lo(6 - dD[d]) for d in range(nD)):
            ok = True
            break
    if not ok:
        continue
    for (a, d) in edges:
        u, v = oA + a, oD + d
        adj[u].add(v); adj[v].add(u)
    stats['built'] += 1
    if not sparse_check(n, adj):
        continue
    stats['sparse'] += 1
    col = bipartition(n, adj)
    if col[oA] != 0:
        col = [1 - x for x in col]
    A = set(range(oA, oA + nA)); C = set(range(oC, oC + nC)); D = set(range(oD, oD + nD)); B = set(range(oB, oB + nB))
    blk = Block(n, adj, A, C, B, D)
    assert blk.check_structure()
    assert not has_4factor(n, adj, col)[0]
    mnum = matching_number(blk.cut)
    ng = [a for a in A if blk.nongeneric_witnesses('X', a)] + [d for d in D if blk.nongeneric_witnesses('Y', d)]
    good = 0
    mism = 0
    for p in sorted(A):
        for q in sorted(D):
            g = has_4factor(n, adj, col, removed=(p, q))[0]
            good += g
            if blk.covering(p, q)[0] != g:
                mism += 1
    stats['nongeneric'] += bool(ng)
    stats['no_good_pair'] += (good == 0)
    stats['cover_mism'] += mism
    stats['min_good'] = min(stats['min_good'], good)
    out.write(f"{g6_encode(n, adj)} n={n} c={c} b={b} nu_cut={mnum} good={good} nongen={ng} mism={mism}\n")
    out.flush()
out.write(f"# STATS tries={tries} {stats}\n")
out.close()
print(stats)
