#!/usr/bin/env python3
"""Referee's own re-check of PAPER2 §7 data, one graph6 file at a time.
Usage: data_check.py FILE.g6 OUTFILE [allpairs] [crit_first=N]
Per instance: E5 numbers, sparsity (sparse_gray), all violations / decompositions, genericity of
every big-side vertex in every decomposition, good pairs by max flow (all P x Q pairs if
`allpairs`, else A x D only), the covering rule against flow, and Theorem 2.2's criterion against
flow on the first N instances.  Writes one line per instance to OUTFILE as it goes."""
import sys
import subprocess
from e5lib import g6_decode, bipartition, has_4factor, decompositions, Block

fn, outfn = sys.argv[1], sys.argv[2]
allpairs = 'allpairs' in sys.argv[3:]
crit_first = 0
for a in sys.argv[3:]:
    if a.startswith('crit_first='):
        crit_first = int(a.split('=')[1])

out = open(outfn, 'w')
lines = [l.strip() for l in open(fn) if l.strip()]
for idx, line in enumerate(lines):
    n, adj = g6_decode(line)
    col = bipartition(n, adj)
    assert col is not None
    P = [v for v in range(n) if col[v] == 0]
    Q = [v for v in range(n) if col[v] == 1]
    degs = [len(adj[v]) for v in range(n)]
    m = sum(degs) // 2
    e5 = (len(P) == len(Q) and max(degs) <= 6 and m == 3 * n - 5
          and sum(6 - degs[v] for v in P) == 5 and sum(6 - degs[v] for v in Q) == 5)
    with open(outfn + '.tmp.g6', 'w') as f:
        f.write(line + "\n")
    sp = subprocess.run(['./sparse_gray'], stdin=open(outfn + '.tmp.g6'), capture_output=True, text=True).stdout
    sparse = 'NOT SPARSE' not in sp and 'SPARSE' in sp
    f4 = has_4factor(n, adj, col)[0]
    decs = decompositions(n, adj, col)
    # mirror orientation: violations with the big side in Q
    colm = [1 - x for x in col]
    decs_m = decompositions(n, adj, colm)
    rec = {'i': idx, 'n': n, 'e5': e5, 'sparse': sparse, 'f4': f4, 'ndec': len(decs), 'ndec_mirror': len(decs_m)}
    nongen_all = []
    struct_ok = True
    blocks = []
    for (A, C, B, D, sl) in decs:
        blk = Block(n, adj, A, C, B, D)
        struct_ok &= blk.check_structure() and sl == -1
        ngX = sorted(a for a in A if blk.nongeneric_witnesses('X', a))
        ngY = sorted(d for d in D if blk.nongeneric_witnesses('Y', d))
        nongen_all.append((ngX, ngY))
        blocks.append((blk, set(ngX), set(ngY)))
    rec['struct_ok'] = struct_ok
    rec['nongen'] = nongen_all
    # pairs, relative to the first decomposition (good pairs do not depend on it)
    blk, ngX, ngY = blocks[0]
    good = 0
    good_outside_AD = 0
    cover_mism = []
    crit_mism = 0
    pairs = [(p, q) for p in P for q in Q] if allpairs else [(p, q) for p in sorted(blk.A) for q in sorted(blk.D)]
    for (p, q) in pairs:
        g = has_4factor(n, adj, col, removed=(p, q))[0]
        good += g
        inAD = p in blk.A and q in blk.D
        if g and not inAD:
            good_outside_AD += 1
        if inAD:
            # covering rule vs flow, in every decomposition
            for (bk, nx, ny) in blocks:
                if p in bk.A and q in bk.D:
                    cv = bk.covering(p, q)[0]
                    if cv != g:
                        cover_mism.append((p, q, cv, g, p in nx, q in ny))
            if idx < crit_first:
                cr = blk.criterion(p, q)[0]
                crit_mism += (cr != g)
    rec['good'] = good
    rec['good_outside_AD'] = good_outside_AD if allpairs else None
    rec['cover_mism'] = cover_mism
    rec['crit_checked'] = idx < crit_first
    rec['crit_mism'] = crit_mism
    out.write(repr(rec) + "\n")
    out.flush()
out.close()
