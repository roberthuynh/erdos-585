#!/usr/bin/env python3
"""Referee's own check of the PAPER2 §6 certificate (n = 28).  Usage: cert_check.py file.g6
Sparsity is checked separately by sparse_gray.c (all 2^28 subsets)."""
import sys
from e5lib import g6_decode, bipartition, has_4factor, decompositions, Block

line = open(sys.argv[1]).readline()
n, adj = g6_decode(line)
m = sum(len(a) for a in adj) // 2
col = bipartition(n, adj)
assert col is not None, "not bipartite"
P = {v for v in range(n) if col[v] == 0}
Q = {v for v in range(n) if col[v] == 1}
degs = [len(adj[v]) for v in range(n)]
print(f"n={n} m={m} 3n-5={3*n-5} |P|={len(P)} |Q|={len(Q)} Delta={max(degs)} delta={min(degs)}")
print("D(P) =", sum(6 - degs[v] for v in P), " D(Q) =", sum(6 - degs[v] for v in Q))
f = has_4factor(n, adj, col)
print("G has a 4-factor:", f[0], f"(max flow {f[1]} of {f[2]})")

# stated decomposition
A = set(range(0, 10)); C = set(range(10, 18)); B = set(range(18, 22)); D = set(range(22, 28))
if 0 not in P:   # orient: A on side of vertex 0
    col = [1 - x for x in col]
    P, Q = Q, P
assert A | B == P and C | D == Q, "stated sides differ from the bipartition"
blk = Block(n, adj, A, C, B, D)
print("stated decomposition has Theorem 6.1 structure:", blk.check_structure())
print("cut:", sorted(blk.cut))
print("in-block degrees A:", [blk.din[a] for a in sorted(A)], " D:", [blk.din[d] for d in sorted(D)])
print("cut degrees A:", [blk.c[a] for a in sorted(A)], " D:", [blk.c[d] for d in sorted(D)])
print("L_A =", sorted(blk.LA), " L_D =", sorted(blk.LD))
for cc in sorted(C):
    print(f"  N({cc}) = {sorted(adj[cc])}")
for b in sorted(B):
    print(f"  N({b}) = {sorted(adj[b])}")
T = {0, 1, 2, 3}
Cp = {cc for cc in C if len(adj[cc] & T) >= 3}
Cpp = C - Cp
A1 = A - T
print("C' =", sorted(Cp), " C'' =", sorted(Cpp), " T u C' complete:", all(adj[cc] >= T for cc in Cp),
      " C'' adjacent to all of A1:", all(adj[cc] >= A1 for cc in Cpp),
      " Y complete K_{4,6}:", all(adj[b] == D for b in B))
print("kappa = t - |C'| =", len(T) - len(Cp), " k = dem_X(A1) =", blk.demX(A1),
      " c(T - 0) =", sum(blk.c[a] for a in T - {0}))

# all decompositions (violations with A on side P), and the mirror side
decs = decompositions(n, adj, col)
print("number of violations (A subset P) =", len(decs), [(sorted(a), sorted(c_), sl) for a, c_, b, d, sl in decs])

# pair (0, 25)
p, q = 0, 25
Mfree = [(a, d) for (a, d) in blk.cut if a != p and d != q]
print("E - E(0) - E(25) =", Mfree, " covers L' = (L_A-0)|(L_D-25) =", sorted((blk.LA - {p}) | (blk.LD - {q})))
f = has_4factor(n, adj, col, removed=(p, q))
print("G - 0 - 25 has a 4-factor:", f[0], f"(max flow {f[1]} of {f[2]})")
D1 = D - {25}
print("witness: dem_X(A1) =", blk.demX(A1), " dem_Y(D - 25) =", blk.demY(D1), " e(A1, D1) =", blk.e_AD(A1, D1),
      " p-relevance dem + c({1,2,3}) =", blk.demX(A1) + sum(blk.c[a] for a in {1, 2, 3}))

# all pairs: flow, Theorem 2.2 criterion, covering rule, genericity
good = []
mism_crit = 0
mism_cover = []
for pp in sorted(P):
    for qq in sorted(Q):
        g = has_4factor(n, adj, col, removed=(pp, qq))[0]
        if g:
            good.append((pp, qq))
        if pp in A and qq in D:
            crit = blk.criterion(pp, qq)[0]
            if crit != g:
                mism_crit += 1
            cov = blk.covering(pp, qq)[0]
            if cov != g:
                mism_cover.append((pp, qq, cov, g))
print("good pairs:", len(good), " all in A x D:", all(a in A and d in D for a, d in good))
print("(0,22) good:", (0, 22) in good, " (4,22) good:", (4, 22) in good, " (0,25) good:", (0, 25) in good)
print("Theorem 2.2 criterion vs flow mismatches on A x D:", mism_crit)
print("covering rule vs flow mismatches:", mism_cover)
nonX = {a: blk.nongeneric_witnesses('X', a) for a in sorted(A)}
nonY = {d: blk.nongeneric_witnesses('Y', d) for d in sorted(D)}
print("non-generic in A:", {a: [(sorted(w), k) for w, k in v] for a, v in nonX.items() if v})
print("non-generic in D:", {d: [(sorted(w), k) for w, k in v] for d, v in nonY.items() if v})
