"""Referee 2: builder of C1 instances (D_U = 1) that carry a sub-case cut (own code).

Layout: U = C' (0..c-1) + (U - C') (c..s-1), u1 = s-1 has degree 5; W = A (s..s+c+1) +
(W - A) (s+c+2..2s). The cut (A, C') has k = 2, D_A = 5 + eps, e(A, U - C') = 7, u1 not in C',
and e(C', W - A) = eps. Hence the slack of (A, C') in G - y is -1 for every y in W - A, so every
port in W - A is bad. Degree caps that sparsity forces anyway (r(a) <= 3 T-edges per A-vertex,
r(x) <= 3 per x in U - C', r(u1) <= 2, W-degrees >= 4) are imposed.
"""
import random
from r2common import BG, random_bip_degseq


def rand_composition(total, parts, lo, hi, rng, tries=10000):
    for _ in range(tries):
        v = [lo] * parts
        left = total - lo * parts
        if left < 0:
            return None
        idx = list(range(parts))
        while left > 0:
            j = rng.choice(idx)
            if v[j] < hi:
                v[j] += 1
                left -= 1
            elif all(v[i] >= hi for i in idx):
                break
        if left == 0:
            return v
    return None


def build(c, t, eps, rng, maxdefA=2, maxdefWA=2):
    s = c + t
    nA = c + 2
    nWA = t - 1
    # deficiencies on A (sum 5 + eps), on W - A (sum 2 - eps)
    defA = rand_composition(5 + eps, nA, 0, maxdefA, rng)
    defWA = rand_composition(2 - eps, nWA, 0, maxdefWA, rng)
    if defA is None or defWA is None:
        return None
    # T-edge counts r(a) on A (sum 7, <= 3), r(x) on U - C' (sum 7, <= 3, u1 <= 2)
    rA = rand_composition(7, nA, 0, 3, rng)
    if rA is None:
        return None
    # e(a, C') = 6 - defA - rA must be in [0, c]
    eAC = [6 - defA[i] - rA[i] for i in range(nA)]
    if any(x < 0 or x > c for x in eAC):
        return None
    rX = rand_composition(7, t, 0, 3, rng)
    if rX is None or rX[t - 1] > 2:
        return None
    # P2: A (degrees eAC) vs C' (degree 6, c* = 0 has 5 if eps = 1)
    cdeg = [6] * c
    if eps == 1:
        cdeg[0] = 5
    if sum(cdeg) != sum(eAC):
        return None
    P2 = random_bip_degseq(c, nA, cdeg, eAC, rng, tries=200)
    if P2 is None:
        return None
    # T: A (degrees rA) vs U - C' (degrees rX)
    Tg = random_bip_degseq(t, nA, rX, rA, rng, tries=200)
    if Tg is None:
        return None
    # P1: U - C' (degrees deg - rX) vs W - A (degrees 6 - defWA, minus 1 at w' if eps = 1)
    udeg1 = [6 - rX[i] for i in range(t)]
    udeg1[t - 1] = 5 - rX[t - 1]
    wdeg1 = [6 - d for d in defWA]
    wprime = None
    if eps == 1:
        # w' is a W - A vertex receiving f from c*; it needs P1-degree <= 5
        cand = [j for j in range(nWA) if wdeg1[j] >= 1]
        wprime = rng.choice(cand)
        wdeg1[wprime] -= 1
    if sum(udeg1) != sum(wdeg1):
        return None
    P1 = random_bip_degseq(t, nWA, udeg1, wdeg1, rng, tries=200)
    if P1 is None:
        return None
    edges = []
    # map: P2 local U i -> global i (C'), local W j -> global s + j (A)
    for (u, w) in P2.edges:
        edges.append((u, s + (w - c)))
    # T local U i -> global c + i, local W j -> global s + j (A)
    for (u, w) in Tg.edges:
        edges.append((c + u, s + (w - t)))
    # P1 local U i -> global c + i, local W j -> global s + nA + j
    for (u, w) in P1.edges:
        edges.append((c + u, s + nA + (w - t)))
    if eps == 1:
        edges.append((0, s + nA + wprime))
    G = BG(s, s + 1, edges)
    info = dict(c=c, t=t, eps=eps, A=list(range(s, s + nA)), Cp=list(range(c)),
                u1=s - 1, wprime=(s + nA + wprime) if eps == 1 else None)
    return G, info
