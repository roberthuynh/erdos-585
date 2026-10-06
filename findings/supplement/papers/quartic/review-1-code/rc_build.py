"""Referee's own builder of C1 instances carrying a sub-case violation (written without reading
c1checks/). Pieces: P2 on C (size c) and A (size c+2), P1 on U-C (size t, contains u1) and W-A (size t-1,
contains the port y), T = 7 edges between A and U-C, and eps in {0,1} edges f between C and W-A.
Constraints chosen so that the obvious non-sparse sets are avoided: s(a) <= 3, r(x) + def(x) <= 3,
W-degrees >= 4. The cut (A, C) of G - y then has slack 2k - D_A + eps = -1 by construction."""
import random
from rc_common import Bip, gen_bip_degseq


def spread(total, k, cap, rng, floor=0):
    """random list of k ints in [floor, cap] summing to total, or None"""
    if total < k * floor or total > k * cap:
        return None
    a = [floor] * k
    r = total - k * floor
    while r > 0:
        i = rng.randrange(k)
        if a[i] < cap:
            a[i] += 1; r -= 1
    return a


def build(c, t, eps, rng, two_ports=None):
    """returns (G, info) or None. Vertex order: U = [C (c) | U-C (t), u1 last of U-C], W = [A (c+2) | W-A (t-1), y first]."""
    s = c + t
    nA, nWA = c + 2, t - 1
    defA = spread(5 + eps, nA, 2, rng)
    if defA is None:
        return None
    if eps == 1:
        defWA = [1] + [0] * (nWA - 1)
    else:
        if two_ports is None:
            two_ports = rng.random() < 0.5
        defWA = ([1, 1] if two_ports else [2, 0]) + [0] * (nWA - 2)
    sA = spread(7, nA, 3, rng)
    rU = spread(7, t, 3, rng)
    if sA is None or rU is None:
        return None
    defU = [0] * (t - 1) + [1]  # u1 is the last vertex of U - C
    if rU[-1] > 2:
        return None
    if any(rU[i] + defU[i] > 3 for i in range(t)):
        return None
    cstar = rng.randrange(c) if eps else None
    wprime = rng.randrange(nWA) if eps else None
    # P2 degree sequences
    dC = [6 - (1 if (eps and i == cstar) else 0) for i in range(c)]
    dA = [6 - defA[i] - sA[i] for i in range(nA)]
    if min(dA) < 0 or max(dA) > c:
        return None
    # P1 degree sequences
    dUC = [6 - defU[i] - rU[i] for i in range(t)]
    dWA = [6 - defWA[i] - (1 if (eps and i == wprime) else 0) for i in range(nWA)]
    if max(dUC) > nWA or min(dUC) < 0 or max(dWA) > t:
        return None
    e2 = gen_bip_degseq(dC, dA, rng)
    e1 = gen_bip_degseq(dUC, dWA, rng)
    eT = gen_bip_degseq(rU, sA, rng)  # U-C side vs A side
    if e2 is None or e1 is None or eT is None:
        return None
    # global labels: U: C -> 0..c-1, U-C -> c..s-1 ; W: A -> s..s+nA-1, W-A -> s+nA..2s
    Cg = list(range(c)); UCg = list(range(c, s))
    Ag = list(range(s, s + nA)); WAg = list(range(s + nA, 2 * s + 1))
    edges = []
    for (i, j) in e2:  # i in C side (0..c-1), j in A side (c..c+nA-1)
        edges.append((Cg[i], Ag[j - c]))
    for (i, j) in e1:  # i in U-C side (0..t-1), j in W-A side (t..)
        edges.append((UCg[i], WAg[j - t]))
    for (i, j) in eT:  # i in U-C side (0..t-1), j in A side (t..)
        edges.append((UCg[i], Ag[j - t]))
    if eps:
        edges.append((Cg[cstar], WAg[wprime]))
    if len(set(edges)) != len(edges):
        return None
    G = Bip(s, s + 1, edges)
    info = {"c": c, "t": t, "eps": eps, "A": Ag, "C": Cg, "y": WAg[0], "u1": UCg[-1],
            "two_ports": bool(eps == 0 and defWA[1] == 1)}
    return G, info
