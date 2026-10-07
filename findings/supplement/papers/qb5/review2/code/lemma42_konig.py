#!/usr/bin/env python3
"""Referee's second check of PAPER2 Lemma 4.2, on the genbg isomorphism classes.

Input: graph6 lines from `genbg -q -d1:1 -D3:3 na nd 7:7` (first na vertices = A, rest = D).
Decision for fixed (p, q) by the edge-cover formula (Gallai/Konig), not by search:
  F = E - E(p) - E(q), L' = (L_A - p) | (L_D - q).
  Some M subset of F with |M| = 4 covers L'  iff  |F| >= 4, every vertex of L' has an F-edge,
  and |L'| - nu(F[L']) <= 4, where nu is the maximum matching among F-edges inside L'.
Usage: lemma42_konig.py NA ND [mode]   (reads graph6 from stdin)
mode 0: p, q ends of cut edges (all vertices here are); mode 1: also p or q outside the cut.
"""
import sys
from itertools import combinations


def g6_decode(line):
    s = line.strip()
    data = [ord(ch) - 63 for ch in s]
    if data[0] == 63:
        raise ValueError("large graph6 not expected")
    n = data[0]
    bits = []
    for x in data[1:]:
        for k in range(5, -1, -1):
            bits.append((x >> k) & 1)
    edges = []
    idx = 0
    for j in range(1, n):
        for i in range(j):
            if bits[idx]:
                edges.append((i, j))
            idx += 1
    return n, edges


def max_matching(edges):
    """edges: list of (a, d); simple augmenting paths."""
    adj = {}
    for a, d in edges:
        adj.setdefault(a, []).append(d)
    match_d = {}

    def try_aug(a, seen):
        for d in adj.get(a, []):
            if d in seen:
                continue
            seen.add(d)
            if d not in match_d or try_aug(match_d[d], seen):
                match_d[d] = a
                return True
        return False

    nu = 0
    for a in adj:
        if try_aug(a, set()):
            nu += 1
    return nu


def pair_ok(E, p, q, LA, LD):
    F = [(a, d) for (a, d) in E if a != p and d != q]
    if len(F) < 4:
        return False
    LAp = LA - {p}
    LDq = LD - {q}
    for a in LAp:
        if not any(x == a for x, _ in F):
            return False
    for d in LDq:
        if not any(y == d for _, y in F):
            return False
    inner = [(a, d) for (a, d) in F if a in LAp and d in LDq]
    nu = max_matching(inner)
    return len(LAp) + len(LDq) - nu <= 4


def main():
    na, nd = int(sys.argv[1]), int(sys.argv[2])
    mode = int(sys.argv[3]) if len(sys.argv) > 3 else 0
    ngraph = nlab = nfail = 0
    for line in sys.stdin:
        if not line.strip():
            continue
        n, edges = g6_decode(line)
        assert n == na + nd
        E = []
        for (i, j) in edges:
            assert i < na <= j, "edge inside a side"
            E.append((i, j - na))
        assert len(E) == 7
        ca = [sum(1 for a, _ in E if a == i) for i in range(na)]
        cd = [sum(1 for _, d in E if d == j) for j in range(nd)]
        assert all(1 <= x <= 3 for x in ca + cd)
        ngraph += 1
        forcedA = {i for i in range(na) if ca[i] == 3}
        forcedD = {j for j in range(nd) if cd[j] == 3}
        LAs = []
        for r in range(na + 1):
            for S in combinations(range(na), r):
                S = set(S)
                if forcedA <= S and sum(3 - ca[i] for i in S) <= 5:
                    LAs.append(S)
        LDs = []
        for r in range(nd + 1):
            for S in combinations(range(nd), r):
                S = set(S)
                if forcedD <= S and sum(3 - cd[j] for j in S) <= 5:
                    LDs.append(S)
        Ps = list(range(na)) + ([None] if mode else [])
        Qs = list(range(nd)) + ([None] if mode else [])
        for LA in LAs:
            for LD in LDs:
                nlab += 1
                ok = any(pair_ok(E, p, q, LA, LD) for p in Ps for q in Qs)
                if not ok:
                    nfail += 1
                    print("FAIL", line.strip(), sorted(LA), sorted(LD))
    print(f"na={na} nd={nd} mode={mode} classes={ngraph} labellings={nlab} failures={nfail}")


if __name__ == "__main__":
    main()
