"""Permissive core model (lane qb5, round 2; NOTES.md section 6, PAPER2.md section 7).

Question: if every admissible core is present at once, is there still a pair (p, q) of generic vertices and
4 cut edges avoiding p, q that cover (L_A - p) u (L_D - q)?  If yes for every configuration, the E5 pair
statement would follow in general.
Model of one side (A; D is symmetric).  A = Ends u I, |I| = i interior vertices (c = 0, not in L).
A core is (T, k), T = T_E u T_I with T_E in Ends, k in {1, 2, 3}, satisfying the proved necessary conditions
(Proposition 5.1): |L - T| <= k - 1; 3|L n T| + c(T_E - L) <= 12 - 3k; |T| >= 4; |A - T| >= 4; |A| >= 10.
A vertex p in T is non-generic for (T, k) if c(T - p) >= 5 - k (and, for k = 3, delta_p <= 1, i.e. p not
in L and c_p <= 1).  Every vertex that is non-generic for some admissible core is forbidden.
Usage: core_model.py   (prints, for each (i_A, i_D), the number of configurations with no allowed pair)
"""
import sys
from itertools import combinations

from generic_check import GENBG, decode, subsets, covers
import subprocess

MINIMAL = len(sys.argv) > 1 and sys.argv[1] == 'minimal'


def core_list(ends, c, L, minimal):
    """Admissible cores restricted to Ends, refined: kappa in {-1, 0, 1}, kappa <= 2 - k,
    3|L n T| + c(T_E - L) <= delta(T) <= 2 kappa + 8 - k - max(0, 3 kappa), |L - T| <= k - 1,
    delta_p <= 2 kappa + 3 - max(0, 3 kappa), and (side minimal) c(A1) >= k.
    Returns tuples (|T_E|, kappa, endpoints made non-generic, interior made non-generic)."""
    out = []
    total = sum(c[v] for v in ends)
    for TE in subsets(ends):
        TE = set(TE)
        cT = sum(c[v] for v in TE)
        cA1 = total - cT          # cut edges at A1 = A - T (interior vertices carry none)
        for k in (1, 2, 3):
            if len(set(L) - TE) > k - 1:
                continue
            if minimal and cA1 < k:
                continue
            for kap in (-1, 0, 1):
                if kap > 2 - k:
                    continue
                dmax = 2 * kap + 8 - k - max(0, 3 * kap)
                if 3 * len(set(L) & TE) + sum(c[v] for v in TE if v not in L) > dmax:
                    continue
                dpmax = 2 * kap + 3 - max(0, 3 * kap)
                ps = set()
                for p in TE:
                    dp_min = 3 if p in L else c[p]
                    if cT - c[p] >= 5 - k and dp_min <= dpmax:
                        ps.add(p)
                intok = (cT >= 5 - k) and 0 <= dpmax
                out.append((len(TE), kap, ps, intok))
    return out


def forbidden(cores, nends, i):
    """Forbidden endpoints and whether interior vertices are forbidden, for interior count i.
    Sizes: |T| = |T_E| + t_I >= 5 + kappa, |A - T| >= 5 - kappa, |A| >= 10."""
    nA = nends + i
    forb = set()
    interior_forb = False
    if nA < 10:
        return forb, interior_forb
    for sz, kap, ps, intok in cores:
        tI = max(0, 5 + kap - sz)
        if ps and tI <= i and nA - sz - tI >= 5 - kap:
            forb |= ps
        tI = max(1, 5 + kap - sz)
        if i >= 1 and intok and tI <= i and nA - sz - tI >= 5 - kap:
            interior_forb = True
    return forb, interior_forb


def main():
    configs = 0
    fails = {}
    examples = {}
    for n1 in range(1, 8):
        for n2 in range(1, 8):
            if n1 * 3 < 7 or n2 * 3 < 7:
                continue
            out = subprocess.run([GENBG, '-q', '-d1:1', '-D3:3', str(n1), str(n2), '7:7'],
                                 capture_output=True, text=True).stdout.split()
            for g in out:
                n, adj = decode(g)
                Av = list(range(n1)); Dv = list(range(n1, n1 + n2))
                edges = {(a, d) for a in Av for d in adj[a]}
                c = {v: len(adj[v]) for v in range(n)}
                forcedA = [a for a in Av if c[a] == 3]; forcedD = [d for d in Dv if c[d] == 3]
                optA = [a for a in Av if c[a] < 3]; optD = [d for d in Dv if c[d] < 3]
                for xa in subsets(optA):
                    LA = forcedA + list(xa)
                    if 3 * len(LA) - sum(c[a] for a in LA) > 5:
                        continue
                    for xd in subsets(optD):
                        LD = forcedD + list(xd)
                        if 3 * len(LD) - sum(c[d] for d in LD) > 5:
                            continue
                        configs += 1
                        coresA = core_list(Av, c, LA, MINIMAL)
                        coresD = core_list(Dv, c, LD, MINIMAL)
                        goodp = {(p, q) for p in Av + ['ia'] for q in Dv + ['id'] if covers(p, q, edges, LA, LD)}
                        FA = [forbidden(coresA, len(Av), i) for i in range(9)]
                        FD = [forbidden(coresD, len(Dv), i) for i in range(9)]
                        for iA in range(0, 9):
                            fA, intA = FA[iA]
                            for iD in range(0, 9):
                                fD, intD = FD[iD]
                                Pch = [a for a in Av if a not in fA] + (['ia'] if iA >= 1 and not intA else [])
                                Qch = [d for d in Dv if d not in fD] + (['id'] if iD >= 1 and not intD else [])
                                ok = any((p, q) in goodp for p in Pch for q in Qch)
                                if not ok:
                                    fails[(iA, iD)] = fails.get((iA, iD), 0) + 1
                                    if (iA, iD) not in examples:
                                        examples[(iA, iD)] = (g, n1, n2, sorted(edges), LA, LD, sorted(fA), intA, sorted(fD), intD)
    print('configurations', configs)
    print('failures by (i_A, i_D):', dict(sorted(fails.items())))
    for key in sorted(examples)[:12]:
        print(key, examples[key])


if __name__ == '__main__':
    main()
