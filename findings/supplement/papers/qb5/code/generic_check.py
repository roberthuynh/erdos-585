"""Generic-case check of the E5 pair statement (lane qb5, round 2; NOTES.md section 6).

Under the generic hypothesis H_gen (every demand group of size <= |A| - 2 has demand at most its number of
in-degree-3 vertices, same in Y), a pair (p, q) in A x D is bad iff one of
  (a) c_p + c_q - [p ~ q] >= 4;
  (b) some d in L_D - q has c_d = 1 and d ~ p;
  (c) some a in L_A - p has c_a = 1 and a ~ q;
  (d) some A1 in L_A - p, D1 in L_D - q have |A1| + |D1| - e(A1, D1) >= 5.
L = in-degree-3 big-side vertices (delta = 3). Constraints: c <= 3; c = 3 forces L; 3|L_A| - c(L_A) <= 5.
This script runs over every 7-edge cut graph (nauty genbg, max degree 3, no isolated vertex) and every
admissible labelling, and reports labellings with no good pair, separately for "interior vertices
available" (c = 0 choices for p and q; true in a minimal counterexample, |A|, |D| >= 11) and not.
"""
import subprocess
import sys
from itertools import combinations

GENBG = '[local path]'


def decode(s):
    n = ord(s[0]) - 63
    bits = []
    for ch in s[1:]:
        v = ord(ch) - 63
        for b in range(5, -1, -1):
            bits.append((v >> b) & 1)
    adj = [set() for _ in range(n)]
    k = 0
    for j in range(1, n):
        for i in range(j):
            if bits[k]:
                adj[i].add(j)
                adj[j].add(i)
            k += 1
    return n, adj


def nu(edges):
    best = 0
    for k in range(len(edges), 0, -1):
        for M in combinations(edges, k):
            vs = [x for e in M for x in e]
            if len(set(vs)) == 2 * k:
                return k
    return best


def subsets(s):
    s = list(s)
    for k in range(len(s) + 1):
        for c in combinations(s, k):
            yield c


def bad(p, q, edges, c, LA, LD):
    adjpq = (p, q) in edges
    cp = c.get(p, 0)
    cq = c.get(q, 0)
    if cp + cq - adjpq >= 4:
        return 'a'
    for d in LD:
        if d != q and c[d] == 1 and (p, d) in edges:
            return 'b'
    for a in LA:
        if a != p and c[a] == 1 and (a, q) in edges:
            return 'c'
    LA1 = [a for a in LA if a != p]
    LD1 = [d for d in LD if d != q]
    for A1 in subsets(LA1):
        for D1 in subsets(LD1):
            if len(A1) + len(D1) < 5:
                continue
            e = sum(1 for a in A1 for d in D1 if (a, d) in edges)
            if len(A1) + len(D1) - e >= 5:
                return 'd'
    return None


def covers(p, q, edges, LA, LD):
    """Direct search: a set M of 4 cut edges, none at p or q, covering (L_A - p) u (L_D - q)."""
    avail = [e for e in edges if e[0] != p and e[1] != q]
    need = {a for a in LA if a != p} | {d for d in LD if d != q}
    for M in combinations(avail, 4):
        ends = {x for e in M for x in e}
        if need <= ends:
            return True
    return False


def main():
    total = 0
    fails = {True: 0, False: 0}
    examples = {True: [], False: []}
    for n1 in range(1, 8):
        for n2 in range(1, 8):
            if n1 * 3 < 7 or n2 * 3 < 7:
                continue
            out = subprocess.run([GENBG, '-q', '-d1:1', '-D3:3', str(n1), str(n2), '7:7'],
                                 capture_output=True, text=True).stdout.split()
            for g in out:
                n, adj = decode(g)
                Av = list(range(n1))
                Dv = list(range(n1, n1 + n2))
                edges = {(a, d) for a in Av for d in adj[a]}
                c = {v: len(adj[v]) for v in range(n)}
                nuv = nu(sorted(edges))
                forcedA = [a for a in Av if c[a] == 3]
                forcedD = [d for d in Dv if c[d] == 3]
                optA = [a for a in Av if c[a] < 3]
                optD = [d for d in Dv if c[d] < 3]
                for xa in subsets(optA):
                    LA = forcedA + list(xa)
                    if 3 * len(LA) - sum(c[a] for a in LA) > 5:
                        continue
                    for xd in subsets(optD):
                        LD = forcedD + list(xd)
                        if 3 * len(LD) - sum(c[d] for d in LD) > 5:
                            continue
                        total += 1
                        for interior in (True, False):
                            Pch = Av + (['ia'] if interior else [])
                            Qch = Dv + (['id'] if interior else [])
                            ok = False
                            for p in Pch:
                                for q in Qch:
                                    r = bad(p, q, edges, c, LA, LD) is None
                                    assert r == covers(p, q, edges, LA, LD), (g, p, q, LA, LD)
                                    ok = ok or r
                            if not ok:
                                fails[interior] += 1
                                if len(examples[interior]) < 5:
                                    examples[interior].append((g, n1, n2, sorted(edges), LA, LD, nuv))
    print('labelled configurations', total)
    for interior in (True, False):
        print('interior=%s: configurations with no good pair: %d' % (interior, fails[interior]))
        for ex in examples[interior]:
            print('   ', ex)


if __name__ == '__main__':
    main()
