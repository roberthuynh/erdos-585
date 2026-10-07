#!/usr/bin/env python3
"""wave4/h22b: second HD decider, SAT with lazy subtour cuts (PySAT). Shares no code with hdq.c.

For a 4-regular graph G: variable x_e (true = red). At each vertex exactly 2 of its 4 edges are
red (no 3 red, no 3 blue). Solve; if the red edges form several cycles, add for each red cycle
with vertex set S the clause "some edge of the cut (S, V-S) is red"; the same for blue with
"some edge of the cut is blue". Both are valid for a Hamilton decomposition, since a Hamilton
cycle crosses every edge cut at least twice. Repeat until a model with one red and one blue
cycle (HD, certificate checked) or UNSAT (not HD). x_0 is fixed red (colour symmetry).

usage: sat_hd.py FILE  (lines whose first field is graph6; other fields ignored)
Prints "<g6> SAT_HD <hexmask> iters=<k>" or "<g6> SAT_NOT_HD iters=<k>" per graph and a summary.
"""
import itertools
import sys

from pysat.solvers import Cadical153


def parse_g6(s):
    n = ord(s[0]) - 63
    bits = []
    for ch in s[1:]:
        v = ord(ch) - 63
        for sh in range(5, -1, -1):
            bits.append((v >> sh) & 1)
    edges = []
    k = 0
    for j in range(1, n):
        for i in range(j):
            if bits[k]:
                edges.append((i, j))
            k += 1
    return n, edges


def components(n, es):
    adj = [[] for _ in range(n)]
    for a, b in es:
        adj[a].append(b)
        adj[b].append(a)
    comp = [-1] * n
    out = []
    for s in range(n):
        if comp[s] >= 0:
            continue
        comp[s] = len(out)
        cur = [s]
        stack = [s]
        while stack:
            v = stack.pop()
            for w in adj[v]:
                if comp[w] < 0:
                    comp[w] = comp[s]
                    cur.append(w)
                    stack.append(w)
        out.append(set(cur))
    return out


def decide(n, edges):
    m = len(edges)
    inc = [[] for _ in range(n)]
    for k, (a, b) in enumerate(edges):
        inc[a].append(k + 1)
        inc[b].append(k + 1)
    if any(len(x) != 4 for x in inc):
        raise ValueError("not 4-regular")
    s = Cadical153()
    for v in range(n):
        for t in itertools.combinations(inc[v], 3):
            s.add_clause([-x for x in t])
            s.add_clause(list(t))
    s.add_clause([1])
    iters = 0
    while True:
        iters += 1
        if not s.solve():
            s.delete()
            return None, iters
        model = s.get_model()
        val = {abs(l): l > 0 for l in model}
        red = [edges[k] for k in range(m) if val.get(k + 1, False)]
        blue = [edges[k] for k in range(m) if not val.get(k + 1, False)]
        rc, bc = components(n, red), components(n, blue)
        if len(rc) == 1 and len(bc) == 1:
            mask = sum(1 << k for k in range(m) if val.get(k + 1, False))
            s.delete()
            return mask, iters
        for S in rc if len(rc) > 1 else []:
            s.add_clause([k + 1 for k, (a, b) in enumerate(edges) if (a in S) != (b in S)])
        for S in bc if len(bc) > 1 else []:
            s.add_clause([-(k + 1) for k, (a, b) in enumerate(edges) if (a in S) != (b in S)])


def check(n, edges, mask):
    for want in (1, 0):
        es = [e for k, e in enumerate(edges) if ((mask >> k) & 1) == want]
        deg = [0] * n
        for a, b in es:
            deg[a] += 1
            deg[b] += 1
        if len(es) != n or any(d != 2 for d in deg) or len(components(n, es)) != 1:
            return False
    return True


def main(fn):
    hd = nothd = bad = 0
    for line in open(fn):
        parts = line.split()
        if not parts or parts[0].startswith(">"):
            continue
        g6 = parts[0]
        n, edges = parse_g6(g6)
        mask, iters = decide(n, edges)
        if mask is None:
            nothd += 1
            print(f"{g6} SAT_NOT_HD iters={iters}")
        elif check(n, edges, mask):
            hd += 1
            print(f"{g6} SAT_HD {mask:x} iters={iters}")
        else:
            bad += 1
            print(f"{g6} SAT_BADCERT {mask:x} iters={iters}")
    print(f"sat_hd graphs={hd + nothd + bad} HD={hd} NOT_HD={nothd} BADCERT={bad}", file=sys.stderr)
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1]))
