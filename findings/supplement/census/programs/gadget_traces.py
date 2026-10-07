#!/usr/bin/python3
"""Enumerate every way a pair can meet a gadget (its "traces"), by plain backtracking.

A gadget is a graph plus dangling half-edges ("units") at some vertices. A trace is a coloring of
the edges and units with N (unused), R, B such that every vertex has (red, blue) degree (0,0) or
(2,2), at least one vertex is used, and no color closes a cycle inside the gadget unless that
coloring is a complete pair inside the gadget (reported separately as INTERNAL).

For a trace we report (r, b) = number of red and blue paths through the gadget (each path uses two
units of its color). A gadget is "vertex-like" if every trace has (r, b) = (1, 1) and there is no
internal pair.

This uses no integer programming and no counting argument: it is the independent check of the
single-passage property claimed in PROOF-R1.md.
"""
import sys
from collections import Counter


def traces(n, edges, units, limit=None):
    """units: list of vertices, one entry per dangling half-edge. Returns Counter of trace types."""
    items = [("e", u, v) for u, v in edges] + [("u", v, None) for v in units]
    inc = [[] for _ in range(n)]
    for t, (kind, a, b) in enumerate(items):
        inc[a].append(t)
        if kind == "e":
            inc[b].append(t)
    # order items so that vertices get completed early (BFS order over vertices)
    order, seen = [], set()
    for v in sorted(range(n), key=lambda v: len(inc[v])):
        for t in inc[v]:
            if t not in seen:
                seen.add(t)
                order.append(t)
    col = [None] * len(items)
    red = [0] * n
    blue = [0] * n
    rem = [len(inc[v]) for v in range(n)]
    out = Counter()
    examples = {}

    def feasible(v):
        r, b, m = red[v], blue[v], rem[v]
        if r > 2 or b > 2:
            return False
        if r == 0 and b == 0:
            return True  # can still be unused, or used if enough remain (checked at completion)
        return (2 - r) + (2 - b) <= m

    def done_ok(v):
        return (red[v], blue[v]) in ((0, 0), (2, 2))

    def classify():
        used = [v for v in range(n) if red[v] == 2]
        if not used:
            return None
        res = []
        for c in "RB":
            adj = {v: [] for v in used}
            ends = Counter()
            for t, (kind, a, b) in enumerate(items):
                if col[t] != c:
                    continue
                if kind == "e":
                    adj[a].append(b)
                    adj[b].append(a)
                else:
                    ends[a] += 1
            comp, seenv, paths, cycles = 0, set(), 0, 0
            for s in used:
                if s in seenv:
                    continue
                stack, cv = [s], []
                seenv.add(s)
                while stack:
                    x = stack.pop()
                    cv.append(x)
                    for y in adj[x]:
                        if y not in seenv:
                            seenv.add(y)
                            stack.append(y)
                k = sum(ends[x] for x in cv)
                if k == 0:
                    cycles += 1
                elif k == 2:
                    paths += 1
                else:
                    return "BAD"
            res.append((paths, cycles))
        (rp, rc), (bp, bc) = res
        if rc or bc:
            if rp == 0 and bp == 0 and rc == 1 and bc == 1:
                return "INTERNAL"
            return None  # a color closes a cycle but is not the whole pair: not a trace
        return (rp, bp)

    def rec(i):
        if limit and sum(out.values()) >= limit:
            return
        if i == len(order):
            if all(done_ok(v) for v in range(n)):
                k = classify()
                if k is not None:
                    out[k] += 1
                    examples.setdefault(k, list(col))
            return
        t = order[i]
        kind, a, b = items[t]
        ends = (a,) if kind == "u" else (a, b)
        for v in ends:
            rem[v] -= 1
        for c in "NRB":
            col[t] = c
            if c == "R":
                for v in ends:
                    red[v] += 1
            elif c == "B":
                for v in ends:
                    blue[v] += 1
            ok = all(feasible(v) for v in ends) and all(rem[v] > 0 or done_ok(v) for v in ends)
            if ok:
                rec(i + 1)
            if c == "R":
                for v in ends:
                    red[v] -= 1
            elif c == "B":
                for v in ends:
                    blue[v] -= 1
        col[t] = None
        for v in ends:
            rem[v] += 1

    rec(0)
    return out, examples


if __name__ == "__main__":
    from bip5 import GAMMA, IX, UNITS
    n, edges = GAMMA
    out, ex = traces(n, edges, [IX[u] for u in UNITS])
    print("GAMMA5 traces by (red paths, blue paths):", dict(out))
    print("vertex-like:", set(out) <= {(1, 1)})
