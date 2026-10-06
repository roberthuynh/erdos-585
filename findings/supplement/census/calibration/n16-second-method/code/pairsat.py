#!/usr/bin/env python3
"""Pair decider by SAT (PySAT), second method for the 16-vertex 5-regular question.

A pair is two edge-disjoint cycles C1, C2 of a simple graph G with V(C1) = V(C2).

Encoding (written for this lane; shares nothing with pairc, pairprune.c or the B-1 tools).
One CNF per vertex count n, built once over all n(n-1)/2 vertex pairs; a graph enters only
through assumptions -g[p] for the non-edges p. Variables:
  g[p]          pair p is an edge of G (assumption-controlled)
  a[p], b[p]    pair p is an edge of cycle A, of cycle B
  x[v]          v is in the common vertex set S
  r[v]          v is the root, forced to be the least vertex of S
  la[v][t]      v is reached from the root by a walk of <= t edges of A (lb: of B)
  ya[u][v][t]   v is reached at step t through u (yb: for B)
Clauses:
  a[p] -> g[p], b[p] -> g[p], not(a[p] and b[p]); a[uv] -> x[u], x[v] (same for b)
  x[v] -> at least 2 a-edges at v; at most 2 a-edges at v (all triples excluded); same for b
  exactly one root; root in S; nothing smaller than the root in S
  la[v][0] = r[v]; la[v][t] -> la[v][t-1] or OR_u ya[u][v][t]; ya[u][v][t] -> la[u][t-1] and a[uv]
  x[v] -> la[v][T] and lb[v][T], with T = floor(n/2)
Sound: A is a 2-regular subgraph of G[S] spanning S whose vertices are all reachable from the
root, so A is one cycle through all of S; the same for B; A and B share no edge.
Complete: from a pair, root = min S and la/lb = true distances along each cycle (<= floor(|S|/2)).

Every SAT answer is turned into two vertex sequences and checked by verify_pair against the
graph as decoded by networkx (a second graph6 decoder), not against the encoding.
"""
import argparse
import itertools
import json
import os
import sys
import time

from pysat.solvers import Solver
import networkx as nx


def g6_order(n):
    return [(i, j) for j in range(1, n) for i in range(j)]


_ORDER = {}


def g6_decode(s):
    """Own graph6 decoder (n <= 62). Returns (n, sorted edge list with i < j)."""
    s = s.strip()
    if s.startswith(b">>graph6<<"):
        s = s[10:]
    n = s[0] - 63
    if n < 0 or n > 62:
        raise ValueError("unsupported graph6 header")
    order = _ORDER.get(n)
    if order is None:
        order = _ORDER[n] = g6_order(n)
    need = (len(order) + 5) // 6
    if len(s) != 1 + need:
        raise ValueError("bad graph6 length")
    edges = []
    k = 0
    m = len(order)
    for c in s[1:]:
        x = c - 63
        if x < 0 or x > 63:
            raise ValueError("bad graph6 byte")
        for sh in (5, 4, 3, 2, 1, 0):
            if k < m and (x >> sh) & 1:
                edges.append(order[k])
            k += 1
    return n, edges


def nx_adj(line):
    """Adjacency sets from networkx's graph6 decoder (independent of g6_decode)."""
    G = nx.from_graph6_bytes(line.strip())
    n = G.number_of_nodes()
    adj = [set() for _ in range(n)]
    for u, v in G.edges():
        if u == v:
            raise ValueError("loop")
        adj[u].add(v)
        adj[v].add(u)
    return n, adj


def verify_pair(n, adj, c1, c2):
    """Check that c1, c2 (vertex sequences) are edge-disjoint cycles of the graph with the same
    vertex set. Uses only adj (list of neighbour sets). Returns (ok, reason)."""
    def cyc_edges(c):
        k = len(c)
        if k < 3:
            return None, "cycle shorter than 3"
        if len(set(c)) != k:
            return None, "repeated vertex"
        es = set()
        for i in range(k):
            u, v = c[i], c[(i + 1) % k]
            if not (0 <= u < n and 0 <= v < n):
                return None, "vertex out of range"
            if v not in adj[u]:
                return None, "non-edge %d-%d" % (u, v)
            es.add((u, v) if u < v else (v, u))
        if len(es) != k:
            return None, "repeated edge"
        return es, ""

    e1, why = cyc_edges(c1)
    if e1 is None:
        return False, "C1: " + why
    e2, why = cyc_edges(c2)
    if e2 is None:
        return False, "C2: " + why
    if set(c1) != set(c2):
        return False, "vertex sets differ"
    if e1 & e2:
        return False, "shared edge"
    return True, ""


class PairSAT:
    def __init__(self, n, solver="g4", phase_x=False):
        self.n = n
        pairs = [(u, v) for u in range(n) for v in range(u + 1, n)]
        self.pairs = pairs
        self.top = 0

        def new():
            self.top += 1
            return self.top

        g = {p: new() for p in pairs}
        a = {p: new() for p in pairs}
        b = {p: new() for p in pairs}
        x = [new() for _ in range(n)]
        r = [new() for _ in range(n)]
        self.g, self.a, self.b, self.x, self.r = g, a, b, x, r
        T = n // 2
        self.T = T

        def e(u, v):
            return (u, v) if u < v else (v, u)

        cl = []
        for p in pairs:
            u, v = p
            for c in (a, b):
                cl.append([-c[p], g[p]])
                cl.append([-c[p], x[u]])
                cl.append([-c[p], x[v]])
            cl.append([-a[p], -b[p]])
        for v in range(n):
            others = [u for u in range(n) if u != v]
            for c in (a, b):
                lits = [c[e(u, v)] for u in others]
                for i in range(len(lits)):
                    cl.append([-x[v]] + lits[:i] + lits[i + 1:])
                for t3 in itertools.combinations(lits, 3):
                    cl.append([-t3[0], -t3[1], -t3[2]])
        cl.append(list(r))
        for u, v in itertools.combinations(range(n), 2):
            cl.append([-r[u], -r[v]])
        for v in range(n):
            cl.append([-r[v], x[v]])
            for w in range(v):
                cl.append([-r[v], -x[w]])
        for c in (a, b):
            L = [[r[v]] for v in range(n)]
            for t in range(1, T + 1):
                for v in range(n):
                    L[v].append(new())
            for t in range(1, T + 1):
                for v in range(n):
                    ys = []
                    for u in range(n):
                        if u == v:
                            continue
                        y = new()
                        cl.append([-y, L[u][t - 1]])
                        cl.append([-y, c[e(u, v)]])
                        ys.append(y)
                    cl.append([-L[v][t], L[v][t - 1]] + ys)
            for v in range(n):
                cl.append([-x[v], L[v][T]])
        self.nclauses = len(cl)
        self.s = Solver(name=solver, bootstrap_with=cl)
        self.solver_name = solver
        if phase_x:
            # search heuristic only: try v in S first (no effect on what is SAT or UNSAT)
            self.s.set_phases(list(x))

    def assumptions(self, edges):
        es = set(edges)
        return [-self.g[p] for p in self.pairs if p not in es]

    def decide(self, edges):
        """Returns (True, (S, c1, c2)) or (False, None)."""
        ok = self.s.solve(assumptions=self.assumptions(edges))
        if not ok:
            return False, None
        model = self.s.get_model()
        val = lambda var: model[var - 1] > 0
        n = self.n
        S = [v for v in range(n) if val(self.x[v])]
        cycles = []
        for c in (self.a, self.b):
            nb = {v: [] for v in S}
            for p in self.pairs:
                if val(c[p]):
                    u, v = p
                    nb[u].append(v)
                    nb[v].append(u)
            start = S[0]
            seq = [start]
            prev, cur = None, start
            while True:
                nxt = [w for w in nb[cur] if w != prev]
                if prev is None:
                    nxt = nb[cur][:1]
                if not nxt:
                    break
                prev, cur = cur, nxt[0]
                if cur == start:
                    break
                seq.append(cur)
                if len(seq) > n:
                    break
            cycles.append(seq)
        return True, (S, cycles[0], cycles[1])


def run_file(path, out_prefix, solver="g4", certs=False, expect_n=None, expect_deg=None,
             progress_every=200000, logf=None, phase_x=False):
    t0 = time.time()
    dec = {}
    stats = {"input": path, "graphs": 0, "pair": 0, "nopair": 0, "verify_fail": 0,
             "decode_mismatch": 0, "degree_mismatch": 0, "S_size_hist": {}, "n_hist": {},
             "solver": solver, "phase_x": phase_x}
    certf = open(out_prefix + ".certs.txt", "w") if certs else None
    nopf = open(out_prefix + ".nopair.g6", "wb")
    badf = open(out_prefix + ".verifyfail.txt", "w")
    with open(path, "rb") as fh:
        for line in fh:
            line = line.strip()
            if not line or line.startswith(b">"):
                continue
            n, edges = g6_decode(line)
            n2, adj = nx_adj(line)
            m2 = sum(len(s) for s in adj) // 2
            if n2 != n or m2 != len(edges) or any(v not in adj[u] for u, v in edges):
                stats["decode_mismatch"] += 1
                badf.write("DECODE %s\n" % line.decode())
                continue
            if expect_n is not None and n != expect_n:
                raise SystemExit("unexpected n %d" % n)
            if expect_deg is not None and any(len(s) != expect_deg for s in adj):
                stats["degree_mismatch"] += 1
                badf.write("DEGREE %s\n" % line.decode())
            stats["n_hist"][n] = stats["n_hist"].get(n, 0) + 1
            if n not in dec:
                dec[n] = PairSAT(n, solver, phase_x)
            stats["graphs"] += 1
            ok, cert = dec[n].decide(edges)
            if ok:
                S, c1, c2 = cert
                good, why = verify_pair(n, adj, c1, c2)
                if not good:
                    stats["verify_fail"] += 1
                    badf.write("VERIFY %s %s S=%s C1=%s C2=%s\n" % (line.decode(), why, S, c1, c2))
                    continue
                stats["pair"] += 1
                k = len(c1)
                stats["S_size_hist"][k] = stats["S_size_hist"].get(k, 0) + 1
                if certf:
                    certf.write("%s PAIR C1=%s C2=%s\n" % (line.decode(), ",".join(map(str, c1)),
                                                          ",".join(map(str, c2))))
            else:
                stats["nopair"] += 1
                nopf.write(line + b"\n")
                if certf:
                    certf.write("%s NOPAIR\n" % line.decode())
            if logf and stats["graphs"] % progress_every == 0:
                with open(logf, "a") as lf:
                    lf.write("%s graphs=%d pair=%d nopair=%d vfail=%d t=%.1fs\n" % (
                        time.strftime("%H:%M:%S"), stats["graphs"], stats["pair"], stats["nopair"],
                        stats["verify_fail"], time.time() - t0))
    for f in (certf, nopf, badf):
        if f:
            f.close()
    stats["seconds"] = round(time.time() - t0, 2)
    stats["cpu_seconds"] = round(time.process_time(), 2)
    stats["S_size_hist"] = {str(k): v for k, v in sorted(stats["S_size_hist"].items())}
    stats["n_hist"] = {str(k): v for k, v in sorted(stats["n_hist"].items())}
    stats["clauses_per_n"] = {str(k): d.nclauses for k, d in sorted(dec.items())}
    with open(out_prefix + ".summary.json", "w") as f:
        json.dump(stats, f, indent=1, sort_keys=True)
        f.write("\n")
    return stats


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("input")
    ap.add_argument("out_prefix")
    ap.add_argument("--solver", default="g4")
    ap.add_argument("--certs", action="store_true")
    ap.add_argument("--n", type=int, default=None)
    ap.add_argument("--deg", type=int, default=None)
    ap.add_argument("--log", default=None)
    ap.add_argument("--every", type=int, default=200000)
    ap.add_argument("--phase-x", action="store_true")
    a = ap.parse_args()
    st = run_file(a.input, a.out_prefix, a.solver, a.certs, a.n, a.deg, a.every, a.log, a.phase_x)
    print(json.dumps({k: st[k] for k in ("graphs", "pair", "nopair", "verify_fail",
                                          "decode_mismatch", "degree_mismatch", "seconds")}))


if __name__ == "__main__":
    main()
