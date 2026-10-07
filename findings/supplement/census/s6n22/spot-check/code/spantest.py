#!/usr/bin/env python3
"""spantest.py (wave8/s6spot): the S6 test by SAT, written independently of wave6/s6n22/code.

For every graph B in a graph6 file whose minimum essential cut (from e10cut's output for the same
file) is at least 10, and every edge oy of B, decide exactly whether Y = B - o - y has two
edge-disjoint Hamilton cycles. Y does not depend on which end of the edge is called o, so the
132 ordered pairs (o, y) give one test per edge: 66 tests for a 6-regular graph on 11 + 11.

SAT encoding (PySAT), one incremental solver per graph B:
  variables  a_v (vertex v is active), x(e, c) (edge e of B has colour c in {0, 1});
  (E1) x(e, c) -> a_u and x(e, c) -> a_v for e = uv          (colours avoid inactive vertices)
  (E2) not x(e, 0) or not x(e, 1)                              (the two cycles are edge-disjoint)
  (E3) at most 2 of the colour-c edges at each vertex          (every 3-subset has a false literal)
  (E4) if a_v then at least 2 colour-c edges at v              (every (deg-1)-subset has a true one)
  (CUT, lazy) for a vertex set S and colour c:
       (some s in S inactive) or (some edge of delta_B(S) has colour c).
A test (o, y) solves under the assumptions not a_o, not a_y, a_v for every other v.
Soundness of a NO: for two edge-disjoint Hamilton cycles H0, H1 of Y, the assignment
a_v = [v not in {o, y}], x(e, c) = [e in Hc] satisfies E1-E4, and every CUT clause: if S meets
{o, y} its guard holds; otherwise S is a proper non-empty subset of V(Y) (cuts are only built
from cycles of a non-Hamiltonian 2-factor, so |S| <= |V(Y)| - 4), and the Hamilton cycle Hc
leaves S along an edge of delta_B(S). So UNSAT under the assumptions means no pair exists; cuts
from earlier tests stay valid for later ones.
Loop: a model gives each colour a 2-factor of Y; if both are Hamilton cycles, the two cyclic
vertex sequences are checked by verify_pair (independent of the encoding: permutations of V(Y),
consecutive vertices adjacent in B, the 40 edges distinct) and the test is SPAN; otherwise the
CUT clause of every cycle of every non-Hamiltonian colour is added for both colours (the current
model violates it, so the loop terminates) and the solver runs again.
A NO answer is re-decided by decide_fresh (a separate encoding of Y alone, no activation
literals, a different SAT solver) and both answers are recorded.

Usage: spantest.py file.g6 file.cut out_prefix [--solver minisat22] [--all] [--limit N]
  --all: also test the graphs that are not E10 (their results are kept separate).
Writes out_prefix.span.json (summary) and out_prefix.no (one line per NO, if any).
"""
import sys, json, time, argparse, itertools
from pysat.solvers import Solver


def decode_g6(line):
    s = line.strip()
    n = ord(s[0]) - 63
    if not (2 <= n <= 62):
        raise ValueError("graph6: bad n")
    nbits = n * (n - 1) // 2
    if len(s) != 1 + (nbits + 5) // 6:
        raise ValueError("graph6: bad length")
    bits = []
    for ch in s[1:]:
        c = ord(ch) - 63
        if not 0 <= c <= 63:
            raise ValueError("graph6: bad char")
        bits.extend((c >> (5 - i)) & 1 for i in range(6))
    if any(bits[nbits:]):
        raise ValueError("graph6: nonzero padding")
    edges = []
    k = 0
    for j in range(1, n):
        for i in range(j):
            if bits[k]:
                edges.append((i, j))
            k += 1
    edges.sort()
    return n, edges


def edge_hash(edges):
    h = 0
    for u, v in edges:  # sorted, u < v
        h = (h * 1000003 + 64 * u + v) & 0xFFFFFFFFFFFFFFFF
    return h


def verify_pair(n, edgeset, o, y, c1, c2):
    """Independent witness check: c1, c2 are cyclic vertex sequences; True iff both are Hamilton
    cycles of B - o - y and they share no edge."""
    rest = set(range(n)) - {o, y}
    used = []
    for cyc in (c1, c2):
        if len(cyc) != len(rest) or set(cyc) != rest:
            return False
        es = set()
        L = len(cyc)
        for i in range(L):
            u, v = cyc[i], cyc[(i + 1) % L]
            e = (u, v) if u < v else (v, u)
            if e not in edgeset or o in e or y in e:
                return False
            es.add(e)
        if len(es) != L:
            return False
        used.append(es)
    return not (used[0] & used[1])


def cycles_of(n_active, active, nbrs):
    """nbrs: dict vertex -> list of neighbours in one colour class. Returns the list of cycles
    (cyclic vertex lists) of this 2-regular graph on the active vertices; raises on a vertex of
    the wrong degree (that would be an encoding bug)."""
    for v in active:
        if len(nbrs.get(v, ())) != 2:
            raise RuntimeError("colour class is not 2-regular on the active vertices")
    if len(nbrs) != n_active:
        raise RuntimeError("colour class touches an inactive vertex")
    seen = set()
    cyc_list = []
    for s in active:
        if s in seen:
            continue
        cyc = [s]
        seen.add(s)
        prev, cur = s, nbrs[s][0]
        while cur != s:
            cyc.append(cur)
            seen.add(cur)
            a, b = nbrs[cur]
            prev, cur = cur, (b if a == prev else a)
        cyc_list.append(cyc)
    return cyc_list


class GraphSAT:
    def __init__(self, n, edges, solver_name):
        self.n = n
        self.edges = edges
        self.m = len(edges)
        self.inc = [[] for _ in range(n)]
        for ei, (u, v) in enumerate(edges):
            self.inc[u].append(ei)
            self.inc[v].append(ei)
        X = self.X
        cl = []
        for ei, (u, v) in enumerate(edges):
            for c in (0, 1):
                cl.append([-X(ei, c), u + 1])
                cl.append([-X(ei, c), v + 1])
            cl.append([-X(ei, 0), -X(ei, 1)])
        for v in range(n):
            for c in (0, 1):
                xs = [X(ei, c) for ei in self.inc[v]]
                for t in itertools.combinations(xs, 3):
                    cl.append([-t[0], -t[1], -t[2]])
                for drop in range(len(xs)):
                    cl.append([-(v + 1)] + xs[:drop] + xs[drop + 1:])
        self.solver = Solver(name=solver_name, bootstrap_with=cl)
        self.ncuts = 0

    def X(self, ei, c):
        return self.n + 1 + 2 * ei + c

    def close(self):
        self.solver.delete()

    def add_cut(self, S):
        guard = [-(s + 1) for s in S]
        delta = [ei for ei, (u, v) in enumerate(self.edges) if (u in S) != (v in S)]
        for c in (0, 1):
            self.solver.add_clause(guard + [self.X(ei, c) for ei in delta])
        self.ncuts += 2

    def test(self, o, y):
        n = self.n
        active = [v for v in range(n) if v != o and v != y]
        assum = [-(o + 1), -(y + 1)] + [v + 1 for v in active]
        rounds = 0
        while True:
            rounds += 1
            if not self.solver.solve(assumptions=assum):
                return "NO", rounds, None
            model = self.solver.get_model()
            cyc_by_c = []
            for c in (0, 1):
                nb = {}
                base = n + c  # X(ei, c) - 1 = n + 2 ei + c
                for ei, (u, v) in enumerate(self.edges):
                    if model[base + 2 * ei] > 0:
                        nb.setdefault(u, []).append(v)
                        nb.setdefault(v, []).append(u)
                cyc_by_c.append(cycles_of(len(active), active, nb))
            if len(cyc_by_c[0]) == 1 and len(cyc_by_c[1]) == 1:
                return "SPAN", rounds, (cyc_by_c[0][0], cyc_by_c[1][0])
            for cl in cyc_by_c:
                if len(cl) > 1:
                    for cyc in cl:
                        self.add_cut(set(cyc))


def decide_fresh(n, edges, o, y, solver_name="cadical153"):
    """Second encoding for re-deciding NO answers: Y alone, variables only for the edges of Y,
    exactly-2 per vertex and colour by plain clauses, lazy unguarded cuts over delta_Y(S)."""
    V = [v for v in range(n) if v != o and v != y]
    E = [(u, v) for (u, v) in edges if u not in (o, y) and v not in (o, y)]
    var = {}
    for i, e in enumerate(E):
        var[(e, 0)] = 2 * i + 1
        var[(e, 1)] = 2 * i + 2
    inc = {v: [] for v in V}
    for e in E:
        inc[e[0]].append(e)
        inc[e[1]].append(e)
    cl = [[-var[(e, 0)], -var[(e, 1)]] for e in E]
    for v in V:
        for c in (0, 1):
            xs = [var[(e, c)] for e in inc[v]]
            for t in itertools.combinations(xs, 3):
                cl.append([-l for l in t])
            for t in itertools.combinations(xs, len(xs) - 1):
                cl.append(list(t))
    s = Solver(name=solver_name, bootstrap_with=cl)
    rounds = 0
    try:
        while True:
            rounds += 1
            if not s.solve():
                return "NO", rounds, None
            mdl = set(l for l in s.get_model() if l > 0)
            cycs = []
            for c in (0, 1):
                nb = {}
                for e in E:
                    if var[(e, c)] in mdl:
                        nb.setdefault(e[0], []).append(e[1])
                        nb.setdefault(e[1], []).append(e[0])
                cycs.append(cycles_of(len(V), V, nb))
            if len(cycs[0]) == 1 and len(cycs[1]) == 1:
                return "SPAN", rounds, (cycs[0][0], cycs[1][0])
            for cl_c in cycs:
                if len(cl_c) > 1:
                    for cyc in cl_c:
                        S = set(cyc)
                        d = [e for e in E if (e[0] in S) != (e[1] in S)]
                        for c in (0, 1):
                            s.add_clause([var[(e, c)] for e in d])
    finally:
        s.delete()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("g6")
    ap.add_argument("cut")
    ap.add_argument("out")
    ap.add_argument("--solver", default="minisat22")
    ap.add_argument("--all", action="store_true")
    ap.add_argument("--limit", type=int, default=0)
    ap.add_argument("--only-non-e10", action="store_true",
                    help="count every graph but run the tests only on the graphs that are not E10")
    a = ap.parse_args()

    t0 = time.time()
    cpu0 = time.process_time()
    st = dict(graphs=0, e10=0, non_e10=0, tests=0, span=0, no=0, witness_fail=0,
              fresh_span=0, fresh_no=0, hash_mismatch=0, cuts=0, rounds_hist={},
              mincut_hist={}, non_e10_graphs=[], solver=a.solver)
    nofile = open(a.out + ".no", "w")
    with open(a.g6) as fg, open(a.cut) as fc:
        for gi, (gl, cl) in enumerate(zip(fg, fc)):
            if a.limit and gi >= a.limit:
                break
            n, edges = decode_g6(gl)
            f = cl.split()
            if int(f[0]) != gi:
                raise RuntimeError("cut file out of step at %d" % gi)
            mincut = int(f[1])
            if int(f[4], 16) != edge_hash(edges):
                st["hash_mismatch"] += 1
                raise RuntimeError("edge hash mismatch at %d" % gi)
            # sanity: 6-regular, bipartite with sides 0..n/2-1 and n/2..n-1
            deg = [0] * n
            for u, v in edges:
                deg[u] += 1
                deg[v] += 1
                if not (u < n // 2 <= v):
                    raise RuntimeError("edge inside a side at %d" % gi)
            if any(d != 6 for d in deg):
                raise RuntimeError("not 6-regular at %d" % gi)
            st["graphs"] += 1
            st["mincut_hist"][mincut] = st["mincut_hist"].get(mincut, 0) + 1
            e10 = mincut >= 10
            if e10:
                st["e10"] += 1
            else:
                st["non_e10"] += 1
                rec = dict(index=gi, g6=gl.strip(), mincut=mincut, cutset_size=int(f[2]),
                           cutset_mask=f[3])
                st["non_e10_graphs"].append(rec)
                if not (a.all or a.only_non_e10):
                    continue
            if e10 and a.only_non_e10:
                continue
            edgeset = set(edges)
            g = GraphSAT(n, edges, a.solver)
            res_this = {"SPAN": 0, "NO": 0}
            for (o, y) in edges:
                ans, rounds, wit = g.test(o, y)
                key = "e10" if e10 else "nonE10"
                st["tests" if e10 else "tests_nonE10"] = st.get("tests" if e10 else "tests_nonE10", 0) + 1
                r = min(rounds, 64)
                st["rounds_hist"][r] = st["rounds_hist"].get(r, 0) + 1
                if ans == "SPAN":
                    if not verify_pair(n, edgeset, o, y, wit[0], wit[1]):
                        st["witness_fail"] += 1
                        nofile.write("WITNESS_FAIL %d %d %d\n" % (gi, o, y))
                        continue
                    st["span" if e10 else "span_nonE10"] = st.get("span" if e10 else "span_nonE10", 0) + 1
                    res_this["SPAN"] += 1
                else:
                    ans2, r2, wit2 = decide_fresh(n, edges, o, y)
                    ok2 = None
                    if ans2 == "SPAN":
                        ok2 = verify_pair(n, edgeset, o, y, wit2[0], wit2[1])
                        st["fresh_span"] += 1
                    else:
                        st["fresh_no"] += 1
                    st["no" if e10 else "no_nonE10"] = st.get("no" if e10 else "no_nonE10", 0) + 1
                    res_this["NO"] += 1
                    nofile.write("NO graph=%d o=%d y=%d e10=%d fresh=%s fresh_witness_ok=%s\n"
                                 % (gi, o, y, int(e10), ans2, ok2))
            st["cuts"] += g.ncuts
            g.close()
            if not e10:
                st["non_e10_graphs"][-1]["tests"] = res_this
    nofile.close()
    st["sec_wall"] = round(time.time() - t0, 2)
    st["sec_cpu"] = round(time.process_time() - cpu0, 2)
    with open(a.out + ".span.json", "w") as fo:
        json.dump(st, fo, indent=1, sort_keys=True)
    print(json.dumps({k: st[k] for k in st if k not in ("non_e10_graphs",)}, sort_keys=True))


if __name__ == "__main__":
    main()
