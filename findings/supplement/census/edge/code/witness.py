"""witness.py: lower-bound witnesses for ex(n), n = 16..20, with SAT certificates.

Start: the first graph with e = 37 = 3*15 - 8 in census/f1/q4free_bip_n15_e33-45.g6 (n = 15, delta >= 4,
no 4-regular subgraph; one of the 37 extremal graphs at n = 15). Then add one vertex at a time with
exactly 3 neighbours, all on the opposite side and all of degree <= 5, alternating sides. Each step
adds 1 vertex and 3 edges, so e - 3n stays at -8; a vertex of degree 3 lies in no 4-regular subgraph,
so the graph stays 4-regular-free (the SAT check below does not rely on this).

For every witness (n = 15..20) the script checks: simple, bipartite, max degree <= 6, e = 3n - 8, and
decides "has a nonempty 4-regular subgraph" three ways:
  1. validate_sat.has_q4 (pysat CaDiCaL 1.5.3, the census decider): must return None (UNSAT);
  2. q4filter (q4core.h, a different program): must print the graph (no 4-regular subgraph);
  3. glucose4 on the same CNF with a DRAT proof, checked here by an independent RUP checker
     (deletions ignored, which is sound); the proof must end in the empty clause.
Writes data/witness_n<N>.g6, data/witness_n<N>.cnf (DIMACS), data/witness_n<N>.drat and
data/WITNESSES.txt (the checks).

The CNF is validate_sat.py's encoding, written out: x_e -> y_u and x_e -> y_v; at most 4 chosen edges
at each vertex (every 5-subset of incident edges has a false one); y_v -> at least 4 chosen edges at v
(every (d-3)-subset has a true one; y_v false if d < 4); some y_v true. A model is a nonempty subgraph
with all degrees in {0, 4}.
"""
import itertools
import os
import subprocess
import sys

import networkx as nx
from pysat.solvers import Solver

E = "[local path]"
QDIR = "[local path]"
SRC = "[local path]"
sys.path.insert(0, QDIR)
from validate_sat import has_q4  # noqa: E402


def cnf(g):
    nodes = sorted(g.nodes())
    idx = {v: i + 1 for i, v in enumerate(nodes)}
    edges = sorted(tuple(sorted(e)) for e in g.edges())
    ev = {e: len(nodes) + 1 + i for i, e in enumerate(edges)}
    inc = {v: [] for v in nodes}
    for (u, v), x in ev.items():
        inc[u].append(x)
        inc[v].append(x)
    cl = []
    for (u, v), x in ev.items():
        cl.append([-x, idx[u]])
        cl.append([-x, idx[v]])
    for v in nodes:
        xs = inc[v]
        d = len(xs)
        for B in itertools.combinations(xs, 5):
            cl.append([-b for b in B])
        if d < 4:
            cl.append([-idx[v]])
        else:
            for A in itertools.combinations(xs, d - 3):
                cl.append([-idx[v]] + list(A))
    cl.append([idx[v] for v in nodes])
    return len(nodes) + len(edges), cl


def rup_check(clauses, proof):
    """Check a DRAT proof using RUP steps only (deletions ignored). True iff every added lemma is
    RUP with respect to the clauses so far and the empty clause is derived."""
    db, occ = [], {}

    def add(c):
        db.append(list(c))
        for l in c:
            occ.setdefault(l, []).append(len(db) - 1)

    def conflict_after(assume):
        val = {}
        q = []

        def setlit(l):
            v = abs(l)
            if v in val:
                return val[v] == (l > 0)
            val[v] = l > 0
            q.append(l)
            return True

        for l in assume:
            if not setlit(l):
                return True
        for c in db:
            if len(c) == 1 and not setlit(c[0]):
                return True
            if len(c) == 0:
                return True
        while q:
            l = q.pop()
            for ci in occ.get(-l, ()):
                unassigned, cnt, sat = None, 0, False
                for x in db[ci]:
                    v = abs(x)
                    if v in val:
                        if val[v] == (x > 0):
                            sat = True
                            break
                    else:
                        cnt += 1
                        unassigned = x
                        if cnt > 1:
                            break
                if sat or cnt > 1:
                    continue
                if cnt == 0:
                    return True
                if not setlit(unassigned):
                    return True
        return False

    for c in clauses:
        add(c)
    lemmas = 0
    for line in proof:
        t = line.split()
        if not t:
            continue
        if t[0] == "d":
            continue
        lits = [int(x) for x in t]
        assert lits[-1] == 0
        lits = lits[:-1]
        if not conflict_after([-l for l in lits]):
            return False, lemmas, "lemma %d not RUP: %s" % (lemmas + 1, line)
        lemmas += 1
        if not lits:
            return True, lemmas, "empty clause derived"
        add(lits)
    return False, lemmas, "no empty clause in proof"


def extend(g, side):
    """Add one vertex with 3 neighbours of degree <= 5 on the side opposite to `side`."""
    n = g.number_of_nodes()
    other = [v for v in g.nodes() if side[v] != 0 and g.degree(v) <= 5]
    other0 = [v for v in g.nodes() if side[v] == 0 and g.degree(v) <= 5]
    # put the new vertex on side 0 if side 1 has 3 low-degree vertices, else on side 1
    if (n % 2 == 0 and len(other) >= 3) or len(other0) < 3:
        nbrs, s = sorted(other, key=lambda v: (g.degree(v), v))[:3], 0
    else:
        nbrs, s = sorted(other0, key=lambda v: (g.degree(v), v))[:3], 1
    assert len(nbrs) == 3
    g.add_node(n)
    side[n] = s
    for u in nbrs:
        g.add_edge(n, u)
    return n, nbrs


def main():
    start = None
    for l in open(SRC):
        l = l.strip()
        if l and nx.from_graph6_bytes(l.encode()).number_of_edges() == 37:
            start = l
            break
    g = nx.convert_node_labels_to_integers(nx.from_graph6_bytes(start.encode()))
    col = nx.bipartite.color(g)
    side = dict(col)
    out = [f"source: {SRC}", f"start graph (n = 15, e = 37): first e = 37 line, graph6 {start}", ""]
    steps = []
    for n in range(15, 21):
        if n > 15:
            v, nb = extend(g, side)
            steps.append(f"vertex {v} on side {side[v]} joined to {nb}")
        e = g.number_of_edges()
        assert g.number_of_nodes() == n
        assert nx.is_bipartite(g) and all(side[a] != side[b] for a, b in g.edges())
        assert max(d for _, d in g.degree()) <= 6
        assert e == 3 * n - 8, (n, e)
        g6 = nx.to_graph6_bytes(g, header=False).decode().strip()
        base = os.path.join(E, "data", f"witness_n{n}")
        open(base + ".g6", "w").write(g6 + "\n")
        # 1. census SAT decider
        r1 = has_q4(nx.from_graph6_bytes(g6.encode()))
        # 2. q4filter
        p = subprocess.run([os.path.join(QDIR, "q4filter")], input=g6 + "\n", capture_output=True, text=True)
        r2 = p.stdout.strip() == g6
        # 3. glucose4 + DRAT, checked by RUP
        nv, cl = cnf(g)
        with open(base + ".cnf", "w") as f:
            f.write(f"p cnf {nv} {len(cl)}\n")
            for c in cl:
                f.write(" ".join(map(str, c)) + " 0\n")
        with Solver(name="glucose4", bootstrap_with=cl, with_proof=True) as s:
            sat = s.solve()
            proof = s.get_proof() if not sat else []
        open(base + ".drat", "w").write("\n".join(proof) + "\n")
        ok, nl, msg = rup_check(cl, proof)
        degs = sorted((d for _, d in g.degree()), reverse=True)
        sides = (sum(1 for v in g if side[v] == 0), sum(1 for v in g if side[v] == 1))
        out.append(f"n = {n}: e = {e} = 3n - 8, sides {sides[0]} + {sides[1]}, max degree {degs[0]}, "
                   f"min degree {degs[-1]}; graph6 in data/witness_n{n}.g6")
        out.append(f"  pysat CaDiCaL (validate_sat.has_q4): {'UNSAT (no 4-regular subgraph)' if r1 is None else 'SAT !!!'}")
        out.append(f"  q4filter (q4core.h): {'no 4-regular subgraph' if r2 else 'HAS one !!!'}")
        out.append(f"  glucose4: {'SAT !!!' if sat else 'UNSAT'}; DRAT proof {len(proof)} lines, "
                   f"RUP check: {'OK' if ok else 'FAILED'} ({nl} lemmas checked, {msg}); "
                   f"CNF {nv} vars, {len(cl)} clauses")
        assert r1 is None and r2 and not sat and ok
    out.append("")
    out.append("construction steps (each new vertex has degree 3 when added):")
    out += ["  " + s for s in steps]
    text = "\n".join(out) + "\n"
    open(os.path.join(E, "data", "WITNESSES.txt"), "w").write(text)
    print(text)


if __name__ == "__main__":
    main()
