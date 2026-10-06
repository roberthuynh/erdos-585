"""check_deep.py: independent certificates for the counter-instances to the port core lemma.
For each graph: degrees, edge count, sparsity by brute force over all vertex subsets, and SAT
(pysat CaDiCaL, own encoding) for: 4-factor of G, of every G - y, and existence of a nonempty
4-regular subgraph (witness re-validated). Classes:
  P4: e = 3n - 4, proper U with |U| >= 2 span <= 3|U| - 5
  P3: e = 3n - 3, proper U with |U| >= 2 span <= 3|U| - 4
  QB5: bipartite, e = 3n - 5, proper U with |U| >= 3 span <= 3|U| - 6 (ports only claim)
Exit 1 if any claim fails."""
import sys, json, itertools
from pysat.solvers import Cadical153
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
from p4lib import *

def edges_of(A, n, mask):
    return [(i, j) for i in range(n) for j in range(i + 1, n)
            if (mask >> i) & 1 and (mask >> j) & 1 and (A[i] >> j) & 1]

def has_4factor(A, n, mask):
    E = edges_of(A, n, mask)
    pool = IDPool(); x = {e: pool.id(("x", e)) for e in E}
    cnf = []
    for v in verts(mask):
        lits = [x[e] for e in E if v in e]
        if len(lits) < 4: return False, None
        enc = CardEnc.equals(lits=lits, bound=4, vpool=pool, encoding=EncType.seqcounter)
        cnf += enc.clauses
    with Cadical153(bootstrap_with=cnf) as s:
        if not s.solve(): return False, None
        m = set(l for l in s.get_model() if l > 0)
        F = [e for e in E if x[e] in m]
    for v in verts(mask):
        assert sum(1 for e in F if v in e) == 4
    return True, F

def has_quartic(A, n):
    V = (1 << n) - 1
    E = edges_of(A, n, V)
    pool = IDPool(); x = {e: pool.id(("x", e)) for e in E}; y = {v: pool.id(("y", v)) for v in range(n)}
    cnf = [[y[v] for v in range(n)]]
    for v in range(n):
        lits = [x[e] for e in E if v in e]
        for l in lits: cnf.append([-l, y[v]])
        if len(lits) < 4: cnf.append([-y[v]]); continue
        cnf += CardEnc.atmost(lits=lits, bound=4, vpool=pool, encoding=EncType.seqcounter).clauses
        for cl in CardEnc.atleast(lits=lits, bound=4, vpool=pool, encoding=EncType.seqcounter).clauses:
            cnf.append(cl + [-y[v]])
    with Cadical153(bootstrap_with=cnf) as s:
        if not s.solve(): return False, None
        m = set(l for l in s.get_model() if l > 0)
        F = [e for e in E if x[e] in m]
    degs = {}
    for (i, j) in F: degs[i] = degs.get(i, 0) + 1; degs[j] = degs.get(j, 0) + 1
    assert F and all(d == 4 for d in degs.values())
    return True, F

def sparse_ok(A, n, c, minsize):
    V = (1 << n) - 1
    worst = None
    for U in range(1, V):
        k = pc(U)
        if k < minsize: continue
        eU = e_in(A, U)
        if eU > 3 * k - c - 1: return False, U
    return True, None

def bipartite(A, n):
    col = [-1] * n
    for s0 in range(n):
        if col[s0] >= 0: continue
        col[s0] = 0; st = [s0]
        while st:
            u = st.pop()
            for v in verts(A[u]):
                if col[v] < 0: col[v] = 1 - col[u]; st.append(v)
                elif col[v] == col[u]: return None
    return col

CASES = [
    ("P4", 4, 2, "HCXf~z{"), ("P4", 4, 2, "JCOfuzsnCf_"),
    ("P4", 4, 2, "K?AFfrw^Fw^_"), ("P4", 4, 2, "K?AFbx{^Fw^_"), ("P4", 4, 2, "K?ABvbw~Fw^_"),
    ("P4", 4, 2, "K?ABrrw~Fw^_"), ("P4", 4, 2, "K?ABvrw|Fw^_"), ("P4", 4, 2, "K?ABvrw^Fw^_"),
    ("P4", 4, 2, "K?AFvrw^Bw^_"), ("P4", 4, 2, "K?AFvrs}Bw^_"), ("P4", 4, 2, "K?B@nrw}Fw^O"),
    ("P3", 3, 2, "K?ABvrw~Fw^_"), ("P3", 3, 2, "K?AFvrw^Fw^_"),
    ("QB5", 5, 3, "N???FbKickNo^_^_No?"), ("QB5", 5, 3, "N???FaM{C[No^_^_No?"), ("QB5", 5, 3, "N???FaMyCkNo^_^_No?"),
]

def main():
    results = []; fail = 0
    for (cls, c, minsize, s) in CASES:
        n, A = g6decode(s); V = (1 << n) - 1
        degs = [pc(a) for a in A]; e = sum(degs) // 2
        r = dict(cls=cls, g6=s, n=n, e=e, maxdeg=max(degs), mindeg=min(degs))
        ok = max(degs) <= 6 and min(degs) >= 4 and e == 3 * n - c
        sp, Ubad = sparse_ok(A, n, c, minsize); r["sparse"] = sp; ok &= sp
        if cls == "QB5":
            col = bipartite(A, n); r["bipartite"] = col is not None; ok &= col is not None
        g4, _ = has_4factor(A, n, V); r["G_has_4factor"] = g4; ok &= not g4
        good = []
        for yv in range(n):
            if cls == "QB5" and degs[yv] == 6: continue
            f, _ = has_4factor(A, n, V & ~(1 << yv))
            if f: good.append(yv)
        r["good_vertices_checked"] = good; ok &= (good == [])
        q, F = has_quartic(A, n); r["has_quartic"] = q
        r["quartic_witness_vertices"] = sorted(set(v for ed in F for v in ed)) if q else None
        r["claims_ok"] = bool(ok)
        if not ok: fail += 1
        results.append(r)
        print(json.dumps(r))
    json.dump(results, open("data/out_deep.json", "w"), indent=1)
    print("FAILURES", fail)
    sys.exit(1 if fail else 0)

main()
