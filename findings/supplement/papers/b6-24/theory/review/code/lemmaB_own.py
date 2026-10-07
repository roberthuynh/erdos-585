"""lemmaB_own.py (referee's own SAT model of Theorem B's case analysis; written without reading the
author's lemmaB_sat.py).

Setting (ADDENDUM-B section 1): bad pair {A, B}, c_F(A) = 1, e1 = p1 q' (p1 in A_P, q' in B_Q),
e2 = p' q1 (p' in B_P, q1 in A_Q). The A side is fixed:
  K44:  F[A] = X[A] = K44 - p1q1, H[A] empty;
  alpha/beta: F[A] = K55 - Fbar, Fbar in configuration (alpha) or (beta), H[A] a given subset of
  Fbar with at most 2 edges.
Unknowns: F[B], H[B], the H-edges E0H (A_Q - B_P) and E1H (A_P - B_Q).
Facts encoded (each holds in every smallest E4-type counterexample in this setting):
  F-degrees 4 (3 at p', q' inside B); every H-degree <= 2; exactly n - 4 H-edges (D(P) = D(Q) = 4);
  5+5 side B: e_H(B) <= 2 (PAPER Lemma 6.1(a) applied to B);
  6+6 / 7+7 side B (optional, flag bside): no K44 in X[B], and e(S) <= 3|S| - 6 for S in B with
  |S| >= 3 (sparsity plus Prop 5/L5), added lazily (cut loop).
(star): for every a = (y, x') in E0H and b = (x, y') in E1H, x reaches y in D_A (fixed) or x' does not
reach y' in D_B. "x' does not reach y'" is certified by a set closed under in-arcs of D_B that contains
y' and not x' (mode coreach, one vector per y'), or by a set closed under out-arcs containing x' and
not y' (mode reach, one vector per x').
Modes: full model; no-star control; relaxed-count test (k E0H and k E1H edges instead of the count)
with a BFS re-check of every decoded model; (star') of section 4.2 (pairs blocked by Fbar edges).
"""
import itertools
import sys
from collections import deque

from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
from pysat.solvers import Solver


def a_side(shape, HA):
    """Return A_P, A_Q, F_A (set of (x,y)), H_A (set of (x,y)), Fbar (set) ."""
    if shape == "K44":
        AP = ["p1", "x1", "x2", "x3"]; AQ = ["q1", "y1", "y2", "y3"]
        FA = {(x, y) for x in AP for y in AQ} - {("p1", "q1")}
        return AP, AQ, FA, set(), {("p1", "q1")}
    AP = ["p1", "x1", "x2", "x3", "x4"]; AQ = ["q1", "y1", "y2", "y3", "y4"]
    if shape == "alpha":
        # path y1 p1 q1 x1, matching x2y2, x3y3, x4y4
        Fbar = {("p1", "y1"), ("p1", "q1"), ("x1", "q1"), ("x2", "y2"), ("x3", "y3"), ("x4", "y4")}
    elif shape == "beta":
        # paths y1 p1 y2 and x1 q1 x2, matching x3y3, x4y4
        Fbar = {("p1", "y1"), ("p1", "y2"), ("x1", "q1"), ("x2", "q1"), ("x3", "y3"), ("x4", "y4")}
    else:
        raise ValueError(shape)
    FA = {(x, y) for x in AP for y in AQ} - Fbar
    assert set(HA) <= Fbar
    return AP, AQ, FA, set(HA), Fbar


def reach_table(AP, AQ, FA, HA):
    succ = {v: [] for v in AP + AQ}
    for (x, y) in FA:
        succ[x].append(y)
    for (x, y) in HA:
        succ[y].append(x)
    R = {}
    for x in AP:
        seen = {x}; dq = deque([x])
        while dq:
            u = dq.popleft()
            for w in succ[u]:
                if w not in seen:
                    seen.add(w); dq.append(w)
        for y in AQ:
            R[(x, y)] = y in seen
    return R


def build_and_solve(shape, n, HA, star="coreach", bside=True, relax_k=None, starprime=False,
                    solver_name="cd15", max_iter=2000, assume_e0=None):
    AP, AQ, FA, HAset, Fbar = a_side(shape, HA)
    a = len(AP); b = n // 2 - a
    BP = ["pp"] + ["u%d" % i for i in range(1, b)]
    BQ = ["qq"] + ["v%d" % i for i in range(1, b)]
    reachA = reach_table(AP, AQ, FA, HAset)
    pool = IDPool()
    f = {(u, v): pool.id(("f", u, v)) for u in BP for v in BQ}
    h = {(u, v): pool.id(("h", u, v)) for u in BP for v in BQ}
    e0 = {(y, u): pool.id(("e0", y, u)) for y in AQ for u in BP if not (y == "q1" and u == "pp")}
    e1 = {(x, v): pool.id(("e1", x, v)) for x in AP for v in BQ if not (x == "p1" and v == "qq")}
    xv = {(u, v): pool.id(("x", u, v)) for u in BP for v in BQ}
    cl = []

    def add_card(lits, k, kind):
        if kind == "eq":
            enc = CardEnc.equals(lits=lits, bound=k, vpool=pool, encoding=EncType.seqcounter)
        elif kind == "le":
            if k >= len(lits):
                return
            if k < 0:
                cl.append([]); return
            enc = CardEnc.atmost(lits=lits, bound=k, vpool=pool, encoding=EncType.seqcounter)
        else:
            if k <= 0:
                return
            enc = CardEnc.atleast(lits=lits, bound=k, vpool=pool, encoding=EncType.seqcounter)
        cl.extend(enc.clauses)

    for key in f:
        cl.append([-f[key], -h[key]])
        cl += [[-xv[key], f[key], h[key]], [-f[key], xv[key]], [-h[key], xv[key]]]
    for u in BP:
        add_card([f[(u, v)] for v in BQ], 3 if u == "pp" else 4, "eq")
    for v in BQ:
        add_card([f[(u, v)] for u in BP], 3 if v == "qq" else 4, "eq")
    hdegA = {w: 0 for w in AP + AQ}
    for (x, y) in HAset:
        hdegA[x] += 1; hdegA[y] += 1
    for u in BP:
        add_card([h[(u, v)] for v in BQ] + [e0[k] for k in e0 if k[1] == u], 2, "le")
    for v in BQ:
        add_card([h[(u, v)] for u in BP] + [e1[k] for k in e1 if k[1] == v], 2, "le")
    for x in AP:
        add_card([e1[k] for k in e1 if k[0] == x], 2 - hdegA[x], "le")
    for y in AQ:
        add_card([e0[k] for k in e0 if k[0] == y], 2 - hdegA[y], "le")
    allH = list(h.values()) + list(e0.values()) + list(e1.values())
    if relax_k is None:
        add_card(allH, n - 4 - len(HAset), "eq")
    else:
        add_card(list(e0.values()), relax_k, "ge")
        add_card(list(e1.values()), relax_k, "ge")
    if b == 5:
        add_card(list(h.values()), 2, "le")
    if b >= 6 and bside:
        for SP in itertools.combinations(BP, 4):
            for SQ in itertools.combinations(BQ, 4):
                cl.append([-xv[(u, v)] for u in SP for v in SQ])
    # reachability certificates in D_B
    Bv = BP + BQ
    cert = {}
    if star in ("coreach", "both"):
        d = {(t, w): pool.id(("d", t, w)) for t in BQ for w in Bv}
        for t in BQ:
            cl.append([d[(t, t)]])
            for u in BP:
                for v in BQ:
                    cl.append([-f[(u, v)], -d[(t, v)], d[(t, u)]])  # arc u->v, v in set => u in set
                    cl.append([-h[(u, v)], -d[(t, u)], d[(t, v)]])  # arc v->u, u in set => v in set
        cert["coreach"] = lambda xp, yq: d[(yq, xp)]
    if star in ("reach", "both"):
        c = {(s, w): pool.id(("c", s, w)) for s in BP for w in Bv}
        for s in BP:
            cl.append([c[(s, s)]])
            for u in BP:
                for v in BQ:
                    cl.append([-f[(u, v)], -c[(s, u)], c[(s, v)]])
                    cl.append([-h[(u, v)], -c[(s, v)], c[(s, u)]])
        cert["reach"] = lambda xp, yq: c[(xp, yq)]
    if star is not None:
        for (y, xp) in e0:
            for (x, yq) in e1:
                if reachA[(x, y)]:
                    for kname, fn in cert.items():
                        cl.append([-e0[(y, xp)], -e1[(x, yq)], -fn(xp, yq)])
    if starprime:
        # (star'): every pair has x y in Fbar or x' y' in Fbar_B (i.e. not an F-edge of B)
        for (y, xp) in e0:
            for (x, yq) in e1:
                if (x, y) not in Fbar:
                    cl.append([-e0[(y, xp)], -e1[(x, yq)], -f[(xp, yq)]])
    if assume_e0 is not None:
        # WLOG case split (symmetry of the model): force the E0H edge (y, x')
        cl.append([e0[tuple(assume_e0)]])
    s = Solver(name=solver_name, bootstrap_with=cl)
    it = 0; cuts = 0
    while True:
        it += 1
        ok = s.solve()
        if not ok:
            s.delete()
            return {"sat": False, "iters": it, "cuts": cuts}
        m = set(l for l in s.get_model() if l > 0)
        Xb = {(u, v) for (u, v) in xv if xv[(u, v)] in m}
        # lazy sparsity cuts
        added = 0
        if b >= 6 and bside:
            for r in range(3, 2 * b + 1):
                for S in itertools.combinations(Bv, r):
                    SP = [w for w in S if w in BP]; SQ = [w for w in S if w in BQ]
                    eS = sum(1 for u in SP for v in SQ if (u, v) in Xb)
                    if eS > 3 * r - 6:
                        lits = [xv[(u, v)] for u in SP for v in SQ]
                        enc = CardEnc.atmost(lits=lits, bound=3 * r - 6, vpool=pool, encoding=EncType.seqcounter)
                        s.append_formula(enc.clauses)
                        added += 1
                        if added >= 50:
                            break
                if added >= 50:
                    break
        if added:
            cuts += added
            if it > max_iter:
                s.delete()
                return {"sat": None, "iters": it, "cuts": cuts}
            continue
        # decode and verify
        F = {(u, v) for (u, v) in f if f[(u, v)] in m}
        H = {(u, v) for (u, v) in h if h[(u, v)] in m}
        E0 = [k for k in e0 if e0[k] in m]
        E1 = [k for k in e1 if e1[k] in m]
        s.delete()
        return {"sat": True, "iters": it, "cuts": cuts, "F": F, "H": H, "E0": E0, "E1": E1,
                "AP": AP, "AQ": AQ, "FA": FA, "HA": HAset, "BP": BP, "BQ": BQ}


def verify_model(res, n):
    """Independent re-check of a decoded model: degrees, counts, and BFS for one-crossing cycles."""
    AP, AQ, BP, BQ = res["AP"], res["AQ"], res["BP"], res["BQ"]
    FA, HA, F, H, E0, E1 = res["FA"], res["HA"], res["F"], res["H"], res["E0"], res["E1"]
    Fall = set(FA) | set(F) | {("p1", "qq"), ("pp", "q1")}
    Hall = set(HA) | set(H) | {(u, y) for (y, u) in E0} | set(E1)
    assert not (Fall & Hall)
    fdeg = {}; hdeg = {}
    for (p, q) in Fall:
        fdeg[p] = fdeg.get(p, 0) + 1; fdeg[q] = fdeg.get(q, 0) + 1
    for (p, q) in Hall:
        hdeg[p] = hdeg.get(p, 0) + 1; hdeg[q] = hdeg.get(q, 0) + 1
    V = AP + AQ + BP + BQ
    assert all(fdeg.get(v, 0) == 4 for v in V), "F not 4-regular"
    assert all(hdeg.get(v, 0) <= 2 for v in V), "H-degree > 2"
    # D^- : arcs P->Q along F minus e1,e2; Q->P along H
    succ = {v: [] for v in V}
    for (p, q) in Fall:
        if (p, q) in (("p1", "qq"), ("pp", "q1")):
            continue
        succ[p].append(q)
    for (p, q) in Hall:
        succ[q].append(p)
    Aset = set(AP + AQ)

    def reach(src, allowed):
        seen = {src}; dq = deque([src])
        while dq:
            u = dq.popleft()
            for w in succ[u]:
                if w in allowed and w not in seen:
                    seen.add(w); dq.append(w)
        return seen
    Bset = set(BP + BQ)
    found = False
    for (y, xp) in E0:
        RB = reach(xp, Bset)
        for (x, yq) in E1:
            if yq in RB and y in reach(x, Aset):
                found = True
    return {"hcount": len(Hall), "one_crossing": found}


def configs():
    out = []
    for n in (20, 22):
        out.append(("K44", n, ()))
        for shape in ("alpha", "beta"):
            _, _, _, _, Fbar = a_side(shape, ())
            Fb = sorted(Fbar)
            subsets = [()] + [(e,) for e in Fb] + list(itertools.combinations(Fb, 2))
            for HA in subsets:
                out.append((shape, n, HA))
    return out


def run_single(mode, idx, solver_name, assume_e0=None):
    shape, n, HA = configs()[idx]
    star = "reach" if mode == "full_reach" else "coreach"
    bside = mode != "nobside"
    r = build_and_solve(shape, n, HA, star=star, bside=bside, solver_name=solver_name, assume_e0=assume_e0)
    line = "idx=%d %s n=%d HA=%s mode=%s solver=%s assume=%s sat=%s iters=%d cuts=%d" % (
        idx, shape, n, list(HA), mode, solver_name, assume_e0, r["sat"], r["iters"], r["cuts"])
    if r["sat"]:
        line += " verify=%s" % verify_model(r, n)
    print(line, flush=True)


if __name__ == "__main__" and len(sys.argv) > 1 and sys.argv[1] == "single":
    ae = None
    if len(sys.argv) > 5:
        ae = tuple(sys.argv[5].split(","))
    run_single(sys.argv[2], int(sys.argv[3]), sys.argv[4], ae)
    sys.exit(0)

if __name__ == "__main__":
    mode = sys.argv[1] if len(sys.argv) > 1 else "full"
    print("mode", mode, flush=True)
    tot = {"sat": 0, "unsat": 0, "unknown": 0}
    for (shape, n, HA) in configs():
        if mode == "full":
            r = build_and_solve(shape, n, HA, star="coreach", bside=True)
        elif mode == "full_reach":
            r = build_and_solve(shape, n, HA, star="reach", bside=True)
        elif mode == "nobside":
            r = build_and_solve(shape, n, HA, star="coreach", bside=False)
        elif mode == "nostar":
            r = build_and_solve(shape, n, HA, star=None, bside=True)
        elif mode == "starprime":
            if not (n == 20 and shape != "K44"):
                continue
            r = build_and_solve(shape, n, HA, star=None, bside=True, starprime=True)
        elif mode.startswith("relax"):
            k = int(mode[5:])
            r = build_and_solve(shape, n, HA, star="coreach", bside=True, relax_k=k)
        else:
            raise SystemExit("bad mode")
        line = "%s n=%d HA=%s sat=%s iters=%d cuts=%d" % (shape, n, list(HA), r["sat"], r["iters"], r["cuts"])
        if r["sat"]:
            v = verify_model(r, n)
            line += " verify=%s" % v
            tot["sat"] += 1
        elif r["sat"] is False:
            tot["unsat"] += 1
        else:
            tot["unknown"] += 1
        print(line, flush=True)
    print("TOTAL", tot, flush=True)
