"""Independent SAT cross-check of Lemma B (ADDENDUM-B.md) for n <= 22.

Model: the small side A of the bad pair is fixed (K_{4,4} - e, or a 5+5 side given by the complement
Fbar of F[A] (configuration alpha or beta) and a set H[A] of at most 2 edges of Fbar); the side B
(F[B], H[B]) and all H-edges between A and B are free variables. e1 = p1 q' and e2 = p' q1 are the
two F-edges across the cut. Constraints are exactly the facts the paper proof uses:
  * F[B] has degree 4 except at p' and q' (degree 3); F and H disjoint; every vertex has H-degree <= 2
    (so 4 <= deg <= 6); the number of H-edges is n - 4 (equivalently D(P) = D(Q) = 4);
  * B side 5+5 (n = 20 with A 5+5): e_H(B) <= 2 (pair-free 5+5 graphs have <= 21 edges);
  * B side 6+6 or 7+7: no K_{4,4} in X[B] (it has a pair), and e(S) <= 3|S| - 6 for every S inside B
    with (|S_P| - 3)(|S_Q| - 3) >= 4 (g(S) >= 12 for 3 <= |S| <= 17; smaller S satisfy it trivially);
  * no one-crossing cycle: for every E0 H-edge a = (y, x') and E1 H-edge b = (y', x) with x ~> y in
    D(F)[A], the vertex y' is outside a closed set of D(F)[B] that contains x' (closure variables).
UNSAT in every configuration = no configuration without a one-crossing cycle.
Controls: the same model with the failure clauses removed must be SAT; for the 6+6 / 7+7 sides the
model with the B-side constraints removed is also reported (expected SAT: the constraints are needed).
Usage: python lemmaB_sat.py  (prints one line per configuration and a summary)."""
import itertools, sys
from pysat.formula import IDPool
from pysat.card import CardEnc, EncType
from pysat.solvers import Cadical153


def fbar_config(name):
    # A_P = P0..P4 (p1 = P0), A_Q = Q0..Q4 (q1 = Q0)
    if name == 'alpha':   # path y* - p1 - q1 - x*, plus a matching
        return [(0, 0), (0, 1), (1, 0), (2, 2), (3, 3), (4, 4)]
    if name == 'beta':    # paths y1 - p1 - y2 and x0 - q1 - x1, plus a matching
        return [(0, 1), (0, 2), (1, 0), (2, 0), (3, 3), (4, 4)]
    raise ValueError(name)


def reach_A(aP, aQ, FA, HA):
    """reachA[x][y]: x ~> y in D(F)[A] (F-arcs P->Q, H-arcs Q->P)."""
    out = {}
    for x in range(aP):
        seenP, seenQ = {x}, set()
        stack = [('P', x)]
        while stack:
            side, v = stack.pop()
            if side == 'P':
                for (p, q) in FA:
                    if p == v and q not in seenQ:
                        seenQ.add(q); stack.append(('Q', q))
            else:
                for (p, q) in HA:
                    if q == v and p not in seenP:
                        seenP.add(p); stack.append(('P', p))
        for y in range(aQ):
            out[(x, y)] = y in seenQ
    return out


def build_and_solve(n, Aspec, bP, failure=True, bconstraints=True, relaxed=False):
    """Aspec = (aP, aQ, FA, HA) with p1 = P0, q1 = Q0. B has bP + bP vertices, p' = BP0, q' = BQ0."""
    aP, aQ, FA, HA = Aspec
    bQ = bP
    pool = IDPool()
    cl = []
    def card_le(lits, k):
        if k < 0:
            cl.append([]); return
        if len(lits) <= k:
            return
        cl.extend(CardEnc.atmost(lits=lits, bound=k, vpool=pool, encoding=EncType.seqcounter).clauses)
    def card_eq(lits, k):
        if k < 0 or k > len(lits):
            cl.append([]); return
        cl.extend(CardEnc.equals(lits=lits, bound=k, vpool=pool, encoding=EncType.seqcounter).clauses)
    f = {(p, q): pool.id(('f', p, q)) for p in range(bP) for q in range(bQ)}
    h = {(p, q): pool.id(('h', p, q)) for p in range(bP) for q in range(bQ)}
    xe = {(p, q): pool.id(('x', p, q)) for p in range(bP) for q in range(bQ)}
    for k in f:
        cl.append([-f[k], -h[k]])
        cl.append([-xe[k], f[k], h[k]]); cl.append([xe[k], -f[k]]); cl.append([xe[k], -h[k]])
    # interface H-edges: u[(y, x')] (A_Q - B_P, not e2 = (q1, p')), w[(x, y')] (A_P - B_Q, not e1 = (p1, q'))
    u = {(y, xp): pool.id(('u', y, xp)) for y in range(aQ) for xp in range(bP) if (y, xp) != (0, 0)}
    w = {(x, yp): pool.id(('w', x, yp)) for x in range(aP) for yp in range(bQ) if (x, yp) != (0, 0)}
    # F[B] degrees
    for p in range(bP):
        card_eq([f[(p, q)] for q in range(bQ)], 4 - (1 if p == 0 else 0))
    for q in range(bQ):
        card_eq([f[(p, q)] for p in range(bP)], 4 - (1 if q == 0 else 0))
    # H-degrees <= 2
    hAP = [sum(1 for (p, q) in HA if p == x) for x in range(aP)]
    hAQ = [sum(1 for (p, q) in HA if q == y) for y in range(aQ)]
    for x in range(aP):
        card_le([w[(x, yp)] for yp in range(bQ) if (x, yp) in w], 2 - hAP[x])
    for y in range(aQ):
        card_le([u[(y, xp)] for xp in range(bP) if (y, xp) in u], 2 - hAQ[y])
    for p in range(bP):
        card_le([h[(p, q)] for q in range(bQ)] + [u[(y, p)] for y in range(aQ) if (y, p) in u], 2)
    for q in range(bQ):
        card_le([h[(p, q)] for p in range(bP)] + [w[(x, q)] for x in range(aP) if (x, q) in w], 2)
    # total H-edges = n - 4 (relaxed test mode: only ask for at least one E0H and one E1H edge)
    if relaxed:
        k = int(relaxed)
        cl.extend(CardEnc.atleast(lits=list(u.values()), bound=k, vpool=pool, encoding=EncType.seqcounter).clauses)
        cl.extend(CardEnc.atleast(lits=list(w.values()), bound=k, vpool=pool, encoding=EncType.seqcounter).clauses)
    else:
        card_eq(list(h.values()) + list(u.values()) + list(w.values()), n - 4 - len(HA))
    if bconstraints:
        if bP == 5:
            card_le(list(h.values()), 2)
        else:
            for SP in itertools.combinations(range(bP), 4):
                for SQ in itertools.combinations(range(bQ), 4):
                    cl.append([-xe[(p, q)] for p in SP for q in SQ])
            for a in range(1, bP + 1):
                for b in range(1, bQ + 1):
                    if a + b < 3 or (a - 3) * (b - 3) < 4:   # |S| >= 3; other S satisfy it trivially
                        continue
                    for SP in itertools.combinations(range(bP), a):
                        for SQ in itertools.combinations(range(bQ), b):
                            card_le([xe[(p, q)] for p in SP for q in SQ], 3 * (a + b) - 6)
    # closure variables: c[(x', ('P', p))], c[(x', ('Q', q))]
    c = {}
    for xp in range(bP):
        for p in range(bP):
            c[(xp, 'P', p)] = pool.id(('c', xp, 'P', p))
        for q in range(bQ):
            c[(xp, 'Q', q)] = pool.id(('c', xp, 'Q', q))
        cl.append([c[(xp, 'P', xp)]])
        for p in range(bP):
            for q in range(bQ):
                cl.append([-c[(xp, 'P', p)], -f[(p, q)], c[(xp, 'Q', q)]])
                cl.append([-c[(xp, 'Q', q)], -h[(p, q)], c[(xp, 'P', p)]])
    if failure:
        rA = reach_A(aP, aQ, FA, HA)
        for (y, xp), uv in u.items():
            for (x, yp), wv in w.items():
                if rA[(x, y)]:
                    cl.append([-uv, -wv, -c[(xp, 'Q', yp)]])
    s = Cadical153(bootstrap_with=cl)
    res = s.solve()
    model = s.get_model() if res else None
    s.delete()
    return res, model, (u, w, f, h)


def specs_55():
    for cfg in ('alpha', 'beta'):
        fb = fbar_config(cfg)
        FA = [(p, q) for p in range(5) for q in range(5) if (p, q) not in fb]
        for k in range(0, 3):
            for HA in itertools.combinations(fb, k):
                yield '%s H%s' % (cfg, list(HA)), (5, 5, FA, list(HA))


def spec_k44():
    FA = [(p, q) for p in range(4) for q in range(4) if (p, q) != (0, 0)]
    return 'K44-e', (4, 4, FA, [])


def main():
    cases = []
    for name, sp in specs_55():
        cases.append(('n=20 A=5+5 B=5+5 ' + name, 20, sp, 5))
    _, k44 = spec_k44()
    cases.append(('n=20 A=K44-e B=6+6', 20, k44, 6))
    for name, sp in specs_55():
        cases.append(('n=22 A=5+5 B=6+6 ' + name, 22, sp, 6))
    cases.append(('n=22 A=K44-e B=7+7', 22, k44, 7))
    nsat = 0
    for (label, n, sp, bP) in cases:
        r, _, _ = build_and_solve(n, sp, bP)
        r0, _, _ = build_and_solve(n, sp, bP, failure=False)
        line = '%s: no-one-crossing model %s; control without failure clauses %s' % (
            label, 'SAT' if r else 'UNSAT', 'SAT' if r0 else 'UNSAT')
        if bP >= 6:
            r1, _, _ = build_and_solve(n, sp, bP, bconstraints=False)
            line += '; without B-side constraints %s' % ('SAT' if r1 else 'UNSAT')
        print(line, flush=True)
        nsat += bool(r)
    print('configurations', len(cases), 'with a model', nsat)


if __name__ == '__main__':
    main()
