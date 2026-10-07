"""SAT check of the one-crossing step at a port of a C1-type instance (c1type lane).

Setting (NOTES.md §1): X is a smallest W1b counterexample of C1 type on n vertices, y a good port,
Y = X - y with classes P = W - y and Q = U (|P| = |Q| = m/2, m = n - 1), F a 4-factor of Y with bad
pair {A, B}, c_F(A) = 1, e1 = p1 q' (p1 in A_P) and e2 = p' q1 (q1 in A_Q) the F-edges across.
H = Y - F. D_Y(q) = [q in N(y)] + [q = u1] on Q; D_Y(P) = D_Y(Q) = d = 1 + deg y.

Model: the side A is fixed (K44 - p1q1, or a pair-free 5+5 side given by the complement Fbar of F[A]
and H[A] within Fbar); F[B], H[B], the interface H-edges, N(y) on Q and the position of u1 are
variables. Constraints (each a fact proved in NOTES.md):
  * F[B] 4-regular except degree 3 at p', q'; F, H disjoint;
  * every Q-vertex q: (H-degree of q) + [q in N(y)] + [q = u1] = 2;  every P-vertex: H-degree <= 2;
  * |N(y)| = deg y, exactly one u1;
  * level 'side': B 5+5 is pair-free (rules R1-R3 of NOTES §4); B 6+6 / 7+7 has no K44 in X[B] and
    e(S) <= 3|S| - 6 for S inside B with 3 <= |S| (|S| <= 14 <= 17, Prop 5 + L5);
  * level 'y' adds: no K44 in X[B + y]; e(S) + |N(y) cap S| <= 3(|S| + 1) - 6 for S inside B,
    2 <= |S| (|S + y| <= 15 <= 17);
  * (star) no one-crossing cycle, encoded by closure variables of D(F)[B] as in theory/lemmaB_sat.py.
Usage: python c1_sat.py [n ...]   (default 19 21 23)."""
import itertools, sys, time
from pysat.formula import IDPool
from pysat.card import CardEnc, EncType
from pysat.solvers import Cadical153


def fbar_config(name):
    if name == 'alpha':
        return [(0, 0), (0, 1), (1, 0), (2, 2), (3, 3), (4, 4)]
    return [(0, 1), (0, 2), (1, 0), (2, 0), (3, 3), (4, 4)]


def pairfree55(cfg, HA):
    """Rules R1-R3 (check_aside.out): a 5+5 side is pair-free iff H avoids p1q1, does not meet both
    p1 and q1, and (beta) does not contain both matching edges."""
    HA = set(HA)
    if (0, 0) in HA:
        return False
    if any(p == 0 for (p, q) in HA) and any(q == 0 for (p, q) in HA):
        return False
    if cfg == 'beta' and {(3, 3), (4, 4)} <= HA:
        return False
    return True


def reach_A(aP, aQ, FA, HA):
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
        for yy in range(aQ):
            out[(x, yy)] = yy in seenQ
    return out


def build(n, degy, Aspec, bP, failure=True, level='y', qfree=False):
    aP, aQ, FA, HA = Aspec
    bQ = bP
    assert 2 * (aP + bP) == n - 1
    pool = IDPool()
    cl = []

    def card(lits, k, kind):
        lits = list(lits)
        if kind == 'le':
            if k < 0:
                cl.append([]); return
            if len(lits) <= k:
                return
            cl.extend(CardEnc.atmost(lits=lits, bound=k, vpool=pool, encoding=EncType.seqcounter).clauses)
        elif kind == 'eq':
            if k < 0 or k > len(lits):
                cl.append([]); return
            if len(lits) == 0:
                return
            cl.extend(CardEnc.equals(lits=lits, bound=k, vpool=pool, encoding=EncType.seqcounter).clauses)
        else:
            if k <= 0:
                return
            if k > len(lits):
                cl.append([]); return
            cl.extend(CardEnc.atleast(lits=lits, bound=k, vpool=pool, encoding=EncType.seqcounter).clauses)

    f = {(p, q): pool.id(('f', p, q)) for p in range(bP) for q in range(bQ)}
    h = {(p, q): pool.id(('h', p, q)) for p in range(bP) for q in range(bQ)}
    xe = {(p, q): pool.id(('x', p, q)) for p in range(bP) for q in range(bQ)}
    for k in f:
        cl.append([-f[k], -h[k]])
        cl.append([-xe[k], f[k], h[k]]); cl.append([xe[k], -f[k]]); cl.append([xe[k], -h[k]])
    u = {(yy, xp): pool.id(('u', yy, xp)) for yy in range(aQ) for xp in range(bP) if (yy, xp) != (0, 0)}
    w = {(x, yp): pool.id(('w', x, yp)) for x in range(aP) for yp in range(bQ) if (x, yp) != (0, 0)}
    ny = {(s, q): pool.id(('ny', s, q)) for s in 'AB' for q in range(aQ if s == 'A' else bQ)}
    uu = {(s, q): pool.id(('uu', s, q)) for s in 'AB' for q in range(aQ if s == 'A' else bQ)}
    # F[B] degrees
    for p in range(bP):
        card([f[(p, q)] for q in range(bQ)], 4 - (1 if p == 0 else 0), 'eq')
    for q in range(bQ):
        card([f[(p, q)] for p in range(bP)], 4 - (1 if q == 0 else 0), 'eq')
    hAP = [sum(1 for (p, q) in HA if p == x) for x in range(aP)]
    hAQ = [sum(1 for (p, q) in HA if q == yy) for yy in range(aQ)]
    if not qfree:
        # Q-vertices: H-degree + ny + uu = 2
        for yy in range(aQ):
            card([u[(yy, xp)] for xp in range(bP) if (yy, xp) in u] + [ny[('A', yy)], uu[('A', yy)]],
                 2 - hAQ[yy], 'eq')
        for q in range(bQ):
            card([h[(p, q)] for p in range(bP)] + [w[(x, q)] for x in range(aP) if (x, q) in w]
                 + [ny[('B', q)], uu[('B', q)]], 2, 'eq')
    else:
        # relaxed: every Q-vertex has H-degree <= 2, and e(H) = m - d (so D_Y(Q) = D_Y(P) = d)
        assert level in ('none', 'side', 'side0')
        for yy in range(aQ):
            card([u[(yy, xp)] for xp in range(bP) if (yy, xp) in u], 2 - hAQ[yy], 'le')
        for q in range(bQ):
            card([h[(p, q)] for p in range(bP)] + [w[(x, q)] for x in range(aP) if (x, q) in w], 2, 'le')
        card(list(h.values()) + list(u.values()) + list(w.values()), (n - 1) - (1 + degy) - len(HA), 'eq')
    # P-vertices: H-degree <= 2
    for x in range(aP):
        card([w[(x, yp)] for yp in range(bQ) if (x, yp) in w], 2 - hAP[x], 'le')
    for p in range(bP):
        card([h[(p, q)] for q in range(bQ)] + [u[(yy, p)] for yy in range(aQ) if (yy, p) in u], 2, 'le')
    if not qfree:
        card(list(ny.values()), degy, 'eq')
        card(list(uu.values()), 1, 'eq')
    # side constraints on B
    if level == 'side0' and bP == 5:
        card(list(h.values()), 2, 'le')                                  # only e_H(B) <= 2
    if level in ('side', 'y'):
        if bP == 5:
            hl = h
            cl.append([-hl[(0, 0)]])                                     # R1
            for q in range(1, bQ):
                for p in range(1, bP):
                    cl.append([-hl[(0, q)], -hl[(p, 0)]])               # R2
            gen = [(p, q) for p in range(1, bP) for q in range(1, bQ)]
            for e1_, e2_ in itertools.combinations(gen, 2):
                if e1_[0] != e2_[0] and e1_[1] != e2_[1]:
                    cl.append([-f[(0, 0)], -hl[e1_], -hl[e2_]])         # R3 (beta: p'q' in F)
            card(list(h.values()), 2, 'le')
        else:
            for SP in itertools.combinations(range(bP), 4):
                for SQ in itertools.combinations(range(bQ), 4):
                    cl.append([-xe[(p, q)] for p in SP for q in SQ])
            for a in range(1, bP + 1):
                for b in range(1, bQ + 1):
                    if a + b < 3 or (a - 3) * (b - 3) < 4:
                        continue
                    for SP in itertools.combinations(range(bP), a):
                        for SQ in itertools.combinations(range(bQ), b):
                            card([xe[(p, q)] for p in SP for q in SQ], 3 * (a + b) - 6, 'le')
    if level == 'k44p':
        # proof-faithful level for A = K44 - e (PAPER §4.1, n = 23): no K44 in X[B] or X[B + w], and
        # (1.2) only for the sets it is used on: |S_P| >= 5, |S_Q| in {5, 6}, |S_Q| <= |S_P| + 1
        for SP in itertools.combinations(range(bP), 4):
            for SQ in itertools.combinations(range(bQ), 4):
                cl.append([-xe[(p, q)] for p in SP for q in SQ])
        for SP in itertools.combinations(range(bP), 3):
            for SQ in itertools.combinations(range(bQ), 4):
                cl.append([-xe[(p, q)] for p in SP for q in SQ] + [-ny[('B', q)] for q in SQ])
        for a in range(5, bP + 1):
            for b in (5, 6):
                if b > a + 1 or b > bQ:
                    continue
                for SP in itertools.combinations(range(bP), a):
                    for SQ in itertools.combinations(range(bQ), b):
                        card([xe[(p, q)] for p in SP for q in SQ] + [ny[('B', q)] for q in SQ],
                             3 * (a + b) - 3, 'le')
    if level == 'y':
        # K44 through y: y plus 3 B_P vertices, 4 B_Q vertices all adjacent to y
        for SP in itertools.combinations(range(bP), 3):
            for SQ in itertools.combinations(range(bQ), 4):
                cl.append([-xe[(p, q)] for p in SP for q in SQ] + [-ny[('B', q)] for q in SQ])
        # sparsity with y: e(S) + |N(y) cap S_Q| <= 3(|S|+1) - 6 = 3|S| - 3
        for a in range(0, bP + 1):
            for b in range(1, bQ + 1):
                if a + b < 2:
                    continue
                if a * b + b <= 3 * (a + b) - 3:
                    continue
                for SP in itertools.combinations(range(bP), a):
                    for SQ in itertools.combinations(range(bQ), b):
                        card([xe[(p, q)] for p in SP for q in SQ] + [ny[('B', q)] for q in SQ],
                             3 * (a + b) - 3, 'le')
    # closure variables of D(F)[B]
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
        for (yy, xp), uv in u.items():
            for (x, yp), wv in w.items():
                if rA[(x, yy)]:
                    cl.append([-uv, -wv, -c[(xp, 'Q', yp)]])
    return cl, (f, h, u, w, ny, uu)


def solve(cl):
    s = Cadical153(bootstrap_with=cl)
    r = s.solve()
    m = s.get_model() if r else None
    s.delete()
    return r, m


def specs_55(only_pairfree=True):
    for cfg in ('alpha', 'beta'):
        fb = fbar_config(cfg)
        FA = [(p, q) for p in range(5) for q in range(5) if (p, q) not in fb]
        for k in range(0, 3):
            for HA in itertools.combinations(fb, k):
                if only_pairfree and not pairfree55(cfg, HA):
                    continue
                yield '%s H%s' % (cfg, list(HA)), (5, 5, FA, list(HA))


def spec_k44():
    FA = [(p, q) for p in range(4) for q in range(4) if (p, q) != (0, 0)]
    return 'K44-e', (4, 4, FA, [])


def cases_for(n, allA=False):
    m = n - 1
    out = []
    name, k44 = spec_k44()
    out.append(('n=%d A=K44-e B=%d+%d' % (n, (m - 8) // 2, (m - 8) // 2), k44, (m - 8) // 2))
    if m - 10 >= 10:
        for nm, sp in specs_55(not allA):
            out.append(('n=%d A=5+5 %s B=%d+%d' % (n, nm, (m - 10) // 2, (m - 10) // 2), sp, (m - 10) // 2))
    return out


def main():
    ns = [int(a) for a in sys.argv[1:]] or [19, 21, 23]
    tot = 0; sat = 0
    for n in ns:
        for (label, sp, bP) in cases_for(n):
            for degy in (4, 5):
                t0 = time.time()
                res = {}
                for lev in ('none', 'side', 'y'):
                    cl, _ = build(n, degy, sp, bP, failure=True, level=lev)
                    res[lev] = solve(cl)[0]
                cl0, _ = build(n, degy, sp, bP, failure=False, level='y')
                ctrl = solve(cl0)[0]
                print('%s deg y=%d: (star) with constraints none/side/y: %s/%s/%s; control (no star, level y): %s  [%.1fs]' % (
                    label, degy, *['SAT' if res[l] else 'UNSAT' for l in ('none', 'side', 'y')],
                    'SAT' if ctrl else 'UNSAT', time.time() - t0), flush=True)
                tot += 1; sat += bool(res['y'])
    print('configurations', tot, 'SAT at level y', sat)


if __name__ == '__main__':
    main()


def one(n, idx, degy, lev, failure=True):
    cases = cases_for(n)
    label, sp, bP = cases[idx]
    t0 = time.time()
    cl, _ = build(n, degy, sp, bP, failure=failure, level=lev)
    r = solve(cl)[0]
    print('%s deg y=%d level=%s star=%s: %s [%.1fs, %d clauses]' % (
        label, degy, lev, failure, 'SAT' if r else 'UNSAT', time.time() - t0, len(cl)), flush=True)
    return r


def one2(n, idx, degy, lev, failure=True, qfree=False, allA=False):
    cases = cases_for(n, allA)
    label, sp, bP = cases[idx]
    t0 = time.time()
    cl, _ = build(n, degy, sp, bP, failure=failure, level=lev, qfree=qfree)
    r = solve(cl)[0]
    print('%s deg y=%d level=%s star=%s qfree=%s: %s [%.1fs]' % (
        label, degy, lev, failure, qfree, 'SAT' if r else 'UNSAT', time.time() - t0), flush=True)
    return r
