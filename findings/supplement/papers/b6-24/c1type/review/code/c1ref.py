#!/usr/bin/env python3
"""Referee's own SAT model for Theorem C3 of wave4/c1type/PAPER.md (written without reading c1_sat.py).

Setting: Y = X - w at a good port w, F a 4-factor of Y with bad pair {A, B}, A the smaller side.
A side fixed (K44 - p1q1, or a 5+5 side given by Fbar config and H[A]); B side: F[B] fixed (one
genbg class) or free; H[B], E0H, E1H, N(w) and the position of u1 are variables.

Indices: A_P = {0..a-1} with p1 = 0, A_Q = {0..a-1} with q1 = 0; B_P = {0..b-1} with p' = 0,
B_Q = {0..b-1} with q' = 0. e1 = p1 q', e2 = p' q1 are the two F-edges across.

Constraints (always): F[B] degrees 4 (3 at p', q'); H[B] disjoint from F[B];
Q-vertex q: H-degree + [q in N(w)] + [q = u1] = 2   (F2; option qfree replaces it);
P-vertex: H-degree <= 2; |N(w)| = deg w; exactly one u1.
(star): every (a, b) in E0H x E1H is A-blocked or B-blocked, with one closed-set certificate per
x' in B_P (closed under out-arcs of D_B, contains x'; it must avoid y'_b when (a, b) is not A-blocked).
B-side levels (comma list): eHB2 (e_H(B) <= 2), k44w (no K44 in X[B + w]), c55 (every 5+5 subgraph
of X[B] has <= 21 edges), r12 (lazy: e(S) + |N(w) & S| <= 3|S| - 3 for S in B with |S_P| >= 5 and
|S_Q| <= |B_Q| - 1), r12all (same for all S in B, |S| >= 2), sp12 (lazy: e(S) <= 3|S| - 6 for S in
B + w, |S| >= 3, i.e. F3 directly; valid only for n <= 18 + ... , used at n = 23 with |S| <= 15).
"""
import itertools
import sys
import time

from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
from pysat.solvers import Solver


# ---------------------------------------------------------------- graph6 (bipartite genbg output)
def parse_g6(s):
    s = s.strip()
    if s.startswith('>>graph6<<'):
        s = s[10:]
    n = ord(s[0]) - 63
    assert n < 63
    bits = []
    for ch in s[1:]:
        v = ord(ch) - 63
        for k in range(5, -1, -1):
            bits.append((v >> k) & 1)
    edges = set()
    k = 0
    for j in range(1, n):
        for i in range(j):
            if bits[k]:
                edges.add((i, j))
            k += 1
    return n, edges


def fb_from_genbg(line, b):
    """genbg n1 = n2 = b: vertices 0..b-1 class P, b..2b-1 class Q. Relabel so p' = 0, q' = 0
    (the unique degree-3 vertices)."""
    n, edges = parse_g6(line)
    assert n == 2 * b
    pairs = set()
    for (i, j) in edges:
        assert i < b <= j
        pairs.add((i, j - b))
    degP = [sum(1 for (k, j) in pairs if k == x) for x in range(b)]
    degQ = [sum(1 for (k, j) in pairs if j == y) for y in range(b)]
    assert sorted(degP) == [3] + [4] * (b - 1) and sorted(degQ) == [3] + [4] * (b - 1), (degP, degQ)
    p0 = degP.index(3)
    q0 = degQ.index(3)
    permP = [p0] + [x for x in range(b) if x != p0]   # new index -> old
    permQ = [q0] + [y for y in range(b) if y != q0]
    invP = {old: new for new, old in enumerate(permP)}
    invQ = {old: new for new, old in enumerate(permQ)}
    return frozenset((invP[k], invQ[j]) for (k, j) in pairs)


# ---------------------------------------------------------------- A sides
def side_k44():
    a = 4
    FA = frozenset((x, y) for x in range(a) for y in range(a) if (x, y) != (0, 0))
    return dict(name='K44-e', a=a, FA=FA, HA=frozenset())


def fbar_config(kind):
    # 5+5: p1 = 0, q1 = 0 (P- and Q-index 0)
    if kind == 'alpha':  # path y* p1 q1 x*, y* = Q1, x* = P1, matching (2,2) (3,3) (4,4)
        return frozenset([(0, 1), (0, 0), (1, 0), (2, 2), (3, 3), (4, 4)])
    if kind == 'beta':   # paths y1 p1 y2 (Q1, Q2), x0 q1 x1 (P1, P2), matching (3,3) (4,4)
        return frozenset([(0, 1), (0, 2), (1, 0), (2, 0), (3, 3), (4, 4)])
    raise ValueError(kind)


def sides_55():
    out = []
    for kind in ('alpha', 'beta'):
        fbar = sorted(fbar_config(kind))
        FA = frozenset((x, y) for x in range(5) for y in range(5)) - frozenset(fbar)
        for k in range(3):
            for HA in itertools.combinations(fbar, k):
                out.append(dict(name='%s H=%s' % (kind, list(HA)), a=5, FA=FA, HA=frozenset(HA)))
    return out


def reach_A(a, FA, HA):
    """reach[x][y]: x in A_P reaches y in A_Q in D_A (F-arcs P->Q, H-arcs Q->P)."""
    reach = {}
    for x0 in range(a):
        seenP, seenQ = {x0}, set()
        stack = [('P', x0)]
        while stack:
            side, v = stack.pop()
            if side == 'P':
                for y in range(a):
                    if (v, y) in FA and y not in seenQ:
                        seenQ.add(y)
                        stack.append(('Q', y))
            else:
                for x in range(a):
                    if (x, v) in HA and x not in seenP:
                        seenP.add(x)
                        stack.append(('P', x))
        reach[x0] = seenQ
    return reach


# ---------------------------------------------------------------- model
class Model:
    def __init__(self, side, b, degw, FB=None, star=True, f2=True, levels=(), solver='cadical195',
                 assume=None):
        self.side, self.b, self.degw, self.FB = side, b, degw, FB
        self.a = a = side['a']
        self.levels = set(levels)
        self.star, self.f2 = star, f2
        self.pool = IDPool()
        self.clauses = []
        P = self.pool
        FA, HA = side['FA'], side['HA']
        self.hAdegP = [sum(1 for (x, y) in HA if x == i) for i in range(a)]
        self.hAdegQ = [sum(1 for (x, y) in HA if y == i) for i in range(a)]
        # variables
        self.f = {}
        for k in range(b):
            for j in range(b):
                if FB is None:
                    self.f[k, j] = P.id(('f', k, j))
                else:
                    self.f[k, j] = True if (k, j) in FB else False
        self.h = {}
        for k in range(b):
            for j in range(b):
                if FB is not None and (k, j) in FB:
                    continue
                self.h[k, j] = P.id(('h', k, j))
                if FB is None:
                    self.clauses.append([-self.f[k, j], -self.h[k, j]])
        self.e0 = {(y, i): P.id(('e0', y, i)) for y in range(a) for i in range(b) if (y, i) != (0, 0)}
        self.e1 = {(x, j): P.id(('e1', x, j)) for x in range(a) for j in range(b) if (x, j) != (0, 0)}
        self.nw = {('A', y): P.id(('nwA', y)) for y in range(a)}
        self.nw.update({('B', j): P.id(('nwB', j)) for j in range(b)})
        self.u = {('A', y): P.id(('uA', y)) for y in range(a)}
        self.u.update({('B', j): P.id(('uB', j)) for j in range(b)})
        # F[B] degrees
        if FB is None:
            for k in range(b):
                self.card([self.f[k, j] for j in range(b)], 4 - (k == 0), 'eq')
            for j in range(b):
                self.card([self.f[k, j] for k in range(b)], 4 - (j == 0), 'eq')
        # Q H-degrees
        Qlits = {}
        for y in range(a):
            Qlits['A', y] = [self.e0[y, i] for i in range(b) if (y, i) in self.e0]
        for j in range(b):
            Qlits['B', j] = [self.h[k, j] for k in range(b) if (k, j) in self.h] + \
                            [self.e1[x, j] for x in range(a) if (x, j) in self.e1]
        relax = [lv for lv in self.levels if str(lv).startswith('relax')]
        if relax:  # encoding test: Q H-degree <= 2, at least k E0H and k E1H edges, nothing else
            k = int(relax[0][5:])
            for q, lits in Qlits.items():
                const = self.hAdegQ[q[1]] if q[0] == 'A' else 0
                self.card(lits, 2 - const, 'atmost')
            self.card([-v for v in self.e0.values()], len(self.e0) - k, 'atmost')
            self.card([-v for v in self.e1.values()], len(self.e1) - k, 'atmost')
        elif f2:
            for q, lits in Qlits.items():
                const = self.hAdegQ[q[1]] if q[0] == 'A' else 0
                self.card(lits + [self.nw[q], self.u[q]], 2 - const, 'eq')
            self.card(list(self.nw.values()), degw, 'eq')
            self.card(list(self.u.values()), 1, 'eq')
        else:  # qfree: Q H-degree <= 2 and total H = 2(a + b) - d
            allH = []
            for q, lits in Qlits.items():
                const = self.hAdegQ[q[1]] if q[0] == 'A' else 0
                self.card(lits, 2 - const, 'atmost')
                allH += lits
            d = 1 + degw
            self.card(allH, 2 * (a + b) - d - len(HA), 'eq')
        # P H-degrees <= 2
        for x in range(a):
            self.card([self.e1[x, j] for j in range(b) if (x, j) in self.e1], 2 - self.hAdegP[x], 'atmost')
        for k in range(b):
            lits = [self.h[k, j] for j in range(b) if (k, j) in self.h] + \
                   [self.e0[y, k] for y in range(a) if (y, k) in self.e0]
            self.card(lits, 2, 'atmost')
        # (star)
        self.reachA = reach_A(a, FA, HA)
        if star:
            self.R = {}
            for i in range(b):
                for k in range(b):
                    self.R[i, 'P', k] = P.id(('R', i, 'P', k))
                for j in range(b):
                    self.R[i, 'Q', j] = P.id(('R', i, 'Q', j))
                self.clauses.append([self.R[i, 'P', i]])
                for k in range(b):
                    for j in range(b):
                        fl = self.f[k, j]
                        if fl is True:
                            self.clauses.append([-self.R[i, 'P', k], self.R[i, 'Q', j]])
                        elif fl is not False:
                            self.clauses.append([-self.R[i, 'P', k], -fl, self.R[i, 'Q', j]])
                        if (k, j) in self.h:
                            self.clauses.append([-self.R[i, 'Q', j], -self.h[k, j], self.R[i, 'P', k]])
            for (y, i), ev in self.e0.items():
                for (x, j), bv in self.e1.items():
                    if y in self.reachA[x]:      # not A-blocked: must be B-blocked
                        self.clauses.append([-ev, -bv, -self.R[i, 'Q', j]])
        # B-side levels
        if 'eHB2' in self.levels:
            self.card(list(self.h.values()), 2, 'atmost')
        if 'k44w' in self.levels:
            Pside = [('B', k) for k in range(b)] + [('w', 0)]
            for SP in itertools.combinations(Pside, 4):
                for SQ in itertools.combinations(range(b), 4):
                    cl = []
                    for p in SP:
                        for j in SQ:
                            lit = self.edge_lit(p, j)
                            if lit is True:
                                continue
                            if lit is False:
                                cl = None
                                break
                            cl.append(-lit)
                        if cl is None:
                            break
                    if cl is None:
                        continue
                    self.clauses.append(cl)   # may be empty -> UNSAT
        if 'c55' in self.levels:
            for SP in itertools.combinations(range(b), 5):
                for SQ in itertools.combinations(range(b), 5):
                    self.atmost_edges(SP, SQ, 21, withw=False)
        if 'symA' in self.levels:
            # K44 - p1q1 side only: A_P - p1 and A_Q - q1 are interchangeable (D_A invariant).
            assert side['name'] == 'K44-e'
            vy = {y: [self.nw['A', y], self.u['A', y]] + [self.e0[y, i] for i in range(b)]
                  for y in range(1, a)}
            vx = {x: [self.e1[x, j] for j in range(b)] for x in range(1, a)}
            for y in range(1, a - 1):
                self.lex_geq(vy[y], vy[y + 1])
            for x in range(1, a - 1):
                self.lex_geq(vx[x], vx[x + 1])
        # WLOG symmetry split for the K44 - p1q1 side (free F[B]): some generic y has an E0H edge
        # (sum of h over A_Q - q1 >= 2 by F2); by S3 on A_Q - q1 it is y = 1; its B_P end is p'
        # (case y1pp) or, by S_{b-1} on B_P - p', vertex 1 (case y1b1). symG then breaks the residual
        # group (stabilizer of the case) by lex-leader constraints.
        cases = [lv for lv in self.levels if str(lv).startswith('case=')]
        groups = None
        if cases:
            assert side['name'] == 'K44-e' and FB is None and f2
            c = cases[0][5:]
            if c == 'y1pp':
                self.clauses.append([self.e0[1, 0]])
                groups = {'AQ': [2, 3], 'AP': [1, 2, 3], 'BP': list(range(1, b)), 'BQ': list(range(1, b))}
            elif c == 'y1b1':
                self.clauses.append([self.e0[1, 1]])
                groups = {'AQ': [2, 3], 'AP': [1, 2, 3], 'BP': list(range(2, b)), 'BQ': list(range(1, b))}
            else:
                raise ValueError(c)
        if 'symG' in self.levels:
            if groups is None:
                groups = {}
                if side['name'] == 'K44-e':
                    groups['AQ'] = list(range(1, a))
                    groups['AP'] = list(range(1, a))
                if FB is None:
                    groups['BP'] = list(range(1, b))
                    groups['BQ'] = list(range(1, b))
            self.add_symG(groups)
        u1cases = [lv for lv in self.levels if str(lv).startswith('u1=')]
        if u1cases:   # plain (complete) case split on the position of u1
            sd, ix = u1cases[0][3:].split(':')
            self.clauses.append([self.u[sd, int(ix)]])
        self.lazy = [lv for lv in ('r12', 'r12all', 'sp12') if lv in self.levels]
        self.cuts = 0
        self.solver_name = solver
        self.assume = assume or []

    def main_order(self):
        """Global order of the main variables (keys), most significant first."""
        a, b = self.a, self.b
        keys = []
        for k in range(b):
            for j in range(b):
                if self.f[k, j] is not True and self.f[k, j] is not False:
                    keys.append(('f', k, j))
                if (k, j) in self.h:
                    keys.append(('h', k, j))
        keys += [('e0', y, i) for y in range(a) for i in range(b) if (y, i) in self.e0]
        keys += [('e1', x, j) for x in range(a) for j in range(b) if (x, j) in self.e1]
        keys += [('nwB', j) for j in range(b)] + [('uB', j) for j in range(b)]
        keys += [('nwA', y) for y in range(a)] + [('uA', y) for y in range(a)]
        return keys

    def key_lit(self, key):
        t = key[0]
        if t == 'f':
            return self.f[key[1], key[2]]
        if t == 'h':
            return self.h[key[1], key[2]]
        if t == 'e0':
            return self.e0[key[1], key[2]]
        if t == 'e1':
            return self.e1[key[1], key[2]]
        if t == 'nwB':
            return self.nw['B', key[1]]
        if t == 'uB':
            return self.u['B', key[1]]
        if t == 'nwA':
            return self.nw['A', key[1]]
        if t == 'uA':
            return self.u['A', key[1]]
        raise KeyError(key)

    @staticmethod
    def swap_key(key, cls, i1, i2):
        """Image of a main-variable key under the transposition (i1 i2) of class cls in
        {'BP', 'BQ', 'AQ', 'AP'}."""
        sw = lambda v: i2 if v == i1 else (i1 if v == i2 else v)
        t = key[0]
        if cls == 'BP':
            if t in ('f', 'h'):
                return (t, sw(key[1]), key[2])
            if t == 'e0':
                return (t, key[1], sw(key[2]))
        elif cls == 'BQ':
            if t in ('f', 'h'):
                return (t, key[1], sw(key[2]))
            if t == 'e1':
                return (t, key[1], sw(key[2]))
            if t in ('nwB', 'uB'):
                return (t, sw(key[1]))
        elif cls == 'AQ':
            if t == 'e0':
                return (t, sw(key[1]), key[2])
            if t in ('nwA', 'uA'):
                return (t, sw(key[1]))
        elif cls == 'AP':
            if t == 'e1':
                return (t, sw(key[1]), key[2])
        return key

    def add_symG(self, groups):
        """Lex-leader constraints x >=_lex tau(x) (global order main_order) for the adjacent
        transpositions of each group {cls: [indices]} of interchangeable vertices. Sound for any set of
        groups that are symmetries of the (projected) solution set: the lex-max element of each orbit
        satisfies all of them."""
        order = self.main_order()
        pos = {key: n for n, key in enumerate(order)}
        n0 = len(self.clauses)
        self.symG_generators = []
        for cls, idx in groups.items():
            for t in range(len(idx) - 1):
                i1, i2 = idx[t], idx[t + 1]
                aff = [key for key in order if self.swap_key(key, cls, i1, i2) != key]
                aff.sort(key=lambda kk: pos[kk])
                u = [self.key_lit(kk) for kk in aff]
                v = [self.key_lit(self.swap_key(kk, cls, i1, i2)) for kk in aff]
                assert all(self.swap_key(kk, cls, i1, i2) in pos for kk in aff)
                self.lex_geq(u, v)
                self.symG_generators.append((cls, i1, i2))
        self.lex_clause_range = (n0, len(self.clauses))

    def lex_geq(self, u, v):
        """u >=_lex v (first coordinate most significant). a_k = 'prefix u[:k] == v[:k]'."""
        self.lexcount = getattr(self, 'lexcount', 0) + 1
        prev = None  # None means a_0 = True
        for k in range(len(u)):
            pre = [] if prev is None else [-prev]
            self.clauses.append(pre + [u[k], -v[k]])          # prefix equal -> u_k >= v_k
            if k == len(u) - 1:
                break
            nxt = self.pool.id(('lex', self.lexcount, k))
            self.clauses.append(pre + [-u[k], -v[k], nxt])    # equal at k (both 1) -> a_{k+1}
            self.clauses.append(pre + [u[k], v[k], nxt])      # equal at k (both 0) -> a_{k+1}
            prev = nxt

    def edge_lit(self, p, j):
        """literal for the X-edge between P-side vertex p (('B',k) or ('w',0)) and B_Q vertex j."""
        if p[0] == 'w':
            return self.nw['B', j]
        k = p[1]
        fl = self.f[k, j]
        if fl is True:
            return True
        if fl is False:
            return self.h.get((k, j), False)
        # f variable: edge = f or h; introduce aux
        v = self.pool.id(('edge', k, j))
        hv = self.h[k, j]
        self.clauses += [[-v, fl, hv], [v, -fl], [v, -hv]]
        return v

    def card(self, lits, bound, kind):
        const = sum(1 for l in lits if l is True)
        lits = [l for l in lits if l is not True and l is not False]
        bound -= const
        if kind == 'eq':
            if bound < 0 or bound > len(lits):
                self.clauses.append([])
                return
            enc = CardEnc.equals(lits=lits, bound=bound, vpool=self.pool, encoding=EncType.seqcounter) \
                if lits else None
        else:
            if bound < 0:
                self.clauses.append([])
                return
            if bound >= len(lits):
                return
            enc = CardEnc.atmost(lits=lits, bound=bound, vpool=self.pool, encoding=EncType.seqcounter)
        if enc is not None:
            self.clauses += enc.clauses

    def atmost_edges(self, SP, SQ, bound, withw=False, extra=()):
        lits = []
        for k in SP:
            for j in SQ:
                lit = self.edge_lit(('B', k), j)
                if lit is not False:
                    lits.append(lit)
        lits += list(extra)
        self.card(lits, bound, 'atmost')

    # ------------------------------------------------------------ solve with lazy cuts
    def solve(self, time_limit=None):
        t0 = time.time()
        s = Solver(name=self.solver_name, bootstrap_with=self.clauses)
        added = len(self.clauses)
        iters = 0
        while True:
            iters += 1
            ok = s.solve(assumptions=self.assume)
            if not ok:
                s.delete()
                return False, None, iters, time.time() - t0
            model = set(l for l in s.get_model() if l > 0)
            cfg = self.decode(model)
            viol = self.lazy_violations(cfg)
            if not viol:
                s.delete()
                return True, cfg, iters, time.time() - t0
            for (SP, SQ, kind) in viol:
                n0 = len(self.clauses)
                if kind == 'r12':
                    t, r = len(SP), len(SQ)
                    self.atmost_edges(SP, SQ, 3 * (t + r) - 3, extra=[self.nw['B', j] for j in SQ])
                elif kind == 'sp12w':   # S + w: e(S) + |N(w) & S| <= 3(|S|+1) - 6
                    t, r = len(SP), len(SQ)
                    self.atmost_edges(SP, SQ, 3 * (t + r + 1) - 6, extra=[self.nw['B', j] for j in SQ])
                elif kind == 'sp12':    # S itself: e(S) <= 3|S| - 6
                    t, r = len(SP), len(SQ)
                    self.atmost_edges(SP, SQ, 3 * (t + r) - 6)
                for cl in self.clauses[n0:]:
                    s.add_clause(cl)
                self.cuts += 1
            if time_limit and time.time() - t0 > time_limit:
                s.delete()
                return None, None, iters, time.time() - t0

    def decode(self, model):
        a, b = self.a, self.b
        val = lambda v: (v is True) or (v is not False and v in model)
        cfg = dict(a=a, b=b, FA=self.side['FA'], HA=self.side['HA'])
        cfg['FB'] = frozenset(kj for kj, v in self.f.items() if val(v))
        cfg['HB'] = frozenset(kj for kj, v in self.h.items() if val(v))
        cfg['E0'] = frozenset(k for k, v in self.e0.items() if val(v))
        cfg['E1'] = frozenset(k for k, v in self.e1.items() if val(v))
        cfg['NW'] = frozenset(k for k, v in self.nw.items() if val(v))
        cfg['U'] = [k for k, v in self.u.items() if val(v)]
        return cfg

    def lazy_violations(self, cfg):
        if not self.lazy:
            return []
        b = self.b
        X = set(cfg['FB']) | set(cfg['HB'])
        nwB = set(j for (s_, j) in cfg['NW'] if s_ == 'B')
        out = []
        for t in range(0, b + 1):
            for SP in itertools.combinations(range(b), t):
                for r in range(0, b + 1):
                    for SQ in itertools.combinations(range(b), r):
                        if t + r < 2:
                            continue
                        e = sum(1 for k in SP for j in SQ if (k, j) in X)
                        nwS = sum(1 for j in SQ if j in nwB)
                        if 'r12all' in self.lazy or ('r12' in self.lazy and t >= 5 and r <= b - 1):
                            if e + nwS > 3 * (t + r) - 3:
                                out.append((SP, SQ, 'r12'))
                                continue
                        if 'sp12' in self.lazy and t + r >= 3:
                            if e > 3 * (t + r) - 6:
                                out.append((SP, SQ, 'sp12'))
                                continue
                        if len(out) > 40:
                            return out
        return out


# ---------------------------------------------------------------- independent checker of a config
def check_config(cfg, degw, f2=True):
    """Re-check a decoded configuration from scratch; return dict with 'onecross' (bool)."""
    a, b = cfg['a'], cfg['b']
    FA, HA, FB, HB, E0, E1 = cfg['FA'], cfg['HA'], cfg['FB'], cfg['HB'], cfg['E0'], cfg['E1']
    # global vertex names
    F = set(('AP%d' % x, 'AQ%d' % y) for (x, y) in FA) | set(('BP%d' % k, 'BQ%d' % j) for (k, j) in FB)
    F |= {('AP0', 'BQ0'), ('BP0', 'AQ0')}
    H = set(('AP%d' % x, 'AQ%d' % y) for (x, y) in HA) | set(('BP%d' % k, 'BQ%d' % j) for (k, j) in HB)
    H |= set(('BP%d' % i, 'AQ%d' % y) for (y, i) in E0) | set(('AP%d' % x, 'BQ%d' % j) for (x, j) in E1)
    assert not (F & H)
    Pv = ['AP%d' % i for i in range(a)] + ['BP%d' % i for i in range(b)]
    Qv = ['AQ%d' % i for i in range(a)] + ['BQ%d' % i for i in range(b)]
    for v in Pv:
        assert sum(1 for (p, q) in F if p == v) == 4, v
        assert sum(1 for (p, q) in H if p == v) <= 2, v
    nw = set(('AQ%d' if s_ == 'A' else 'BQ%d') % i for (s_, i) in cfg['NW'])
    u1 = [('AQ%d' if s_ == 'A' else 'BQ%d') % i for (s_, i) in cfg['U']]
    for v in Qv:
        assert sum(1 for (p, q) in F if q == v) == 4, v
        hq = sum(1 for (p, q) in H if q == v)
        if f2:
            assert hq == 2 - (v in nw) - (v in u1), (v, hq)
        else:
            assert hq <= 2
    if f2:
        assert len(nw) == degw and len(u1) == 1
    # c_F(A) = 1
    Aset = set('AP%d' % i for i in range(a)) | set('AQ%d' % i for i in range(a))
    cross_F = [(p, q) for (p, q) in F if (p in Aset) != (q in Aset)]
    assert len(cross_F) == 2
    # digraph D(F) minus e1, e2
    arcs = {}
    for (p, q) in F:
        if (p in Aset) != (q in Aset):
            continue
        arcs.setdefault(p, []).append(q)
    for (p, q) in H:
        arcs.setdefault(q, []).append(p)

    def reach(src, inside):
        seen = {src}
        st = [src]
        while st:
            v = st.pop()
            for w_ in arcs.get(v, []):
                if w_ in inside and w_ not in seen:
                    seen.add(w_)
                    st.append(w_)
        return seen
    Bset = set('BP%d' % i for i in range(b)) | set('BQ%d' % i for i in range(b))
    onecross = False
    for (y, i) in E0:
        for (x, j) in E1:
            if ('AQ%d' % y) in reach('AP%d' % x, Aset) and ('BQ%d' % j) in reach('BP%d' % i, Bset):
                onecross = True
    # H-degree totals
    hP = {v: sum(1 for (p, q) in H if p == v) for v in Pv}
    hQ = {v: sum(1 for (p, q) in H if q == v) for v in Qv}
    D_P = sum(2 - hP[v] for v in Pv)
    D_Q = sum(2 - hQ[v] for v in Qv)
    return dict(onecross=onecross, D_P=D_P, D_Q=D_Q, eHB=len(HB), k0=len(E0), k1=len(E1))


def k44_in_Xbw(cfg):
    b = cfg['b']
    X = set(cfg['FB']) | set(cfg['HB'])
    nwB = set(j for (s_, j) in cfg['NW'] if s_ == 'B')
    rows = [frozenset(j for j in range(b) if (k, j) in X) for k in range(b)] + [frozenset(nwB)]
    for SP in itertools.combinations(range(b + 1), 4):
        common = frozenset(range(b))
        for k in SP:
            common &= rows[k]
        if len(common) >= 4:
            return True
    return False
