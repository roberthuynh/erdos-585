#!/usr/bin/env python3
"""Test of the symG lex clauses in isolation: for main-variable assignments x (random, and pushed to a
local lex-max by applying improving generator transpositions), the lex clauses with x fixed are SAT
iff x >=_lex tau(x) in the global order for every generator tau."""
import os, random, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import c1ref
from pysat.solvers import Solver

def run(b, levels, ntests, rng):
    m = c1ref.Model(c1ref.side_k44(), b, 5, FB=None, star=False, f2=True, levels=levels)
    lo, hi = m.lex_clause_range
    lexcl = m.clauses[lo:hi]
    order = m.main_order()
    gens = m.symG_generators
    def img(x, g):
        cls, i1, i2 = g
        return {k: x[m.swap_key(k, cls, i1, i2)] for k in order}
    def flat(x):
        return [x[k] for k in order]
    ok = bad = pos = 0
    for t in range(ntests):
        x = {k: rng.random() < 0.4 for k in order}
        if t % 2 == 0:  # push to a local lex-max
            improved = True
            while improved:
                improved = False
                for g in gens:
                    y = img(x, g)
                    if flat(y) > flat(x):
                        x = y
                        improved = True
        expected = all(flat(x) >= flat(img(x, g)) for g in gens)
        pos += expected
        units = [m.key_lit(k) if x[k] else -m.key_lit(k) for k in order]
        s = Solver(name='cadical195', bootstrap_with=lexcl)
        got = s.solve(assumptions=units)
        s.delete()
        if got == expected:
            ok += 1
        else:
            bad += 1
    print('b=%d levels=%s generators=%d tests=%d (lex-ok assignments %d): agree %d disagree %d' % (
        b, levels, len(gens), ntests, pos, ok, bad))

rng = random.Random(5)
for lv in (('symG',), ('symG', 'case=y1pp'), ('symG', 'case=y1b1')):
    run(6, lv, 300, rng)
    run(7, lv, 200, rng)
