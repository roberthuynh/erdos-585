#!/usr/bin/env python3
"""Encoding tests for the (star) clauses of c1ref.Model.
(1) soundness of 'star => no one-crossing': with relaxed counts (relaxK: >= K E0H and E1H edges,
    Q H-degree <= 2), every SAT model with (star) is re-checked by BFS: it must have no one-crossing.
(2) completeness ('every configuration with no one-crossing satisfies the clauses'): random
    configurations are drawn from SAT models without (star) (random phases); for each, BFS decides
    one-crossing; the (star) model with all main variables fixed must be SAT exactly when there is
    no one-crossing.
"""
import os
import random
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import c1ref  # noqa: E402
import run_shape  # noqa: E402
from pysat.solvers import Solver  # noqa: E402


def fixed_units(m, cfg):
    units = []
    for kj, v in m.f.items():
        if v is True or v is False:
            continue
        units.append(v if kj in cfg['FB'] else -v)
    for kj, v in m.h.items():
        units.append(v if kj in cfg['HB'] else -v)
    for k, v in m.e0.items():
        units.append(v if k in cfg['E0'] else -v)
    for k, v in m.e1.items():
        units.append(v if k in cfg['E1'] else -v)
    return units


def main():
    shape = sys.argv[1]
    K = int(sys.argv[2])
    ntests = int(sys.argv[3])
    rng = random.Random(int(sys.argv[4]) if len(sys.argv) > 4 else 1)
    kind, b, _ = run_shape.SHAPES[shape]
    sides = [c1ref.side_k44()] if kind == 'k44' else c1ref.sides_55()
    fbs = run_shape.load_fb(b)
    lv = ('relax%d' % K,)
    star_sat = star_unsat = bad1 = 0
    agree = disagree = n_noc = 0
    for t in range(ntests):
        side = rng.choice(sides)
        FB = rng.choice(fbs)
        # (1)
        m = c1ref.Model(side, b, 5, FB=FB, star=True, f2=False, levels=lv)
        s = Solver(name='cadical195', bootstrap_with=m.clauses)
        allv = list(range(1, m.pool.top + 1))
        s.set_phases([v if rng.random() < 0.5 else -v for v in allv])
        if s.solve():
            star_sat += 1
            cfg = m.decode(set(l for l in s.get_model() if l > 0))
            chk = c1ref.check_config(cfg, 5, f2=False)
            if chk['onecross']:
                bad1 += 1
        else:
            star_unsat += 1
        s.delete()
        # (2)
        m0 = c1ref.Model(side, b, 5, FB=FB, star=False, f2=False, levels=lv)
        s0 = Solver(name='cadical195', bootstrap_with=m0.clauses)
        s0.set_phases([v if rng.random() < 0.5 else -v for v in range(1, m0.pool.top + 1)])
        if not s0.solve():
            s0.delete()
            continue
        cfg = m0.decode(set(l for l in s0.get_model() if l > 0))
        s0.delete()
        chk = c1ref.check_config(cfg, 5, f2=False)
        m1 = c1ref.Model(side, b, 5, FB=FB, star=True, f2=False, levels=lv)
        s1 = Solver(name='cadical195', bootstrap_with=m1.clauses)
        ok = s1.solve(assumptions=fixed_units(m1, cfg))
        s1.delete()
        if not chk['onecross']:
            n_noc += 1
        if ok == (not chk['onecross']):
            agree += 1
        else:
            disagree += 1
    print('shape=%s relax%d tests=%d: (1) star SAT %d (with one-crossing: %d) star UNSAT %d; '
          '(2) agree %d disagree %d (configs without one-crossing: %d)' % (
              shape, K, ntests, star_sat, bad1, star_unsat, agree, disagree, n_noc))


if __name__ == '__main__':
    main()
