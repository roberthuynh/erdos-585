#!/usr/bin/env python3
"""Completeness test of the (star) clauses: random configurations built directly (no SAT), BFS
decides one-crossing, and the (star) model (relax1: Q/P H-degree <= 2, >= 1 E0H and E1H edge) with
all main variables fixed must be SAT iff there is no one-crossing."""
import os
import random
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import c1ref  # noqa: E402
import run_shape  # noqa: E402
from enc_test import fixed_units  # noqa: E402
from pysat.solvers import Solver  # noqa: E402


P_CHOICES = [0.1, 0.2, 0.35]


def rand_cfg(rng, side, b, FB):
    a = side['a']
    hP = {('A', x): sum(1 for (xx, y) in side['HA'] if xx == x) for x in range(a)}
    hQ = {('A', y): sum(1 for (x, yy) in side['HA'] if yy == y) for y in range(a)}
    for k in range(b):
        hP['B', k] = 0
        hQ['B', k] = 0
    cand = []
    for k in range(b):
        for j in range(b):
            if (k, j) not in FB:
                cand.append(('h', k, j))
    for y in range(a):
        for i in range(b):
            if (y, i) != (0, 0):
                cand.append(('e0', y, i))
    for x in range(a):
        for j in range(b):
            if (x, j) != (0, 0):
                cand.append(('e1', x, j))
    rng.shuffle(cand)
    p_take = rng.choice(P_CHOICES)
    HB, E0, E1 = set(), set(), set()
    for c in cand:
        if rng.random() > p_take:
            continue
        if c[0] == 'h':
            pv, qv = ('B', c[1]), ('B', c[2])
        elif c[0] == 'e0':
            pv, qv = ('B', c[2]), ('A', c[1])
        else:
            pv, qv = ('A', c[1]), ('B', c[2])
        if hP[pv] >= 2 or hQ[qv] >= 2:
            continue
        hP[pv] += 1
        hQ[qv] += 1
        (HB if c[0] == 'h' else E0 if c[0] == 'e0' else E1).add((c[1], c[2]))
    if not E0 or not E1:
        return None
    return dict(a=a, b=b, FA=side['FA'], HA=side['HA'], FB=FB, HB=frozenset(HB), E0=frozenset(E0),
                E1=frozenset(E1), NW=frozenset(), U=[])


def main():
    shape, ntests, seed = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    if len(sys.argv) > 4:
        P_CHOICES[:] = [float(x) for x in sys.argv[4].split(",")]
    rng = random.Random(seed)
    kind, b, _ = run_shape.SHAPES[shape]
    sides = [c1ref.side_k44()] if kind == 'k44' else c1ref.sides_55()
    fbs = run_shape.load_fb(b)
    agree = disagree = noc = 0
    tested = 0
    while tested < ntests:
        side = rng.choice(sides)
        FB = rng.choice(fbs)
        cfg = rand_cfg(rng, side, b, FB)
        if cfg is None:
            continue
        tested += 1
        chk = c1ref.check_config(cfg, 5, f2=False)
        m = c1ref.Model(side, b, 5, FB=FB, star=True, f2=False, levels=('relax1',))
        s = Solver(name='cadical195', bootstrap_with=m.clauses)
        ok = s.solve(assumptions=fixed_units(m, cfg))
        s.delete()
        noc += (not chk['onecross'])
        if ok == (not chk['onecross']):
            agree += 1
        else:
            disagree += 1
            print('DISAGREE', side['name'], sorted(cfg['HB']), sorted(cfg['E0']), sorted(cfg['E1']), ok, chk)
    print('shape=%s random configs=%d: without one-crossing %d; agree %d disagree %d' % (
        shape, ntests, noc, agree, disagree))


if __name__ == '__main__':
    main()
