"""Checks of PAPER Identity 6.2 (runs), the H-balance of Remark 6.4, the arc balance, and (1.1)-(1.2),
on random sparse E4 instances, random 4-factors, random directed cycles of D(F), random sets."""
import sys, random
sys.path.insert(0, '.')
from tools import *
from gen import random_e4
from dyn import digraph, cycle_edges, swap
from exp11lib import random_alt_cycle
rng = random.Random(int(sys.argv[1]))
cnt = {'inst': 0, 'id62': 0, 'hbal': 0, 'arcbal': 0, 'id11': 0, 'id12': 0}
while cnt['inst'] < int(sys.argv[2]):
    r = random_e4(rng.choice([8, 9, 10, 11]), rng)
    if r is None: continue
    Y, P = r
    I = Inst(Y, P)
    if min(I.deg.values()) < 4: continue
    F = I.random_four_factor(rng)
    if F is None: continue
    cnt['inst'] += 1
    V = list(Y)
    D = digraph(I, F)
    for _ in range(30):
        Z = random_alt_cycle(I, F, rng, maxlen=16)
        if Z is None: continue
        F2 = swap(F, cycle_edges(I, Z))
        for _u in range(20):
            # random balanced U
            k = rng.randrange(1, len(P))
            UP = rng.sample(sorted(I.P), k); UQ = rng.sample(sorted(I.Q), k)
            U = frozenset(UP + UQ)
            cF = lambda G: sum(1 for (p, q) in G if q in U and p not in U)
            # runs of Z inside U
            n_ = len(Z); FF = HH = 0
            inside = [z in U for z in Z]
            if all(inside) or not any(inside):
                runs = []
            else:
                start = next(i for i in range(n_) if inside[i] and not inside[i - 1])
                i = start
                while True:
                    # run from i while inside
                    j = i
                    while inside[(j + 1) % n_]: j = (j + 1) % n_
                    ein = (Z[i - 1], Z[i]); eout = (Z[j], Z[(j + 1) % n_])
                    kin = 'F' if ((ein[0], ein[1]) if ein[0] in I.P else (ein[1], ein[0])) in F else 'H'
                    kout = 'F' if ((eout[0], eout[1]) if eout[0] in I.P else (eout[1], eout[0])) in F else 'H'
                    FF += (kin == 'F' and kout == 'F'); HH += (kin == 'H' and kout == 'H')
                    # next run
                    k2 = (j + 1) % n_
                    while not inside[k2]: k2 = (k2 + 1) % n_
                    i = k2
                    if i == start: break
            assert cF(F2) == cF(F) + HH - FF, 'Identity 6.2'
            cnt['id62'] += 1
        # H-balance and arc balance for random sets R
        for _r in range(20):
            R = frozenset(v for v in V if rng.random() < 0.5)
            Hin = sum(1 for (p, q) in I.pq if (p, q) not in F and p in R and q not in R)
            Hout = sum(1 for (p, q) in I.pq if (p, q) not in F and q in R and p not in R)
            j = I.j(R)
            assert Hin - Hout == I.D(R & I.Q) - I.D(R & I.P) - 2 * j, 'H-balance'
            cnt['hbal'] += 1
            out = sum(1 for (u, v) in D.edges() if u in R and v not in R)
            inn = sum(1 for (u, v) in D.edges() if v in R and u not in R)
            assert out - inn == -2 * j - I.D(R & I.Q) + I.D(R & I.P), 'arc balance'
            assert out == I.s(R), 'Lemma 1.1 out-degree'
            cnt['arcbal'] += 1
            g = I.g(R)
            if R:
                assert I.dQ(R) == g // 2 + 3 * j - I.D(R & I.Q) and I.dP(R) == g // 2 - 3 * j - I.D(R & I.P), '(1.1)'
                cnt['id11'] += 1
            Vs = frozenset(V)
            assert I.g(R) + I.g(Vs - R) == 8 + 2 * (I.dP(R) + I.dQ(R)), '(1.2)'
            cnt['id12'] += 1
print(cnt)
