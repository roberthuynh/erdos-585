"""Which 5+5 sides (Fbar configuration alpha/beta, H[A] subset of Fbar, |H[A]| <= 2) are pair-free?
A_P = 0..4 (p1 = 0), A_Q = 5..9 (q1 = 5). Also K44 - e as a sanity check (must be pair-free)."""
import itertools, sys
from c1lib import has_pair_many

def fbar(name):
    if name == 'alpha':
        return [(0, 0), (0, 1), (1, 0), (2, 2), (3, 3), (4, 4)]
    return [(0, 1), (0, 2), (1, 0), (2, 0), (3, 3), (4, 4)]

cases, graphs = [], []
for cfg in ('alpha', 'beta'):
    fb = fbar(cfg)
    FA = [(p, q) for p in range(5) for q in range(5) if (p, q) not in fb]
    for k in range(3):
        for HA in itertools.combinations(fb, k):
            E = [(p, 5 + q) for (p, q) in FA + list(HA)]
            cases.append((cfg, HA)); graphs.append((10, E))
K44e = [(p, 4 + q) for p in range(4) for q in range(4) if (p, q) != (0, 0)]
cases.append(('K44-e', ())); graphs.append((8, K44e))
K44 = [(p, 4 + q) for p in range(4) for q in range(4)]
cases.append(('K44 (control)', ())); graphs.append((8, K44))
res = has_pair_many(graphs)
for c, r in zip(cases, res):
    print(c[0], list(c[1]), 'PAIR' if r else 'pair-free')
