# Stress-test Conjecture M: random walks over 4-factors (random alternating cycles) in necklace
# instances; at every F with bad sets, apply the M rule to every atom and look for new bad sets.
import sys, time, random, collections
sys.path.insert(0, '.')
from tools import *
from dyn import *
from gen2 import necklace
def random_alt_cycle(I, F, rng, maxlen=12):
    D = digraph(I, F)
    for _ in range(50):
        v0 = rng.choice(list(I.Y)); path = [v0]; seen = {v0}; cur = v0
        while len(path) <= maxlen:
            nb = list(D.successors(cur))
            if not nb: break
            nxt = rng.choice(nb)
            if nxt == v0 and len(path) >= 4:
                return path
            if nxt in seen: break
            path.append(nxt); seen.add(nxt); cur = nxt
    return None
