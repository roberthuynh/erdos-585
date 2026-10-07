"""Necklace generator: F0 = cactus cycle of k random 4-regular bipartite blocks (one edge removed
from each block, blocks joined cyclically), H = random h-factor in the complement with h = 2 except
the deficient vertices. Y = F0 + H is an E4 instance with a 4-factor F0 that has many 2-edge cuts."""
import random
import networkx as nx
from gen import realize

def random_4reg_bip(BP, BQ, rng):
    for _ in range(200):
        E = set()
        ok = True
        for _m in range(4):
            for _t in range(100):
                perm = BQ[:]; rng.shuffle(perm)
                if all((BP[i], perm[i]) not in E for i in range(len(BP))):
                    for i in range(len(BP)): E.add((BP[i], perm[i]))
                    break
            else:
                ok = False; break
        if ok:
            return E
    return None

def necklace(k, b, rng, pdefpat=None, qdefpat=None):
    a = k * b
    P = list(range(a)); Q = list(range(a, 2 * a))
    F0 = set()
    ports = []
    for i in range(k):
        BP = P[i * b:(i + 1) * b]; BQ = Q[i * b:(i + 1) * b]
        E = random_4reg_bip(BP, BQ, rng)
        if E is None: return None
        e = rng.choice(sorted(E)); E.remove(e)
        F0 |= E; ports.append(e)
    for i in range(k):
        p_i = ports[i][0]; q_next = ports[(i + 1) % k][1]
        F0.add((p_i, q_next))
    pats = [[2, 2], [2, 1, 1], [1, 1, 1, 1]]
    pdefpat = pdefpat or rng.choice(pats); qdefpat = qdefpat or rng.choice(pats)
    hp = {p: 2 for p in P}; hq = {q: 2 for q in Q}
    dp = rng.sample(P, len(pdefpat)); dq = rng.sample(Q, len(qdefpat))
    for v, d in zip(dp, pdefpat): hp[v] -= d
    for v, d in zip(dq, qdefpat): hq[v] -= d
    H = realize(hp, hq, rng, forbid=F0)
    if H is None: return None
    Y = nx.Graph(); Y.add_nodes_from(range(2 * a))
    Y.add_edges_from(F0); Y.add_edges_from(H)
    if Y.number_of_edges() != len(F0) + len(H): return None
    return Y, set(P), frozenset(F0)
