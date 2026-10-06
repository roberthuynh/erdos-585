# Independent check of mpair NONE answers: enumerate every cycle (networkx simple_cycles, undirected),
# and look for edge-disjoint C1 (through ab, not cd) and C2 (through cd) with the same vertex set.
# Also: is Y - ab - cd pair-free (any two edge-disjoint cycles on one vertex set)?
# And for X = (Y - ab - cd) + v with N(v) = {a,b,c,d}: which pairings at v are realized by pairs?
import sys, itertools, collections
import networkx as nx
def cycles_by_set(G):
    by = collections.defaultdict(list)
    for c in nx.simple_cycles(G):
        if len(c) < 3: continue
        es = frozenset(frozenset((c[i], c[(i + 1) % len(c)])) for i in range(len(c)))
        by[frozenset(c)].append(es)
    return by
def has_pair(by):
    for S, L in by.items():
        for x, y in itertools.combinations(L, 2):
            if not (x & y): return True
    return False
for line in open(sys.argv[1]):
    t = line.split()
    g, a, b, c, d = t[0], *map(int, t[1:5])
    Y = nx.from_graph6_bytes(g.encode())
    ab, cd = frozenset((a, b)), frozenset((c, d))
    by = cycles_by_set(Y)
    compat = False
    for S, L in by.items():
        for x in L:
            if ab in x and cd not in x:
                for y in L:
                    if cd in y and not (x & y): compat = True
    Z = Y.copy(); Z.remove_edge(a, b); Z.remove_edge(c, d)
    zfree = not has_pair(cycles_by_set(Z))
    X = Z.copy(); v = Y.number_of_nodes()
    for u in (a, b, c, d): X.add_edge(v, u)
    byX = cycles_by_set(X)
    pairings = set()
    for S, L in byX.items():
        if v not in S: continue
        for x, y in itertools.combinations(L, 2):
            if x & y: continue
            nb = tuple(sorted(sorted(u for u in (a, b, c, d) if frozenset((v, u)) in x)))
            pairings.add(nb)
    ncyc = sum(len(L) for L in by.values())
    print(g, a, b, c, d, 'cycles=%d' % ncyc, 'compat=%s' % compat, 'Z_pairfree=%s' % zfree,
          'X_pairings_at_v=%s' % sorted(pairings), 'deg=%s' % sorted(dict(Y.degree()).values()))
