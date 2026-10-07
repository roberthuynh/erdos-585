# verify spanning-pair witnesses "g6 SP C1=... C2=...": both Hamilton cycles of G, edge-disjoint
import sys, networkx as nx
ok = bad = nosp = 0
for line in sys.stdin:
    t = line.split()
    if len(t) < 2: continue
    if t[1] != 'SP': nosp += 1; continue
    G = nx.from_graph6_bytes(t[0].encode()); n = G.number_of_nodes()
    def cyc(spec):
        c = [int(x) for x in spec.split('=')[1].split(',')]
        assert sorted(c) == list(range(n)), 'not spanning'
        es = set()
        for i in range(n):
            a, b = c[i], c[(i + 1) % n]
            assert G.has_edge(a, b), 'non-edge'
            es.add(frozenset((a, b)))
        assert len(es) == n
        return es
    try:
        e1 = cyc(t[2]); e2 = cyc(t[3]); assert not (e1 & e2), 'not disjoint'; ok += 1
    except AssertionError as ex:
        bad += 1; print('BAD', t[0], ex)
print('verified', ok, 'bad', bad, 'nosp', nosp)
