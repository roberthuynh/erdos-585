#!/usr/bin/env python3
"""Own pair test (networkx cycle enumeration, cycles grouped by vertex set, edge-disjoint pair
search) on the 44 5+5 sides X[A] = F[A] + H[A] (Fbar config alpha/beta, H[A] subset of Fbar,
|H[A]| <= 2), plus controls K44 (pair) and K44 - e (no pair). Checks PAPER §7 check_aside claim:
12 with a pair, 32 pair-free, and the stated rule."""
import itertools
import os
import sys

import networkx as nx

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import c1ref  # noqa: E402


def has_pair(G):
    by_vs = {}
    for cyc in nx.simple_cycles(G):
        if len(cyc) < 4:
            continue
        es = frozenset(frozenset((cyc[i], cyc[(i + 1) % len(cyc)])) for i in range(len(cyc)))
        by_vs.setdefault(frozenset(cyc), []).append(es)
    for vs, lst in by_vs.items():
        for e1, e2 in itertools.combinations(lst, 2):
            if not (e1 & e2):
                return True
    return False


def graph_of(a, edges):
    G = nx.Graph()
    G.add_nodes_from(['p%d' % i for i in range(a)] + ['q%d' % i for i in range(a)])
    G.add_edges_from(('p%d' % x, 'q%d' % y) for (x, y) in edges)
    return G


def main():
    k44 = graph_of(4, [(x, y) for x in range(4) for y in range(4)])
    k44e = graph_of(4, [(x, y) for x in range(4) for y in range(4) if (x, y) != (0, 0)])
    print('control K44 has pair:', has_pair(k44), ' K44-e has pair:', has_pair(k44e))
    npair = nfree = 0
    rule_ok = 0
    for side in c1ref.sides_55():
        X = set(side['FA']) | set(side['HA'])
        hp = has_pair(graph_of(5, X))
        kind = side['name'].split()[0]
        HA = side['HA']
        # stated rule: pair-free iff p1q1 not in H[A], H[A] not meeting both p1 and q1, and in beta not
        # both matching edges (3,3), (4,4)
        r1 = (0, 0) not in HA
        r2 = not (any(x == 0 for (x, y) in HA) and any(y == 0 for (x, y) in HA))
        r3 = not (kind == 'beta' and {(3, 3), (4, 4)} <= set(HA))
        rule_free = r1 and r2 and r3
        rule_ok += (rule_free == (not hp))
        npair += hp
        nfree += (not hp)
        print(side['name'], 'e=%d' % len(X), 'pair' if hp else 'pair-free', 'rule-agrees' if rule_free == (not hp) else 'RULE-DISAGREES')
    print('sides with a pair: %d, pair-free: %d, rule agrees on %d of 44' % (npair, nfree, rule_ok))


if __name__ == '__main__':
    main()
