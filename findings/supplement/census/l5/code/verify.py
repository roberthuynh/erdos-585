#!/usr/bin/env python3
"""L5B verifier: re-checks the decider's output with separate code (networkx graph6 parser).

Input: decider output files (plain or .gz), lines "<g6> P <k> <C1> <C2>", "<g6> F", "<g6> X <why>".
For every line:
  - class membership again: e = 3n - 5, 4 <= deg <= 6, bipartite (networkx), connected or not,
    side sizes of the bipartition (connected case);
  - P lines: C1 and C2 are cycles of G (consecutive vertices adjacent, closing edge present, no
    repeated vertex, length >= 3), V(C1) = V(C2), |V(C1)| = k, E(C1) and E(C2) disjoint;
  - for even n and connected G: does G have an automorphism exchanging the two sides
    (networkx VF2++ with side labels)? Used to convert to genbg's colour-preserving count:
    colour-preserving classes = 2 * (uncoloured classes) - (classes with a side-swapping automorphism).
Prints one JSON summary; F and X lines are copied to --exceptions.
"""
import argparse
import gzip
import json
import sys

import networkx as nx


def opener(fn):
    return gzip.open(fn, 'rt') if fn.endswith('.gz') else open(fn)


def cycle_edges(G, seq):
    if len(seq) < 3 or len(set(seq)) != len(seq):
        return None
    es = set()
    for j in range(len(seq)):
        a, b = seq[j], seq[(j + 1) % len(seq)]
        if not G.has_edge(a, b):
            return None
        es.add(frozenset((a, b)))
    return es if len(es) == len(seq) else None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('files', nargs='+')
    ap.add_argument('--exceptions', default=None)
    ap.add_argument('--noswap', action='store_true')
    args = ap.parse_args()
    st = {'lines': 0, 'P_ok': 0, 'P_bad': 0, 'F': 0, 'X': 0, 'class_ok': 0, 'class_bad': 0,
          'connected': 0, 'disconnected': 0, 'sides': {}, 'swap_auto': 0, 'swap_checked': 0,
          'n': {}, 'files': len(args.files)}
    exc = open(args.exceptions, 'w') if args.exceptions else None
    for fn in args.files:
        with opener(fn) as f:
            for line in f:
                parts = line.split()
                if not parts:
                    continue
                st['lines'] += 1
                g6 = parts[0]
                G = nx.from_graph6_bytes(g6.encode())
                n = G.number_of_nodes()
                st['n'][str(n)] = st['n'].get(str(n), 0) + 1
                degs = [d for _, d in G.degree()]
                inclass = (G.number_of_edges() == 3 * n - 5 and min(degs) >= 4 and max(degs) <= 6
                           and nx.is_bipartite(G))
                st['class_ok' if inclass else 'class_bad'] += 1
                conn = nx.is_connected(G)
                st['connected' if conn else 'disconnected'] += 1
                if conn and inclass:
                    top, bot = nx.bipartite.sets(G)
                    key = '%d+%d' % tuple(sorted((len(top), len(bot))))
                    st['sides'][key] = st['sides'].get(key, 0) + 1
                    if n % 2 == 0 and len(top) == len(bot) and not args.noswap:
                        side = {v: (0 if v in top else 1) for v in G}
                        G1 = G.copy()
                        G2 = G.copy()
                        nx.set_node_attributes(G1, side, 'side')
                        nx.set_node_attributes(G2, {v: 1 - s for v, s in side.items()}, 'side')
                        st['swap_checked'] += 1
                        if nx.vf2pp_is_isomorphic(G1, G2, node_label='side'):
                            st['swap_auto'] += 1
                tag = parts[1]
                if tag == 'P':
                    k = int(parts[2])
                    c1 = [ord(ch) - 97 for ch in parts[3]]
                    c2 = [ord(ch) - 97 for ch in parts[4]]
                    e1, e2 = cycle_edges(G, c1), cycle_edges(G, c2)
                    ok = (e1 is not None and e2 is not None and set(c1) == set(c2)
                          and len(c1) == k and not (e1 & e2))
                    st['P_ok' if ok else 'P_bad'] += 1
                    if not ok and exc:
                        exc.write('BADCERT ' + line)
                elif tag == 'F':
                    st['F'] += 1
                    if exc:
                        exc.write(line)
                else:
                    st['X'] += 1
                    if exc:
                        exc.write(line)
    if exc:
        exc.close()
    print(json.dumps(st, sort_keys=True))


if __name__ == '__main__':
    main()
