#!/usr/bin/env python3
"""Validate the SAT pair decider (l5b_sat.decide) against a brute force written here.

Brute force: enumerate every cycle once (DFS from its least vertex, one direction), group the
cycles by vertex set, and look for two edge-disjoint cycles in one group.

Test sets:
  random   G(n, p) for n = 4..9 and random bipartite graphs with sides 3..5 (seeded)
  named    K4 (no pair), K5 (pair), K_{4,4} (pair), K_{3,3} (no pair), Petersen (no pair),
           K_{4,4} minus an edge (no pair), octahedron K_{2,2,2} (pair)
  files    graph6 files given with --pairfree (every graph expected pair-free) or --brute
           (decided by both methods)
Prints a JSON summary; exits 1 on any disagreement.
"""
import argparse
import itertools
import json
import random
import sys
import os

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from l5b_sat import parse_g6, decide, check_pair  # noqa: E402


def brute_pair(n, edges):
    adj = [set() for _ in range(n)]
    for u, w in edges:
        adj[u].add(w)
        adj[w].add(u)
    groups = {}

    def dfs(s, path, onpath):
        v = path[-1]
        for w in adj[v]:
            if w == s and len(path) >= 3 and path[1] < path[-1]:
                es = frozenset((min(path[j], path[(j + 1) % len(path)]),
                                max(path[j], path[(j + 1) % len(path)])) for j in range(len(path)))
                groups.setdefault(frozenset(path), []).append(es)
            elif w > s and w not in onpath:
                onpath.add(w)
                path.append(w)
                dfs(s, path, onpath)
                path.pop()
                onpath.discard(w)

    for s in range(n):
        dfs(s, [s], {s})
    for vs, lst in groups.items():
        for a, b in itertools.combinations(lst, 2):
            if not (a & b):
                return True
    return False


def g6_encode(n, edges):
    eset = set(edges)
    bits = []
    for j in range(1, n):
        for i in range(j):
            bits.append(1 if (i, j) in eset else 0)
    while len(bits) % 6:
        bits.append(0)
    out = [chr(n + 63)]
    for k in range(0, len(bits), 6):
        x = 0
        for b in bits[k:k + 6]:
            x = 2 * x + b
        out.append(chr(x + 63))
    return ''.join(out)


def named():
    def complete(n):
        return [(i, j) for i in range(n) for j in range(i + 1, n)]

    def kbip(a, b):
        return [(i, a + j) for i in range(a) for j in range(b)]
    pet_outer = [(i, (i + 1) % 5) for i in range(5)]
    pet_inner = [(5 + i, 5 + (i + 2) % 5) for i in range(5)]
    pet_spokes = [(i, 5 + i) for i in range(5)]
    pet = [(min(u, w), max(u, w)) for u, w in pet_outer + pet_inner + pet_spokes]
    k44m = kbip(4, 4)[1:]
    octa = [e for e in complete(6) if e not in [(0, 1), (2, 3), (4, 5)]]
    return [('K4', 4, complete(4), False), ('K5', 5, complete(5), True),
            ('K44', 8, kbip(4, 4), True), ('K33', 6, kbip(3, 3), False),
            ('Petersen', 10, pet, False), ('K44-e', 8, k44m, False), ('octahedron', 6, octa, True)]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--random', type=int, default=0, help='number of random graphs')
    ap.add_argument('--seed', type=int, default=585)
    ap.add_argument('--pairfree', nargs='*', default=[])
    ap.add_argument('--brute', nargs='*', default=[])
    ap.add_argument('--solver', default='m22')
    args = ap.parse_args()
    rep = {'named': {}, 'random': {'tested': 0, 'pair': 0, 'free': 0, 'disagree': 0},
           'pairfree_files': {}, 'brute_files': {}}
    bad = 0
    for name, n, edges, expect in named():
        r = decide(n, edges, args.solver)
        b = brute_pair(n, edges)
        ok = (r is not None) == expect == b
        rep['named'][name] = {'sat': r is not None, 'brute': b, 'expected': expect, 'ok': ok}
        bad += not ok
    rng = random.Random(args.seed)
    for t in range(args.random):
        if t % 2 == 0:
            n = rng.randint(4, 9)
            p = rng.choice([0.3, 0.45, 0.6, 0.75, 0.9])
            edges = [(i, j) for i in range(n) for j in range(i + 1, n) if rng.random() < p]
        else:
            a, b2 = rng.randint(3, 5), rng.randint(3, 5)
            n = a + b2
            p = rng.choice([0.5, 0.7, 0.85, 1.0])
            edges = [(i, a + j) for i in range(a) for j in range(b2) if rng.random() < p]
            perm = list(range(n))
            rng.shuffle(perm)
            edges = sorted((min(perm[u], perm[w]), max(perm[u], perm[w])) for u, w in edges)
        r = decide(n, edges, args.solver)
        bp = brute_pair(n, edges)
        rep['random']['tested'] += 1
        rep['random']['pair' if bp else 'free'] += 1
        if (r is not None) != bp:
            rep['random']['disagree'] += 1
            bad += 1
            sys.stderr.write('DISAGREE %s sat=%s brute=%s\n' % (g6_encode(n, edges), r is not None, bp))
    for fn in args.pairfree:
        cnt = {'graphs': 0, 'sat_free': 0, 'sat_pair': 0}
        with open(fn) as f:
            for line in f:
                if not line.strip():
                    continue
                n, edges = parse_g6(line.split()[0])
                cnt['graphs'] += 1
                r = decide(n, edges, args.solver)
                if r is None:
                    cnt['sat_free'] += 1
                else:
                    cnt['sat_pair'] += 1
                    bad += 1
                    sys.stderr.write('EXPECTED FREE, SAT FOUND %s %s\n' % (line.split()[0], r))
        rep['pairfree_files'][fn] = cnt
    for fn in args.brute:
        cnt = {'graphs': 0, 'agree': 0, 'pair': 0, 'free': 0}
        with open(fn) as f:
            for line in f:
                if not line.strip():
                    continue
                n, edges = parse_g6(line.split()[0])
                r = decide(n, edges, args.solver)
                bp = brute_pair(n, edges)
                cnt['graphs'] += 1
                cnt['pair' if bp else 'free'] += 1
                if (r is not None) == bp:
                    cnt['agree'] += 1
                else:
                    bad += 1
                    sys.stderr.write('DISAGREE %s sat=%s brute=%s\n' % (line.split()[0], r is not None, bp))
        rep['brute_files'][fn] = cnt
    rep['bad'] = bad
    print(json.dumps(rep, indent=1, sort_keys=True))
    sys.exit(1 if bad else 0)


if __name__ == '__main__':
    main()
