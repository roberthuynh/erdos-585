#!/usr/bin/env python3
"""Count the class members in a superset stream (geng run with a degree flag dropped).

Reads graph6 on stdin, applies l5b_sat.class_check (e = 3n - 5, 4 <= deg <= 6, bipartite) and
prints a JSON line: graphs read, in class, by side split, and the reasons for rejection.
"""
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from l5b_sat import parse_g6, class_check  # noqa: E402

st = {'read': 0, 'in_class': 0, 'rejected': {}, 'sides': {}, 'disconnected': 0,
      'label': sys.argv[1] if len(sys.argv) > 1 else ''}
for line in sys.stdin:
    g6 = line.strip()
    if not g6:
        continue
    st['read'] += 1
    n, edges = parse_g6(g6)
    why, info = class_check(n, edges)
    if why is not None:
        st['rejected'][why] = st['rejected'].get(why, 0) + 1
        continue
    st['in_class'] += 1
    if info['connected']:
        k = '%d+%d' % tuple(info['sides'])
        st['sides'][k] = st['sides'].get(k, 0) + 1
    else:
        st['disconnected'] += 1
print(json.dumps(st, sort_keys=True))
