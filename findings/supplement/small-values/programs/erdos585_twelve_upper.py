#!/usr/bin/env python3
"""Second complete exclusion of 37 edges at order twelve, using vertex deletion.

The independently established f(11)=31 implies minimum degree >=6 in a
12-vertex, 37-edge counterexample. Its average degree is <7, so deleting a
degree-six vertex gives an 11-vertex graph with 31 edges and minimum degree
>=5. Delete a degree-five vertex there (average degree <6): its parent has
10 vertices, 26 edges and minimum degree >=4. The separately completed Python
catalogue supplies EVERY such ten-vertex parent. No nauty or C detector is used.
"""
import itertools
import json
from pathlib import Path

import erdos585_verify as ref
from erdos585_deletion_exhaustive import check
from erdos585_extension import atomic_json, verify_both

OUT = Path(__file__).resolve().parents[1]/'reports/585-overnight'
STATE = OUT/'twelve-upper-independent-state.json'


def extend(state, n, d, parents):
    old, ctx = ref.Ctx(n-1), ref.Ctx(n)
    key = str(n)
    work = state.setdefault(key, dict(next_parent=0, kept={}, tests=0, rejections=0))
    for idx in range(work['next_parent'], len(parents)):
        m = parents[idx]
        es = old.edges(m)
        deg = [x.bit_count() for x in old.adj(m)]
        if min(deg) < d-1:
            work['next_parent'] = idx+1
            continue
        base = ctx.mask(es)
        for nb in itertools.combinations(range(n-1), d):
            nb = set(nb)
            if any(deg[v]+(v in nb) < d for v in range(n-1)):
                continue
            host = base | sum(ctx.ebit[v][n-1] for v in nb)
            work['tests'] += 1
            if check(ctx, host) is not None:
                work['rejections'] += 1
            else:
                form, aut = ref.canon(ctx, host)
                work['kept'][str(form)] = aut
        work['next_parent'] = idx+1
        atomic_json(STATE, state)
    work['complete'] = True
    atomic_json(STATE, state)
    return sorted(map(int, work['kept']))


def main():
    baseline = json.loads((OUT/'deletion-exhaustive-result.json').read_text())
    assert baseline['status'] == 'complete'
    source = json.loads((OUT/'deletion-twelve-state.json').read_text())
    assert '10' in source['catalogues'], 'complete the ten-vertex Python catalogue first'
    parents = [m for m, _ in source['catalogues']['10'] if m.bit_count()==26]
    state = json.loads(STATE.read_text()) if STATE.exists() else dict(status='incomplete')
    state['ten_vertex_parents'] = len(parents)
    eleven = extend(state, 11, 5, parents)
    twelve = extend(state, 12, 6, eleven)
    assert not twelve
    witness = json.loads((OUT/'twelve-36-witness.json').read_text())
    assert verify_both(12, witness['edges'])
    state.update(status='complete', conclusion='computational f(12)=36',
                 limitation='no Lean upper-bound theorem; extremal uniqueness not checked by this method')
    atomic_json(STATE, state)
    result = dict(status='complete', conclusion=state['conclusion'],
                  ten_vertex_parents=len(parents),
                  eleven_tests=state['11']['tests'], eleven_survivors=len(eleven),
                  twelve_tests=state['12']['tests'], twelve_survivors=len(twelve),
                  source_counts=source['counts'],
                  completeness=__doc__, limitation=state['limitation'])
    atomic_json(OUT/'twelve-upper-independent-result.json', result)
    print(json.dumps(result, indent=2), flush=True)


if __name__ == '__main__':
    main()
