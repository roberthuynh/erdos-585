#!/usr/bin/env python3
"""Checkpointed independent deletion audit for a proposed twelve-vertex bound.

This expands the base range of the eleven-vertex audit. No nauty or native
detector is used. At each extension the added vertex is required to have
minimum degree, so deleting a minimum-degree vertex proves completeness.
"""
import argparse
import json
import math
import time

import erdos585_deletion_exhaustive as engine
import erdos585_verify as ref
from erdos585_extension import atomic_json

OUT = engine.OUT
STATE = OUT / 'deletion-twelve-state.json'
engine.STATE = STATE
_last_save = 0.0


def checkpoint(state):
    # Limit full-state rewrites. A hard interruption repeats at most one second
    # of completed parents; it cannot skip any untested parent.
    global _last_save
    now = time.monotonic()
    if now - _last_save >= 1.0:
        atomic_json(STATE, state)
        _last_save = now


engine.emit = checkpoint


def start_eight(state, deadline):
    ctx = ref.Ctx(8)
    if not ref.gen_levels(ctx, 12, state, str(STATE), deadline,
                          lambda s: print(s, flush=True)):
        return False
    levels = state['levels']['8']
    for k, rows in levels.items():
        assert sum(math.factorial(8)//aut for _, aut in rows) == math.comb(28, int(k))
    if '8' in state['catalogues']:
        return True
    work = state.setdefault('base_work', dict(next_index=0, kept={}))
    candidates = [(k, m) for k in range(9, 13) for m, _ in levels[str(k)]]
    for i in range(work['next_index'], len(candidates)):
        k, m = candidates[i]
        host = ctx.full ^ m
        if engine.check(ctx, host) is None:
            form, aut = ref.canon(ctx, host)
            work['kept'][str(form)] = aut
        work['next_index'] = i + 1
        if i % 50 == 0:
            atomic_json(STATE, state)
            print('base', i+1, len(candidates), len(work['kept']), flush=True)
        if time.time() > deadline:
            atomic_json(STATE, state)
            return False
    rows = sorted([int(m), aut] for m, aut in work['kept'].items())
    state['catalogues']['8'] = rows
    state['bounds']['8'] = 19
    state['counts']['8'] = {str(e): sum(m.bit_count()==e for m, _ in rows)
                            for e in range(16, 20)}
    atomic_json(STATE, state)
    return True


def run():
    parser = argparse.ArgumentParser()
    parser.add_argument('--through-ten', action='store_true')
    args = parser.parse_args()
    deadline = time.time() + 210
    if STATE.exists():
        state = json.loads(STATE.read_text())
    else:
        old = json.loads((OUT/'deletion-exhaustive-state.json').read_text())
        state = dict(levels=old['levels'], catalogues={}, bounds={}, counts={},
                     status='incomplete')
    if not start_eight(state, deadline):
        return
    for n, low, target in [(9, 20, None), (10, 25, None), (11, 30, None), (12, 36, 36)]:
        if not engine.extend(state, n, low, target, deadline):
            return
        if n == 10 and args.through_ten:
            atomic_json(STATE, state)
            print('Complete ten-vertex catalogue saved for the targeted upper-bound audit.', flush=True)
            return
    state['status'] = 'complete'
    state['conclusion'] = ('no twelve-vertex 36-edge pair-free graph' if not
                           state['catalogues']['12'] else 'twelve-vertex witnesses found')
    atomic_json(STATE, state)
    result = dict(status=state['status'], conclusion=state['conclusion'],
                  counts=state['counts'], bounds=state['bounds'],
                  tests={k:v['tests'] for k,v in state['work'].items()},
                  method='independent Python minimum-degree deletion and canonicalization',
                  classification='computational evidence; not a Lean theorem')
    atomic_json(OUT/'deletion-twelve-result.json', result)
    print(json.dumps(result, indent=2), flush=True)


if __name__ == '__main__':
    run()
