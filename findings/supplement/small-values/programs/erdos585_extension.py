#!/usr/bin/env python3
"""Local reproducible experiments; every verdict is computational evidence only.

The construction suite checks all labeled base graphs on at most four vertices,
with every matching contained in each base graph. The two existing checkers are
called independently; neither checker is changed by this driver.
"""
import argparse
import itertools
import json
import random
from pathlib import Path
import time
import erdos585_small as first
import erdos585_verify as second

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'reports' / '585-extension'


def construction(t, edges, matching):
    edges, matching = set(edges), set(matching)
    assert matching <= edges
    endpoints = [v for edge in matching for v in edge]
    assert len(endpoints) == len(set(endpoints))
    graph = list(matching)
    next_vertex = t
    for a, b in sorted(edges - matching):
        graph.extend([(a, next_vertex), (b, next_vertex)])
        next_vertex += 1
    for v in range(next_vertex):
        graph.extend([(v, next_vertex), (v, next_vertex + 1)])
    graph.append((next_vertex, next_vertex + 1))
    return next_vertex + 2, sorted(tuple(sorted(e)) for e in graph)


def verify_both(n, edges):
    pairs, index = first.edge_index(n)
    mask = sum(1 << index[a][b] for a, b in edges)
    good1 = first.is_good_full(n, first.adj_from_mask(n, mask, pairs), index)
    ctx = second.Ctx(n)
    witness = second.find_pair(ctx, ctx.adj(ctx.mask(edges)))
    good2 = witness is None
    assert good1 == good2, (n, edges, good1, good2)
    if witness is not None:
        assert second.witness_ok(ctx, ctx.mask(edges), witness)
    return good1


def atomic_json(path, data):
    temp = path.with_suffix('.tmp')
    temp.write_text(json.dumps(data, indent=2) + '\n')
    temp.replace(path)


def constructions():
    OUT.mkdir(parents=True, exist_ok=True)
    start = time.time()
    rows = []
    controls = []
    for n, edges, expected, name in [
        (4, list(itertools.combinations(range(4), 2)), True, 'K4'),
        (5, list(itertools.combinations(range(5), 2)), False, 'K5'),
        (6, [(0,1),(0,2),(1,3),(2,3)] +
            [(v,h) for v in range(4) for h in (4,5)] + [(4,5)], False,
            'dropping the matching condition creates a forbidden pair'),
        (5, [(0,1),(0,2),(1,2)] +
            [(v,h) for v in range(3) for h in (3,4)] + [(3,4)], False,
            'retaining and subdividing the same edge creates K5')]:
        verdict = verify_both(n, edges)
        assert verdict == expected, name
        controls.append(dict(name=name, n=n, e=len(edges), pair_free=verdict))
    for t in range(5):
        all_edges = list(itertools.combinations(range(t), 2))
        for mask in range(1 << len(all_edges)):
            edges = [edge for i, edge in enumerate(all_edges) if mask >> i & 1]
            for mmask in range(1 << len(edges)):
                matching = [edge for i, edge in enumerate(edges) if mmask >> i & 1]
                flat = [v for edge in matching for v in edge]
                if len(flat) != len(set(flat)):
                    continue
                n, graph = construction(t, edges, matching)
                assert n == t + len(edges) - len(matching) + 2
                assert len(graph) == 2*t + 4*len(edges) - 3*len(matching) + 1
                assert verify_both(n, graph), (t, edges, matching)
                rows.append(dict(t=t, base=edges, matching=matching, n=n, e=len(graph)))
        atomic_json(OUT / 'construction-tests.json', dict(
            scope='all labeled H with t <= 4 and every matching M subset E(H)',
            complete_through_t=t, cases=len(rows), rows=rows, controls=controls,
            seconds=time.time()-start, status='computational evidence'))
        print(f't <= {t}: {len(rows)} constructions passed both checkers', flush=True)


WITNESS11 = [(0,4),(0,8),(0,9),(0,10),(1,3),(1,7),(1,9),(1,10),
    (2,7),(2,8),(2,9),(2,10),(3,5),(3,8),(3,9),(3,10),(4,6),(4,7),
    (4,9),(4,10),(5,6),(5,8),(5,9),(5,10),(6,7),(6,9),(6,10),
    (7,9),(7,10),(8,9),(8,10)]


def eleven(seconds, moves):
    """Checkpointed local search, never an exhaustive global upper-bound argument.

    First checks all one- and two-edge additions to the known witness, recording
    an independently validated forbidden pair for each failed candidate. Then
    performs seeded delete-and-greedily-extend steps, checking each extension by
    both independent programs. The RNG state and current graph survive restarts.
    """
    OUT.mkdir(parents=True, exist_ok=True)
    path = OUT / 'eleven-search.json'
    ctx = second.Ctx(11)
    start = time.time()
    assert verify_both(11, WITNESS11)
    pairs, index = first.edge_index(11)
    adj = first.adj_from_mask(11, ctx.mask(WITNESS11), pairs)
    cycles1 = sorted(first.all_cycles(11, adj, index))
    cycles2 = sorted(second.dfs_cycles(ctx, ctx.adj(ctx.mask(WITNESS11))))
    assert cycles1 == cycles2
    if path.exists():
        state = json.loads(path.read_text())
    else:
        state = dict(seed=5851101, current=ctx.mask(WITNESS11), best=31,
            steps=0, additions_checked=0, neighborhood_done=0,
            witnesses=[], candidates_at_32=0, candidates_at_33=0,
            verified_good_masks=[ctx.mask(WITNESS11)],
            scope='bounded local exploration; no completeness or new upper bound',
            baseline_cycles=len(cycles1), seconds=0)
    rng = random.Random(state['seed'])
    if 'rng_state' in state:
        def tuples(x):
            return tuple(tuples(y) for y in x) if isinstance(x, list) else x
        rng.setstate(tuples(state['rng_state']))
    def checkpoint():
        state['rng_state'] = rng.getstate()
        state['seconds'] += time.time() - checkpoint.last
        checkpoint.last = time.time()
        atomic_json(path, state)
    checkpoint.last = time.time()
    base = ctx.mask(WITNESS11)
    missing = [i for i in range(ctx.N) if not base >> i & 1]
    neighborhood = [(i,) for i in missing] + list(itertools.combinations(missing, 2))
    for ix in range(state['neighborhood_done'], len(neighborhood)):
        extra = neighborhood[ix]
        mask = base | sum(1 << i for i in extra)
        good = verify_both(11, ctx.edges(mask))
        state['candidates_at_' + str(mask.bit_count())] += 1
        if good:
            state['best'] = max(state['best'], mask.bit_count())
            state['verified_good_masks'].append(mask)
        else:
            witness = second.find_pair(ctx, ctx.adj(mask))
            assert second.witness_ok(ctx, mask, witness)
            state['witnesses'].append(dict(mask=mask, pair=witness))
        state['neighborhood_done'] = ix + 1
        checkpoint()
        if time.time() - start >= seconds:
            print(json.dumps({k: state[k] for k in ('steps','best','neighborhood_done','seconds')}), flush=True)
            return
    stop_step = state['steps'] + moves
    while state['steps'] < stop_step and time.time() - start < seconds:
        mask = state['current']
        present = [i for i in range(ctx.N) if mask >> i & 1]
        # Larger perturbations every fifth step prevent confinement to one plateau.
        for i in rng.sample(present, min(len(present), 2 if state['steps'] % 5 == 0 else 1)):
            mask ^= 1 << i
        absent = [i for i in range(ctx.N) if not mask >> i & 1]
        rng.shuffle(absent)
        for i in absent:
            candidate = mask | (1 << i)
            state['additions_checked'] += 1
            e = candidate.bit_count()
            if e in (32,33):
                state['candidates_at_' + str(e)] += 1
            if verify_both(11, ctx.edges(candidate)):
                mask = candidate
                state['best'] = max(state['best'], e)
                if e >= 31 and mask not in state['verified_good_masks']:
                    state['verified_good_masks'].append(mask)
            if time.time() - start >= seconds:
                break
        state['current'] = mask
        state['steps'] += 1
        checkpoint()
        if state['steps'] % 10 == 0:
            print(f"steps={state['steps']} best={state['best']} checked={state['additions_checked']}", flush=True)
    checkpoint()
    print(json.dumps({k: state[k] for k in ('steps','best','neighborhood_done','candidates_at_32','candidates_at_33','seconds')}), flush=True)



def neighborhood(seconds):
    """Exhaust only G-e+f+g around the named 31-edge witness (8,556 candidates).

    A forbidden pair in G-e+f is a certificate for each of its extensions.
    This avoids repeated checks while retaining an explicit completeness argument
    for this one local neighborhood. It says nothing about other 11-vertex graphs.
    """
    OUT.mkdir(parents=True, exist_ok=True)
    path = OUT / 'eleven-neighborhood.json'
    ctx = second.Ctx(11)
    base = ctx.mask(WITNESS11)
    present = [i for i in range(ctx.N) if base >> i & 1]
    absent = [i for i in range(ctx.N) if not base >> i & 1]
    jobs = [(e,i) for e in present for i in range(len(absent)-1)]
    state = json.loads(path.read_text()) if path.exists() else dict(
        next_job=0, covered=0, tested=0, cuts=[], good=[], seconds=0,
        scope='G minus one original edge plus two original nonedges only',
        candidates=len(present)*len(absent)*(len(absent)-1)//2,
        complete=False)
    start = time.time()
    last = start
    for job in range(state['next_job'], len(jobs)):
        e,i = jobs[job]
        mask = (base ^ (1 << e)) | (1 << absent[i])
        good = verify_both(11, ctx.edges(mask))
        state['tested'] += 1
        if not good:
            witness = second.find_pair(ctx, ctx.adj(mask))
            assert second.witness_ok(ctx, mask, witness)
            state['cuts'].append(dict(job=job, graph=mask, pair=witness,
                covers=len(absent)-i-1))
            state['covered'] += len(absent)-i-1
        else:
            for j in range(i+1, len(absent)):
                candidate = mask | (1 << absent[j])
                if verify_both(11, ctx.edges(candidate)):
                    state['good'].append(candidate)
                state['tested'] += 1
                state['covered'] += 1
        state['next_job'] = job+1
        state['complete'] = state['next_job'] == len(jobs)
        state['seconds'] += time.time()-last
        last = time.time()
        atomic_json(path, state)
        if state['next_job'] % 50 == 0:
            print(f"jobs={state['next_job']}/{len(jobs)} covered={state['covered']} good={len(state['good'])}", flush=True)
        if time.time()-start >= seconds:
            break
    print(json.dumps({k:state[k] for k in ['next_job','covered','tested','candidates','complete','seconds']}), flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('step', choices=['construction', 'eleven', 'neighborhood'])
    parser.add_argument('--seconds', type=int, default=180)
    parser.add_argument('--moves', type=int, default=100)
    args = parser.parse_args()
    if args.step == 'construction':
        constructions()
    elif args.step == 'eleven':
        eleven(args.seconds, args.moves)
    else:
        neighborhood(args.seconds)
