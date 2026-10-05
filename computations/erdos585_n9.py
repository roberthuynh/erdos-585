#!/usr/bin/env python3
"""Erdos 585 beyond n = 8 (Python 3 standard library only).

The pair test, witness re-check and canonical form are imported from the
checker computations/erdos585_verify.py (find_pair, witness_ok, canon).
A second, separately written cycle test comes from computations/erdos585_small.py
(is_good_full) and, for n <= 10, the brute-force cycle list of the verifier
(naive_cycles + naive_pair_grouped).

Steps (resumable state in --state):
  struct   structure table of the known extremal classes (n = 7, n = 8)
  witness  re-check an edge list (--edges) with all three tests
  kfam     K2 join C_{n-2} has no pair, n = 9..12
  ext      one-vertex extensions of the n = 8 extremal classes, then add edges
  levels   k-edge graphs on n vertices up to isomorphism (parallel, resumable)
  comp     complements of the level-k classes: bad with verified witness, or good
  ext10    one-vertex extensions of the good classes found by `comp` (n = 9)
  ext11    one-vertex extensions of the 27-edge n = 10 classes found by ext10
Sections are appended to computations/585-n9.md as each chunk finishes.
"""
import argparse
import ast
import itertools
import json
import math
import os
import sys
import time
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import erdos585_verify as V  # noqa: E402
import erdos585_small as S   # noqa: E402

REPORT = os.path.join(HERE, '585-n9.md')
A008406 = {(9, 12): 5995, (9, 13): 10120, (9, 14): 15615, (8, 10): 663, (8, 11): 980, (8, 12): 1312}

CTX = {}


def ctx_of(n):
    c = CTX.get(n)
    if c is None:
        c = CTX[n] = V.Ctx(n)
    return c


def append(text):
    with open(REPORT, 'a') as fh:
        fh.write(text.rstrip('\n') + '\n')


def load_state(path):
    if os.path.exists(path):
        with open(path) as fh:
            return json.load(fh)
    return {}


def save_state(path, state):
    tmp = path + '.tmp'
    with open(tmp, 'w') as fh:
        json.dump(state, fh)
    os.replace(tmp, path)


def degs(ctx, m):
    return [V.popcount(x) for x in ctx.adj(m)]


def good3(ctx, m):
    """(verdict by find_pair, verdict by erdos585_small.is_good_full, brute force or None)."""
    adj = ctx.adj(m)
    w = V.find_pair(ctx, adj)
    edges, E = S.edge_index(ctx.n)
    g2 = S.is_good_full(ctx.n, S.adj_from_mask(ctx.n, m, edges), E)
    g3 = None
    if ctx.n <= 10:
        g3 = V.naive_pair_grouped(V.naive_cycles(ctx, adj)) is None
    return w, g2, g3


def sub_mask(ctx_big, m, keep):
    """Induced subgraph on the vertex list `keep`, relabelled 0..len(keep)-1."""
    small = ctx_of(len(keep))
    idx = {v: i for i, v in enumerate(keep)}
    f = 0
    for u, v in ctx_big.edges(m):
        if u in idx and v in idx:
            f |= small.ebit[idx[u]][idx[v]]
    return f


def kcore(n, adj, k):
    alive = set(range(n))
    changed = True
    while changed:
        changed = False
        for v in sorted(alive):
            if sum(1 for w in alive if (adj[v] >> w) & 1) < k:
                alive.discard(v)
                changed = True
    return sorted(alive)


def components(n, adj, verts):
    vs = set(verts)
    out = []
    seen = set()
    for v in verts:
        if v in seen:
            continue
        comp = [v]
        seen.add(v)
        todo = [v]
        while todo:
            x = todo.pop()
            for y in vs:
                if y not in seen and (adj[x] >> y) & 1:
                    seen.add(y)
                    comp.append(y)
                    todo.append(y)
        out.append(sorted(comp))
    return out


def name_graph(n, adj, verts):
    """Short name of the induced subgraph on verts (component by component)."""
    parts = []
    for comp in components(n, adj, verts):
        c = len(comp)
        d = [sum(1 for w in comp if (adj[v] >> w) & 1) for v in comp]
        e = sum(d) // 2
        if c == 1:
            parts.append('K1')
        elif e == c * (c - 1) // 2:
            parts.append('K%d' % c)
        elif e == c and all(x == 2 for x in d):
            parts.append('C%d' % c)
        elif e == c - 1 and max(d) <= 2:
            parts.append('P%d' % c)
        elif e == c + 1 and sorted(d)[-2:] == [3, 3] and all(x == 2 for x in sorted(d)[:-2]):
            # theta graph: two degree-3 vertices joined by three internally disjoint paths
            a, b = [v for v, x in zip(comp, d) if x == 3]
            lens, loops = [], []
            for s in [w for w in comp if (adj[a] >> w) & 1]:
                L, prev, cur = 1, a, s
                while cur not in (a, b):
                    nxt = [w for w in comp if (adj[cur] >> w) & 1 and w != prev][0]
                    prev, cur = cur, nxt
                    L += 1
                (lens if cur == b else loops).append(L)
            if len(lens) == 3:
                parts.append('theta(%s)' % ','.join(map(str, sorted(lens))))
            else:
                # dumbbell: a cycle through a, a cycle through b, an a-b path of lens[0] edges
                la = loops[0]
                lb = c - (la - 1) - (lens[0] - 1) - 2 + 1
                parts.append('dumbbell(C%d,path %d,C%d)' % (min(la, lb), lens[0], max(la, lb)))
        else:
            parts.append('[%dv,%de,deg %s]' % (c, e, ''.join(map(str, sorted(d, reverse=True)))))
    return '+'.join(sorted(parts))


def cycle_stats(ctx, adj):
    groups = {}
    total = 0
    for vm, em in V.dfs_cycles(ctx, adj):
        total += 1
        groups[vm] = groups.get(vm, 0) + 1
    multi = sum(1 for c in groups.values() if c >= 2)
    return total, len(groups), multi, max(groups.values()) if groups else 0


def join_shape(ctx, m):
    """Pairs {u, v} adjacent to every other vertex.  Returns (count, 'K2'|'2K1', H name) for the first."""
    n = ctx.n
    adj = ctx.adj(m)
    allv = (1 << n) - 1
    pairs = []
    for u, v in itertools.combinations(range(n), 2):
        rest = allv & ~(1 << u) & ~(1 << v)
        if adj[u] & rest == rest and adj[v] & rest == rest:
            pairs.append((u, v))
    if not pairs:
        return 0, None, None
    u, v = pairs[0]
    hv = [x for x in range(n) if x not in (u, v)]
    return len(pairs), ('K2' if (adj[u] >> v) & 1 else '2K1'), name_graph(n, adj, hv)


def has_spanning_k2_join_cycle(ctx, m):
    """True when G contains K2 join C_{n-2} as a spanning subgraph."""
    n = ctx.n
    adj = ctx.adj(m)
    allv = (1 << n) - 1
    for u, v in itertools.combinations(range(n), 2):
        if not (adj[u] >> v) & 1:
            continue
        rest = allv & ~(1 << u) & ~(1 << v)
        if adj[u] & rest != rest or adj[v] & rest != rest:
            continue
        hv = [x for x in range(n) if x not in (u, v)]
        s0 = hv[0]
        for p in itertools.permutations(hv[1:]):
            seq = (s0,) + p
            if all((adj[seq[i]] >> seq[(i + 1) % len(seq)]) & 1 for i in range(len(seq))):
                return True
    return False


# ------------------------------------------------------------------ steps


def classes_from_md(n):
    info = V.parse_md(n)
    return [(aut, el) for src, aut, el in info['lists'] if src == '|Aut| line']


def struct_row(ctx, m, label, prev_forms):
    n = ctx.n
    adj = ctx.adj(m)
    d = [V.popcount(x) for x in adj]
    f, a = V.canon(ctx, m)
    npairs, kind, hname = join_shape(ctx, m)
    core = kcore(n, adj, 4)
    core_m = sub_mask(ctx, m, core)
    core_e = V.popcount(core_m)
    core_name = '%dv/%de' % (len(core), core_e)
    if len(core) == n:
        core_name += ' (all)'
    tot, groups, multi, mx = cycle_stats(ctx, adj)
    # vertex deletions that give an extremal class of n-1
    dels = []
    if prev_forms:
        pctx = ctx_of(n - 1)
        for v in range(n):
            sm = sub_mask(ctx, m, [x for x in range(n) if x != v])
            if V.canon(pctx, sm)[0] in prev_forms:
                dels.append(v)
    span = has_spanning_k2_join_cycle(ctx, m)
    return {
        'label': label, 'aut': a, 'degseq': ''.join(map(str, sorted(d, reverse=True))),
        'ge5': sum(1 for x in d if x >= 5), 'univ': sum(1 for x in d if x == n - 1),
        'pairs': npairs, 'kind': kind, 'H': hname, 'span': span, 'core': core_name,
        'cycles': tot, 'groups': groups, 'multi': multi, 'maxgroup': mx,
        'dels': len(dels), 'mindeg': min(d), 'form': f,
    }


def step_struct(args, state):
    t0 = time.time()
    out = ['', '## 1. Structure of the known extremal graphs (n = 7, 8) and the n = 9 witness', '']
    out.append('Columns: degree sequence; vertices of degree >= 5; universal vertices (degree n-1); '
               '"dominating pairs" {u, v} adjacent to all other vertices (so G = K2 join H or 2K1 join H on the rest) and H for the first pair; '
               'spanning K2 join C_{n-2}; 4-core (vertices/edges); simple cycles; distinct cycle vertex sets ("groups"); groups holding >= 2 cycles; '
               'vertices v with G - v extremal for n - 1.')
    out.append('')
    out.append('| n | class (|Aut|) | degrees | deg>=5 | universal | dom. pairs: join, H | spans K2+C_{n-2} | 4-core | cycles | groups | groups >= 2 cycles (max) | G-v extremal |')
    out.append('|---|---|---|---|---|---|---|---|---|---|---|---|')
    forms7 = set()
    rows = {}
    for n in (7, 8):
        ctx = ctx_of(n)
        cl = classes_from_md(n)
        rows[n] = []
        for i, (aut, el) in enumerate(cl):
            m = ctx.mask(el)
            r = struct_row(ctx, m, '%d.%d' % (n, i + 1), forms7 if n == 8 else None)
            assert r['aut'] == aut
            rows[n].append(r)
            out.append('| %d | %s (%d) | %s | %d | %d | %s | %s | %s | %d | %d | %d (%d) | %s |' % (
                n, r['label'], r['aut'], r['degseq'], r['ge5'], r['univ'],
                ('%d: %s, H = %s' % (r['pairs'], r['kind'], r['H'])) if r['pairs'] else '0',
                'yes' if r['span'] else 'no', r['core'], r['cycles'], r['groups'], r['multi'], r['maxgroup'],
                str(r['dels']) if n == 8 else '-'))
        if n == 7:
            forms7 = {r['form'] for r in rows[7]}
    if args.edges:
        ctx = ctx_of(9)
        m = ctx.mask(ast.literal_eval(args.edges))
        r = struct_row(ctx, m, '9.w', None)
        out.append('| 9 | %s (%d) | %s | %d | %d | %s | %s | %s | %d | %d | %d (%d) | - |' % (
            r['label'], r['aut'], r['degseq'], r['ge5'], r['univ'],
            ('%d: %s, H = %s' % (r['pairs'], r['kind'], r['H'])) if r['pairs'] else '0',
            'yes' if r['span'] else 'no', r['core'], r['cycles'], r['groups'], r['multi'], r['maxgroup']))
    r8 = rows[8]
    two7 = sum(1 for r in r8 if r['univ'] == 2)
    out.append('')
    out.append('- n = 8: %d of 12 classes have exactly two vertices of degree 7; universal-vertex counts %s; '
               'dominating-pair counts %s; join types %s; min degree %s; classes with a vertex v such that G - v = C5 join K2: %d.'
               % (two7, sorted(r['univ'] for r in r8), sorted(r['pairs'] for r in r8),
                  sorted(set(str(r['kind']) for r in r8)), sorted(r['mindeg'] for r in r8),
                  sum(1 for r in r8 if r['dels'] > 0)))
    out.append('- struct step %.1f s' % (time.time() - t0))
    append('\n'.join(out))
    state['struct'] = [{k: v for k, v in r.items() if k != 'form'} for r in r8]
    return True


def step_witness(args, state):
    el = ast.literal_eval(args.edges)
    n = 1 + max(max(e) for e in el)
    ctx = ctx_of(n)
    m = ctx.mask(el)
    t0 = time.time()
    w, g2, g3 = good3(ctx, m)
    f, a = V.canon(ctx, m)
    tot, groups, multi, mx = cycle_stats(ctx, ctx.adj(m))
    npairs, kind, hname = join_shape(ctx, m)
    line = ('- witness n = %d, %d edges, degrees %s: find_pair %s; erdos585_small.is_good_full %s; brute force %s; '
            '|Aut| = %d; %d cycles in %d vertex-set groups (%d groups with >= 2 cycles, max %d); dominating pairs %d (%s join %s); %.1f s'
            % (n, len(el), sorted(degs(ctx, m), reverse=True),
               'good' if w is None else 'BAD ' + V.fmt_witness(ctx, w), 'good' if g2 else 'BAD',
               'not run' if g3 is None else ('good' if g3 else 'BAD'), a, tot, groups, multi, mx,
               npairs, kind, hname, time.time() - t0))
    append(line)
    print(line)
    return w is None and g2 and g3 is not False


def step_kfam(args, state):
    out = ['', '## 2a. K2 join C_{n-2} (3n - 5 edges), n = 9..12', '']
    append('\n'.join(out))
    for n in (9, 10, 11, 12):
        ctx = ctx_of(n)
        m = V.join_k2(ctx, n - 2)
        t0 = time.time()
        adj = ctx.adj(m)
        w = V.find_pair(ctx, adj)
        tot, groups, multi, mx = cycle_stats(ctx, adj)
        t1 = time.time() - t0
        t0 = time.time()
        edges, E = S.edge_index(n)
        g2 = S.is_good_full(n, S.adj_from_mask(n, m, edges), E)
        t2 = time.time() - t0
        out.append('- n = %d: %d edges (3n - 5 = %d); find_pair: %s; erdos585_small.is_good_full: %s; '
                   '%d cycles, %d vertex-set groups, %d with >= 2 cycles (max %d); %.1f s + %.1f s'
                   % (n, V.popcount(m), 3 * n - 5, 'no pair' if w is None else 'PAIR ' + V.fmt_witness(ctx, w),
                      'good' if g2 else 'BAD', tot, groups, multi, mx, t1, t2))
        append(out[-1])
        print(out[-1], flush=True)
    return True


def _ext_task(job):
    n, base, subsets = job
    ctx = ctx_of(n)
    good, bad, badw = [], 0, 0
    for sub in subsets:
        m = base
        for s in sub:
            m |= ctx.ebit[n - 1][s]
        w = V.find_pair(ctx, ctx.adj(m))
        if w is None:
            good.append(m)
        else:
            bad += 1
            badw += V.witness_ok(ctx, m, w)
    return good, bad, badw


def closure(ctx, seeds, procs, deadline):
    """All good supergraphs reachable from the good seeds by adding edges, by canonical form."""
    level = {}
    for m in seeds:
        f, a = V.canon(ctx, m)
        level[f] = a
    best = {}
    allforms = dict(level)
    while level:
        e = V.popcount(next(iter(level)))
        best[e] = len(level)
        nxt = {}
        for f in level:
            for i in range(ctx.N):
                b = 1 << i
                if f & b:
                    continue
                m = f | b
                if V.find_pair(ctx, ctx.adj(m)) is None:
                    g, a = V.canon(ctx, m)
                    nxt[g] = a
        level = nxt
        allforms.update(nxt)
        if time.time() > deadline:
            break
    return best, allforms


def step_ext(args, state):
    """New vertex 8 joined to every k-subset of each n = 8 extremal class, k = 3, 4, 5."""
    t0 = time.time()
    ctx8, ctx9 = ctx_of(8), ctx_of(9)
    cl = classes_from_md(8)
    out = ['', '## 2b. One-vertex extensions of the 12 extremal classes for n = 8', '']
    append('\n'.join(out))
    res = state.setdefault('ext', {})
    goods = {}
    for k in (3, 4, 5):
        jobs = []
        for aut, el in cl:
            base = ctx9.mask(ctx8.edges(ctx8.mask(el)))
            jobs.append((9, base, list(itertools.combinations(range(8), k))))
        good, bad, badw = [], 0, 0
        with Pool(min(args.procs, len(jobs))) as pool:
            for g, b, bw in pool.imap_unordered(_ext_task, jobs):
                good.extend(g)
                bad += b
                badw += bw
        forms = {}
        for m in good:
            f, a = V.canon(ctx9, m)
            forms[f] = a
        goods[k] = forms
        lab = sum(math.factorial(9) // a for a in forms.values())
        out.append('- degree-%d new vertex: %d graphs with %d edges (12 x C(8,%d)); good: %d, in %d isomorphism classes; '
                   'bad: %d, witnesses verified: %d'
                   % (k, 12 * math.comb(8, k), 19 + k, k, len(good), len(forms), bad, badw))
        res[str(k)] = {'graphs': 12 * math.comb(8, k), 'good': len(good), 'classes': len(forms), 'bad': bad, 'badw': badw,
                       'forms': sorted([f, a] for f, a in forms.items())}
        save_state(args.state, state)
        append(out[-1])
        print(out[-1], flush=True)
    # closure: add any edge to the good 22-edge extensions, keep good, repeat
    best, allforms = closure(ctx9, list(goods[3]), args.procs, time.time() + 120)
    line = ('- add-edge closure from the %d good degree-3 classes (22 edges): good classes per edge count %s; maximum %d edges'
            % (len(goods[3]), json.dumps(best), max(int(e) for e in best)))
    out.append(line)
    append(line)
    print(line, flush=True)
    top = max(best)
    tops = sorted(f for f in allforms if V.popcount(f) == top)
    for f in tops:
        append('  - %d-edge class from the closure (|Aut| %d): %s' % (top, allforms[f], ctx9.edges(f)))
    res['closure'] = {'best': best, 'top': [[f, allforms[f]] for f in tops]}
    append('- extension step %.1f s' % (time.time() - t0))
    return True


# ------------------------------------------------------------------ levels


def _level_task(job):
    n, idx, parents = job
    ctx = ctx_of(n)
    out = {}
    for m in parents:
        for e in range(ctx.N):
            b = 1 << e
            if m & b:
                continue
            f, a = V.canon(ctx, m | b)
            old = out.get(f)
            if old is None:
                out[f] = a
            elif old != a:
                raise AssertionError('|Aut| disagrees for one canonical form')
    return idx, out


def step_levels(args, state):
    n, kmax = args.n, args.k
    ctx = ctx_of(n)
    key = 'levels%d' % n
    lv = state.setdefault(key, {})
    t_start = time.time()
    deadline = t_start + args.budget
    if '0' not in lv:
        f, a = V.canon(ctx, 0)
        lv['0'] = [[f, a]]
        save_state(args.state, state)
    fact = math.factorial(n)
    while True:
        k = max(int(x) for x in lv)
        if k >= kmax:
            return True
        parents = [f for f, a in lv[str(k)]]
        part = state.get('partial')
        if not part or part.get('n') != n or part.get('k') != k + 1:
            part = {'n': n, 'k': k + 1, 'done': [], 'forms': {}, 'seconds': 0.0}
            state['partial'] = part
        CH = args.chunk
        chunks = [parents[i:i + CH] for i in range(0, len(parents), CH)]
        done = set(part['done'])
        todo = [(n, i, chunks[i]) for i in range(len(chunks)) if i not in done]
        forms = {int(f): a for f, a in part['forms'].items()}
        t = time.time()
        stopped = False
        last_save = time.time()
        with Pool(args.procs) as pool:
            for idx, res in pool.imap_unordered(_level_task, todo):
                for f, a in res.items():
                    old = forms.get(f)
                    if old is None:
                        forms[f] = a
                    elif old != a:
                        raise AssertionError('|Aut| disagrees across chunks')
                part['done'].append(idx)
                if time.time() - last_save > 20 or time.time() > deadline:
                    part['forms'] = {str(f): a for f, a in forms.items()}
                    part['seconds'] = part.get('seconds', 0.0) + (time.time() - t)
                    t = time.time()
                    save_state(args.state, state)
                    last_save = time.time()
                if time.time() > deadline:
                    stopped = True
                    pool.terminate()
                    break
        part['forms'] = {str(f): a for f, a in forms.items()}
        if stopped:
            part['seconds'] = part.get('seconds', 0.0) + (time.time() - t)
            save_state(args.state, state)
            line = ('- progress n = %d, level %d: %d/%d chunks done, %d classes so far; checkpointed, rerun to resume'
                    % (n, k + 1, len(part['done']), len(chunks), len(forms)))
            append(line)
            print(line, flush=True)
            return False
        secs = part.get('seconds', 0.0) + (time.time() - t)
        lv[str(k + 1)] = sorted([f, a] for f, a in forms.items())
        state['partial'] = None
        save_state(args.state, state)
        labelled = sum(fact // a for _, a in lv[str(k + 1)])
        want = A008406.get((n, k + 1))
        line = ('- n = %d, level %d edges: %d classes from %d parents (OEIS A008406: %s); sum %d!/|Aut| = %d vs C(%d,%d) = %d (%s); %.1f s on %d processes'
                % (n, k + 1, len(forms), len(parents), want if want is not None else 'n/a', n, labelled, ctx.N, k + 1,
                   math.comb(ctx.N, k + 1), 'match' if labelled == math.comb(ctx.N, k + 1) else 'MISMATCH', secs, args.procs))
        append(line)
        print(line, flush=True)
        if time.time() > deadline:
            return k + 1 >= kmax


# ------------------------------------------------------------------ complements


def _comp_task(job):
    n, idx, reps = job
    ctx = ctx_of(n)
    good = []
    bad = 0
    badw = 0
    sizes = {}
    mindeg = {}
    for f, a in reps:
        comp = ctx.full ^ f
        adj = ctx.adj(comp)
        d = min(V.popcount(x) for x in adj)
        w = V.find_pair(ctx, adj)
        if w is None:
            good.append((comp, a))
        else:
            bad += 1
            badw += V.witness_ok(ctx, comp, w)
            s = V.popcount(w[0])
            sizes[s] = sizes.get(s, 0) + 1
            mindeg[d] = mindeg.get(d, 0) + 1
    return idx, good, bad, badw, sizes, mindeg


def step_comp(args, state):
    n, k = args.n, args.k
    ctx = ctx_of(n)
    reps = state['levels%d' % n][str(k)]
    key = 'comp%d_%d' % (n, k)
    st = state.get(key)
    if not st:
        st = state[key] = {'done': [], 'good': [], 'bad': 0, 'badw': 0, 'sizes': {}, 'mindeg': {}, 'seconds': 0.0}
    CH = args.chunk
    chunks = [reps[i:i + CH] for i in range(0, len(reps), CH)]
    done = set(st['done'])
    todo = [(n, i, chunks[i]) for i in range(len(chunks)) if i not in done]
    t = time.time()
    deadline = t + args.budget
    stopped = False
    with Pool(args.procs) as pool:
        for idx, good, bad, badw, sizes, mindeg in pool.imap_unordered(_comp_task, todo):
            st['done'].append(idx)
            st['good'].extend([[c, a] for c, a in good])
            st['bad'] += bad
            st['badw'] += badw
            for s, c in sizes.items():
                st['sizes'][str(s)] = st['sizes'].get(str(s), 0) + c
            for s, c in mindeg.items():
                st['mindeg'][str(s)] = st['mindeg'].get(str(s), 0) + c
            if time.time() > deadline:
                stopped = True
                pool.terminate()
                break
    st['seconds'] += time.time() - t
    save_state(args.state, state)
    if stopped:
        line = '- progress complements n = %d, k = %d: %d/%d chunks; rerun to resume' % (n, k, len(st['done']), len(chunks))
        append(line)
        print(line, flush=True)
        return False
    fact = math.factorial(n)
    lab_good = sum(fact // a for _, a in st['good'])
    goods = sorted(st['good'])
    line = ('- complements of the %d classes of %d-edge graphs on %d vertices (%d edges each): bad %d (witness verified %d), good %d '
            '(%d labelled); witness vertex-set sizes %s; bad complements by min degree %s; %.1f s on %d processes'
            % (len(reps), k, n, ctx.N - k, st['bad'], st['badw'], len(goods), lab_good,
               json.dumps(dict(sorted(st['sizes'].items()))), json.dumps(dict(sorted(st['mindeg'].items()))),
               st['seconds'], args.procs))
    append(line)
    print(line, flush=True)
    for c, a in goods[:args.list]:
        dd = sorted(degs(ctx, c), reverse=True)
        npairs, kind, hname = join_shape(ctx, c)
        append('  - good: |Aut| %d, degrees %s, dominating pairs %d (%s join %s): %s'
               % (a, ''.join(map(str, dd)), npairs, kind, hname, ctx.edges(c)))
    return True


def step_ext10(args, state):
    """New vertex joined to k-subsets of each good class stored by comp (n = 9, 23 edges)."""
    t0 = time.time()
    key = 'comp9_%d' % args.k
    goods = state[key]['good']
    ctx9, ctx10 = ctx_of(9), ctx_of(10)
    out = ['', '## 4b. f(10) lower bound: one-vertex extensions of the n = 9 extremal classes', '']
    append('\n'.join(out))
    best_forms = {}
    for deg in (3, 4, 5):
        jobs = []
        for c, a in goods:
            base = ctx10.mask(ctx9.edges(c))
            jobs.append((10, base, list(itertools.combinations(range(9), deg))))
        good, bad, badw = [], 0, 0
        with Pool(min(args.procs, max(1, len(jobs)))) as pool:
            for g, b, bw in pool.imap_unordered(_ext_task, jobs):
                good.extend(g)
                bad += b
                badw += bw
        forms = {}
        for m in good:
            f, a = V.canon(ctx10, m)
            forms[f] = a
        best_forms[deg] = forms
        line = ('- degree-%d new vertex on each of the %d classes: %d graphs with %d edges; good %d in %d classes; bad %d (witness verified %d)'
                % (deg, len(goods), len(goods) * math.comb(9, deg), V.popcount(goods[0][0]) + deg if goods else 0,
                   len(good), len(forms), bad, badw))
        out.append(line)
        append(line)
        print(line, flush=True)
        if not forms:
            break
    top = max(d for d in best_forms if best_forms[d])
    forms = best_forms[top]
    f0 = sorted(forms)[0]
    append('  - witness (%d edges, |Aut| %d, degrees %s): %s'
           % (V.popcount(f0), forms[f0], ''.join(map(str, sorted(degs(ctx10, f0), reverse=True))), ctx10.edges(f0)))
    state['ext10'] = {str(d): sorted([f, a] for f, a in fs.items()) for d, fs in best_forms.items()}
    save_state(args.state, state)
    append('- ext10 step %.1f s' % (time.time() - t0))
    return True


def step_ext11(args, state):
    """New vertex joined to k-subsets of each 27-edge class stored by ext10 (n = 10, degree-4 extensions)."""
    t0 = time.time()
    src = state['ext10']['4']
    ctx10, ctx11 = ctx_of(10), ctx_of(11)
    append('\n## 4c. f(11) lower bound: one-vertex extensions of the 27-edge n = 10 classes from 4b\n')
    best = None
    for deg in (4, 5, 6):
        jobs = []
        for f, a in src:
            base = ctx11.mask(ctx10.edges(f))
            jobs.append((11, base, list(itertools.combinations(range(10), deg))))
        good, bad, badw = [], 0, 0
        with Pool(min(args.procs, max(1, len(jobs)))) as pool:
            for g, b, bw in pool.imap_unordered(_ext_task, jobs):
                good.extend(g)
                bad += b
                badw += bw
        forms = {}
        for m in good:
            f, a = V.canon(ctx11, m)
            forms[f] = a
        line = ('- degree-%d new vertex on each of the %d classes: %d graphs with %d edges; good %d in %d classes; bad %d (witness verified %d); %.1f s'
                % (deg, len(src), len(src) * math.comb(10, deg), 27 + deg, len(good), len(forms), bad, badw, time.time() - t0))
        append(line)
        print(line, flush=True)
        if not forms:
            break
        best = (deg, forms)
        state['ext11_%d' % deg] = sorted([f, a] for f, a in forms.items())
        save_state(args.state, state)
    if best:
        deg, forms = best
        f0 = sorted(forms)[0]
        append('  - witness (%d edges, |Aut| %d, degrees %s): %s'
               % (V.popcount(f0), forms[f0], ''.join(map(str, sorted(degs(ctx11, f0), reverse=True))), ctx11.edges(f0)))
    return True


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('step', choices=['struct', 'witness', 'kfam', 'ext', 'levels', 'comp', 'ext10', 'ext11'])
    ap.add_argument('--state', required=True)
    ap.add_argument('--n', type=int, default=9)
    ap.add_argument('--k', type=int, default=12)
    ap.add_argument('--procs', type=int, default=8)
    ap.add_argument('--chunk', type=int, default=100)
    ap.add_argument('--budget', type=float, default=200.0)
    ap.add_argument('--edges', default=None)
    ap.add_argument('--list', type=int, default=0, help='list this many good graphs')
    args = ap.parse_args()
    state = load_state(args.state)
    fn = {'struct': step_struct, 'witness': step_witness, 'kfam': step_kfam, 'ext': step_ext,
          'levels': step_levels, 'comp': step_comp, 'ext10': step_ext10, 'ext11': step_ext11}[args.step]
    ok = fn(args, state)
    save_state(args.state, state)
    sys.exit(0 if ok else 3)


if __name__ == '__main__':
    main()
