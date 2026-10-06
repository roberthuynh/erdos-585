#!/usr/bin/env python3
"""Independent check of f(7) = 16 and f(8) = 19 for Erdos problem 585.

f(n) = max number of edges of a simple graph on n vertices with no two
edge-disjoint cycles (simple cycles, >= 3 vertices) on the same vertex set.
A graph is "bad" if it has such a pair, "good" otherwise.  Adding edges keeps a
bad graph bad, so f(n) = m holds exactly when (a) some m-edge graph is good and
(b) every (m+1)-edge graph is bad.

Written from scratch for this check: it does not import or copy
computations/erdos585_small.py.  Python 3 standard library only.

Each step appends its section to computations/585-verify.md as soon as it is known.
Level-by-level isomorphism classes (n = 8) and step results are checkpointed
in the --state JSON file, so an interrupted step resumes where it stopped.
"""

import argparse
import ast
import itertools
import json
import math
import os
import platform
import random
import re
import sys
import tempfile
import time

HERE = os.path.dirname(os.path.abspath(__file__))
REPORT = os.path.join(HERE, '585-verify.md')
SOURCE_MD = os.path.join(HERE, '585-small-n.md')
CLAIM = {7: 16, 8: 19}
# Number of graphs on n vertices with k edges up to isomorphism (OEIS A008406),
# used only as an outside cross-check of the class counts produced here.
A008406 = {(7, 4): 10, (7, 5): 21, (8, 8): 221, (8, 9): 402}

HEADER = """# Erdos 585, small n: independent check of f(7) = 16 and f(8) = 19

Written from scratch in `computations/erdos585_verify.py` (Python 3 standard library only). `computations/erdos585_small.py` was not imported, copied or consulted for its search code.
Definitions as in `585-small-n.md`: a graph is **bad** if it has two edge-disjoint cycles (simple, >= 3 vertices) on the same vertex set, **good** otherwise. Adding edges keeps a bad graph bad, so f(n) = m holds exactly when some m-edge graph is good (lower bound) and every (m+1)-edge graph is bad (upper bound).

Method:
- Checker: DFS from the minimum vertex s of each cycle through vertices > s (vertex and edge bitmasks), closing back to s only when the last vertex exceeds the second, so each cycle appears once; cycles are grouped by vertex-set mask and a pair is two disjoint edge masks in one group.
- Every bad verdict carries a witness that a separate routine re-checks: both edge sets lie in G, are disjoint, and are each 2-regular and connected on exactly the shared vertex set.
- Brute-force cross-check: every vertex subset S and every cyclic order of S (min(S) first, one direction), then an all-pairs test (literal over the whole cycle list for n <= 7 random tests and the Petersen graph, within vertex-set buckets for n = 8 and the reported lists).
- Isomorphism reduction: color refinement from degrees, then the minimum edge mask over all relabelings that keep the color classes in color order; the number of relabelings that reach the minimum is |Aut|. Class lists are cross-checked by sum n!/|Aut| = number of labeled graphs and against OEIS A008406.
- Times are wall-clock seconds, CPython %s, one core.

Sections are appended as each step finishes.
"""

# ------------------------------------------------------------------ report io


def append(text):
    if not os.path.exists(REPORT):
        with open(REPORT, 'w') as fh:
            fh.write(HEADER % platform.python_version())
    with open(REPORT, 'a') as fh:
        fh.write(text.rstrip('\n') + '\n')


def load_state(path):
    if os.path.exists(path):
        with open(path) as fh:
            return json.load(fh)
    return {'levels': {}, 'results': {}}


def save_state(path, state):
    tmp = path + '.tmp'
    with open(tmp, 'w') as fh:
        json.dump(state, fh)
    os.replace(tmp, path)


def popcount(x):
    return bin(x).count('1')


# ------------------------------------------------------------------ graphs


class Ctx:
    """Edge indexing for simple graphs on vertices 0..n-1 (edge masks are ints)."""

    def __init__(self, n):
        self.n = n
        self.pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
        self.N = len(self.pairs)
        self.ebit = [[0] * n for _ in range(n)]
        for k, (i, j) in enumerate(self.pairs):
            self.ebit[i][j] = self.ebit[j][i] = 1 << k
        self.full = (1 << self.N) - 1

    def edges(self, m):
        out = []
        k = 0
        while m:
            if m & 1:
                out.append(self.pairs[k])
            m >>= 1
            k += 1
        return out

    def adj(self, m):
        a = [0] * self.n
        for i, j in self.edges(m):
            a[i] |= 1 << j
            a[j] |= 1 << i
        return a

    def mask(self, edge_list):
        m = 0
        for u, v in edge_list:
            if not (0 <= u < self.n and 0 <= v < self.n) or u == v:
                raise ValueError('bad edge %r' % ((u, v),))
            b = self.ebit[u][v]
            if m & b:
                raise ValueError('repeated edge %r' % ((u, v),))
            m |= b
        return m

    def relabel(self, m, perm):
        f = 0
        for u, v in self.edges(m):
            f |= self.ebit[perm[u]][perm[v]]
        return f


# ------------------------------------------------------------------ checker


def dfs_cycles(ctx, adj):
    """Yield (vertex_mask, edge_mask) once for every simple cycle with >= 3 vertices.

    A cycle is grown from its minimum vertex s through vertices > s and closed
    back to s only when the last vertex is larger than the second vertex, which
    keeps exactly one of its two traversal directions."""
    n = ctx.n
    ebit = ctx.ebit
    allv = (1 << n) - 1
    for s in range(n):
        higher = allv & ~((2 << s) - 1)
        adj_s = adj[s]
        row_s = ebit[s]
        stack = []
        m = adj_s & higher
        while m:
            low = m & -m
            m ^= low
            a = low.bit_length() - 1
            stack.append((a, (1 << s) | low, row_s[a], a))
        while stack:
            v, vm, em, first = stack.pop()
            if v > first and (adj_s >> v) & 1:
                yield vm, em | row_s[v]
            ext = adj[v] & higher & ~vm
            row_v = ebit[v]
            while ext:
                low = ext & -ext
                ext ^= low
                w = low.bit_length() - 1
                stack.append((w, vm | low, em | row_v[w], first))


def find_pair(ctx, adj):
    """(vertex_mask, edge_mask_1, edge_mask_2) of a pair of edge-disjoint cycles
    on the same vertex set, or None when the graph is good."""
    groups = {}
    for vm, em in dfs_cycles(ctx, adj):
        lst = groups.get(vm)
        if lst is None:
            groups[vm] = [em]
            continue
        for f in lst:
            if not f & em:
                return vm, f, em
        lst.append(em)
    return None


def naive_cycles(ctx, adj):
    """Brute force: every subset S (|S| >= 3) and every cyclic order of S that
    starts at min(S) with seq[1] < seq[-1]; keep the orders whose consecutive
    vertices are all adjacent."""
    n = ctx.n
    ebit = ctx.ebit
    out = []
    for k in range(3, n + 1):
        for S in itertools.combinations(range(n), k):
            vm = 0
            for v in S:
                vm |= 1 << v
            s0 = S[0]
            for p in itertools.permutations(S[1:]):
                if p[0] > p[-1]:
                    continue
                seq = (s0,) + p
                ok = True
                for i in range(k):
                    if not (adj[seq[i]] >> seq[(i + 1) % k]) & 1:
                        ok = False
                        break
                if ok:
                    em = 0
                    for i in range(k):
                        em |= ebit[seq[i]][seq[(i + 1) % k]]
                    out.append((vm, em))
    return out


def naive_pair(cycles):
    """Literal all-pairs test over a cycle list."""
    L = len(cycles)
    for i in range(L):
        vi, ei = cycles[i]
        for j in range(i + 1, L):
            vj, ej = cycles[j]
            if vi == vj and not ei & ej:
                return vi, ei, ej
    return None


def naive_pair_grouped(cycles):
    """All pairs inside each vertex-set bucket (same answer, fewer comparisons)."""
    buckets = {}
    for vm, em in cycles:
        buckets.setdefault(vm, []).append(em)
    for vm, ems in buckets.items():
        for i in range(len(ems)):
            for j in range(i + 1, len(ems)):
                if not ems[i] & ems[j]:
                    return vm, ems[i], ems[j]
    return None


def is_cycle_on(ctx, em, vm):
    """True when edge mask em is one simple cycle whose vertex set is exactly vm."""
    nb = {}
    for u, v in ctx.edges(em):
        nb.setdefault(u, []).append(v)
        nb.setdefault(v, []).append(u)
    verts = sorted(nb)
    if len(verts) < 3 or sum(1 << v for v in verts) != vm:
        return False
    if any(len(x) != 2 for x in nb.values()):
        return False
    seen = {verts[0]}
    todo = [verts[0]]
    while todo:
        x = todo.pop()
        for y in nb[x]:
            if y not in seen:
                seen.add(y)
                todo.append(y)
    return len(seen) == len(verts)


def witness_ok(ctx, gm, w):
    vm, e1, e2 = w
    return (not e1 & e2 and not e1 & ~gm and not e2 & ~gm
            and is_cycle_on(ctx, e1, vm) and is_cycle_on(ctx, e2, vm))


def cycle_seq(ctx, em):
    nb = {}
    for u, v in ctx.edges(em):
        nb.setdefault(u, []).append(v)
        nb.setdefault(v, []).append(u)
    start = min(nb)
    seq = [start]
    prev, cur = None, start
    while True:
        a, b = nb[cur]
        nxt = a if a != prev else b
        if nxt == start:
            break
        seq.append(nxt)
        prev, cur = cur, nxt
    return seq


def fmt_witness(ctx, w):
    if w is None:
        return 'none'
    vm, e1, e2 = w
    s1 = cycle_seq(ctx, e1)
    s2 = cycle_seq(ctx, e2)
    return '%s and %s' % ('-'.join(map(str, s1 + s1[:1])), '-'.join(map(str, s2 + s2[:1])))


# ------------------------------------------------------------------ canonical form


def refine(n, adj):
    """Color refinement starting from degrees.  Colors are ranks of
    isomorphism-invariant signatures, so the ordered partition is canonical."""
    nbrs = [[w for w in range(n) if (adj[v] >> w) & 1] for v in range(n)]
    color = [len(x) for x in nbrs]
    ranks = sorted(set(color))
    color = [ranks.index(c) for c in color]
    ncol = len(ranks)
    while True:
        sig = [(color[v], tuple(sorted(color[w] for w in nbrs[v]))) for v in range(n)]
        uniq = sorted(set(sig))
        color = [uniq.index(s) for s in sig]
        if len(uniq) == ncol:
            return color
        ncol = len(uniq)


def canon(ctx, m):
    """(canonical edge mask, |Aut|).

    The form is the minimum edge mask over every relabeling that sends the
    color classes of `refine` to consecutive position blocks in color order.
    Refinement is isomorphism-invariant, so isomorphic graphs get the same
    form; the form is itself a relabeling of the graph, so equal forms imply
    isomorphic graphs.  Automorphisms preserve colors, so the number of these
    relabelings that reach the minimum is |Aut|."""
    n = ctx.n
    adj = ctx.adj(m)
    color = refine(n, adj)
    cells = {}
    for v in range(n):
        cells.setdefault(color[v], []).append(v)
    pos = [0] * n
    free = []
    off = 0
    for c in sorted(cells):
        cell = cells[c]
        if len(cell) == 1:
            pos[cell[0]] = off
        else:
            free.append((cell, list(itertools.permutations(range(off, off + len(cell))))))
        off += len(cell)
    edges = ctx.edges(m)
    ebit = ctx.ebit
    best = -1
    count = 0
    free_cells = [c for c, _ in free]
    for choice in itertools.product(*[p for _, p in free]):
        for cell, perm in zip(free_cells, choice):
            for v, p in zip(cell, perm):
                pos[v] = p
        f = 0
        for u, v in edges:
            f |= ebit[pos[u]][pos[v]]
        if best < 0 or f < best:
            best = f
            count = 1
        elif f == best:
            count += 1
    return best, count


def aut_bruteforce(ctx, m):
    c = 0
    for perm in itertools.permutations(range(ctx.n)):
        if ctx.relabel(m, perm) == m:
            c += 1
    return c


def gen_levels(ctx, kmax, state, state_path, deadline, log):
    """Isomorphism classes of k-edge graphs on ctx.n vertices for k = 0..kmax,
    by adding every non-edge to every class representative of level k-1 and
    deduplicating by canonical form.  Checkpoints after every level."""
    key = str(ctx.n)
    levels = state['levels'].setdefault(key, {})
    if '0' not in levels:
        f, a = canon(ctx, 0)
        levels['0'] = [[f, a]]
        save_state(state_path, state)
    k = max(int(x) for x in levels)
    fact = math.factorial(ctx.n)
    while k < kmax:
        if time.time() > deadline:
            return False
        t = time.time()
        new = {}
        extensions = 0
        for m, _ in levels[str(k)]:
            for e in range(ctx.N):
                b = 1 << e
                if m & b:
                    continue
                extensions += 1
                f, a = canon(ctx, m | b)
                old = new.get(f)
                if old is None:
                    new[f] = a
                elif old != a:
                    raise AssertionError('|Aut| disagrees for one canonical form')
        k += 1
        levels[str(k)] = sorted([f, a] for f, a in new.items())
        labeled = sum(fact // a for _, a in levels[str(k)])
        save_state(state_path, state)
        log('- progress n = %d, level %d edges: %d classes from %d extensions; sum %d!/|Aut| = %d vs C(%d,%d) = %d (%s); %.2f s'
            % (ctx.n, k, len(new), extensions, ctx.n, labeled, ctx.N, k, math.comb(ctx.N, k),
               'match' if labeled == math.comb(ctx.N, k) else 'MISMATCH', time.time() - t))
    return True


# ------------------------------------------------------------------ steps


def step_selftest(args, state):
    t0 = time.time()
    lines = ['', '## 1. Self-tests', '']
    allok = True

    def check(name, cond, detail=''):
        nonlocal allok
        allok = allok and bool(cond)
        lines.append('- %s: **%s**%s' % (name, 'PASS' if cond else 'FAIL', ('; ' + detail) if detail else ''))

    c5 = Ctx(5)
    k5 = c5.full
    w = find_pair(c5, c5.adj(k5))
    check('K5 has a pair', w is not None and witness_ok(c5, k5, w) and popcount(w[0]) == 5,
          'witness %s' % fmt_witness(c5, w))
    k5e = k5 & ~c5.ebit[0][1]
    w = find_pair(c5, c5.adj(k5e))
    nw = naive_pair(naive_cycles(c5, c5.adj(k5e)))
    check('K5 minus an edge has no pair (DFS and brute force)', w is None and nw is None)

    c6 = Ctx(6)
    octa = c6.full & ~(c6.ebit[0][1] | c6.ebit[2][3] | c6.ebit[4][5])
    oadj = c6.adj(octa)
    w = find_pair(c6, oadj)
    ocyc = naive_cycles(c6, oadj)
    small = [x for x in ocyc if popcount(x[0]) < 6]
    check('K6 minus a perfect matching (octahedron) has a pair of Hamiltonian cycles',
          w is not None and witness_ok(c6, octa, w) and popcount(w[0]) == 6
          and naive_pair_grouped(small) is None,
          'witness %s; brute force finds no pair on fewer than 6 vertices' % fmt_witness(c6, w))

    c10 = Ctx(10)
    pet = [(i, (i + 1) % 5) for i in range(5)] + [(5 + i, 5 + (i + 2) % 5) for i in range(5)] \
        + [(i, 5 + i) for i in range(5)]
    pm = c10.mask(pet)
    padj = c10.adj(pm)
    tp = time.time()
    dl = list(dfs_cycles(c10, padj))
    nl = naive_cycles(c10, padj)
    bylen = {}
    for vm, _ in dl:
        bylen[popcount(vm)] = bylen.get(popcount(vm), 0) + 1
    w = find_pair(c10, padj)
    nw = naive_pair(nl)
    check('Petersen graph: DFS cycle list equals the brute-force list',
          len(dl) == len(set(dl)) and set(dl) == set(nl) and len(nl) == len(set(nl)),
          '%d cycles' % len(dl))
    lines.append('- Petersen graph (report): cycles by length %s, %d total; pair: %s (DFS), %s (brute force); '
                 'expected none, since it is 3-regular and a pair on S needs degree >= 4 inside S; %.2f s'
                 % (', '.join('%d: %d' % (k, bylen[k]) for k in sorted(bylen)), len(dl),
                    'none' if w is None else fmt_witness(c10, w),
                    'none' if nw is None else fmt_witness(c10, nw), time.time() - tp))

    rng = random.Random(585)
    tr = time.time()
    stats = []
    rand_ok = []
    for n, trials in ((4, 60), (5, 200), (6, 200), (7, 150), (8, 80)):
        ctx = Ctx(n)
        agree = listeq = good = bad = wit = 0
        for _ in range(trials):
            p = rng.choice([0.3, 0.45, 0.6, 0.7, 0.8, 0.9, 1.0])
            m = 0
            for e in range(ctx.N):
                if rng.random() < p:
                    m |= 1 << e
            adj = ctx.adj(m)
            dl = list(dfs_cycles(ctx, adj))
            nl = naive_cycles(ctx, adj)
            if len(dl) == len(set(dl)) and set(dl) == set(nl) and len(nl) == len(set(nl)):
                listeq += 1
            w = find_pair(ctx, adj)
            nw = naive_pair(nl) if n <= 7 else naive_pair_grouped(nl)
            if (w is None) == (nw is None):
                agree += 1
            if w is None:
                good += 1
            else:
                bad += 1
            if (w is None or witness_ok(ctx, m, w)) and (nw is None or witness_ok(ctx, m, nw)):
                wit += 1
        ok = agree == listeq == wit == trials
        rand_ok.append(ok)
        stats.append('n = %d: %d graphs (%d good, %d bad); cycle lists equal %d/%d, verdicts agree %d/%d, witnesses valid %d/%d'
                     % (n, trials, good, bad, listeq, trials, agree, trials, wit, trials))
    check('random graphs, DFS checker vs brute force (%s for n <= 7, bucketed all-pairs for n = 8)'
          % 'literal all-pairs', all(rand_ok),
          '%.1f s' % (time.time() - tr))
    for s in stats:
        lines.append('  - ' + s)

    tc = time.time()
    cf_ok = aut_ok = 0
    cf_n = aut_n = 0
    for n, trials in ((6, 60), (7, 60), (8, 40)):
        ctx = Ctx(n)
        for t in range(trials):
            m = 0
            p = rng.choice([0.2, 0.35, 0.5, 0.65, 0.8])
            for e in range(ctx.N):
                if rng.random() < p:
                    m |= 1 << e
            perm = list(range(n))
            rng.shuffle(perm)
            f1, a1 = canon(ctx, m)
            f2, a2 = canon(ctx, ctx.relabel(m, perm))
            cf_n += 1
            if f1 == f2 and a1 == a2 and popcount(f1) == popcount(m):
                cf_ok += 1
            if n <= 7 or t < 6:
                aut_n += 1
                if aut_bruteforce(ctx, m) == a1:
                    aut_ok += 1
    check('canonical form invariant under random relabeling', cf_ok == cf_n, '%d/%d graphs on 6-8 vertices' % (cf_ok, cf_n))
    check('|Aut| from canon equals brute force over all n! permutations', aut_ok == aut_n,
          '%d/%d graphs; %.1f s' % (aut_ok, aut_n, time.time() - tc))
    lines.append('- self-test total %.1f s; overall **%s**' % (time.time() - t0, 'PASS' if allok else 'FAIL'))
    append('\n'.join(lines))
    state['results']['selftest'] = {'ok': allok, 'seconds': round(time.time() - t0, 2)}
    return allok


def parse_md(n):
    with open(SOURCE_MD) as fh:
        text = fh.read()
    m = re.search(r'^## n = %d[ \t]*\n(.*?)(?=^## |\Z)' % n, text, re.M | re.S)
    if not m:
        return None
    sec = m.group(1)
    lists = []
    first = re.search(r'extremal graph \(edge list\): (\[.*?\]);', sec)
    if first:
        lists.append(('edge-list line', None, ast.literal_eval(first.group(1))))
    for mm in re.finditer(r'^\s*- \|Aut\| = (\d+): (\[.*\])\s*$', sec, re.M):
        lists.append(('|Aut| line', int(mm.group(1)), ast.literal_eval(mm.group(2))))
    cls = re.search(r'extremal graphs: (\d+) isomorphism classes', sec)
    lab = re.search(r'(\d+) labeled graphs', sec)
    return {'lists': lists, 'classes': int(cls.group(1)) if cls else None,
            'labeled': int(lab.group(1)) if lab else None}


def join_k2(ctx, cyc_len):
    """C_k join K2 on vertices 0..k+1 (cycle 0..k-1, then x = k, y = k+1)."""
    k = cyc_len
    edges = [(i, (i + 1) % k) for i in range(k)] + [(k, k + 1)] + [(i, k) for i in range(k)] + [(i, k + 1) for i in range(k)]
    return ctx.mask(edges)


def step_lower(args, state):
    t0 = time.time()
    lines = ['', '## 2. Lower bounds: the edge lists in 585-small-n.md', '']
    res = {}
    for n in (7, 8):
        ctx = Ctx(n)
        info = parse_md(n)
        fact = math.factorial(n)
        if info is None or not info['lists']:
            lines.append('- n = %d: no edge list found in 585-small-n.md' % n)
            res[str(n)] = {'ok': False}
            continue
        forms = {}
        rows = []
        allgood = True
        for src, claimed_aut, el in info['lists']:
            m = ctx.mask(el)
            w = find_pair(ctx, ctx.adj(m))
            nw = naive_pair_grouped(naive_cycles(ctx, ctx.adj(m)))
            f, a = canon(ctx, m)
            good = w is None and nw is None and popcount(m) == CLAIM[n]
            allgood = allgood and good
            if src == '|Aut| line':
                forms.setdefault(f, []).append((claimed_aut, a))
            rows.append('  - %s: %d edges, %s by DFS, %s by brute force; |Aut| = %d%s'
                        % (src, popcount(m), 'good' if w is None else 'BAD ' + fmt_witness(ctx, w),
                           'good' if nw is None else 'BAD', a,
                           '' if claimed_aut is None else (' (reported %d, %s)' % (claimed_aut, 'match' if claimed_aut == a else 'MISMATCH'))))
        aut_lines = [x for x in info['lists'] if x[0] == '|Aut| line']
        distinct = len(forms) == len(aut_lines)
        labeled = sum(fact // v[0][1] for v in forms.values())
        auts_match = all(ca == a for v in forms.values() for ca, a in v)
        jm = join_k2(ctx, n - 2)
        jf, ja = canon(ctx, jm)
        jw = find_pair(ctx, ctx.adj(jm))
        lines.append('- n = %d: %d list(s) parsed (%d |Aut| lines); all have %d edges and are good by both checkers: **%s**; '
                     '|Aut| lines pairwise non-isomorphic: %s (%d classes, reported %s); sum %d!/|Aut| = %d (reported %s); reported |Aut| all match: %s'
                     % (n, len(info['lists']), len(aut_lines), CLAIM[n], 'yes' if allgood else 'NO',
                        'yes' if distinct else 'NO', len(forms), info['classes'], n, labeled, info['labeled'],
                        'yes' if auts_match else 'NO'))
        lines.extend(rows)
        lines.append('  - C%d join K2 built here: %d edges, %s, |Aut| = %d, isomorphic to a reported class: %s'
                     % (n - 2, popcount(jm), 'good' if jw is None else 'BAD', ja, 'yes' if jf in forms else 'no'))
        res[str(n)] = {'ok': allgood, 'distinct': distinct, 'classes': len(forms), 'labeled': labeled,
                       'forms': sorted(forms), 'auts_match': auts_match}
    lines.append('- lower-bound step %.1f s' % (time.time() - t0))
    append('\n'.join(lines))
    res['seconds'] = round(time.time() - t0, 2)
    state['results']['lower'] = res
    return all(res[k]['ok'] for k in ('7', '8'))


def check_complements(ctx, reps, want_bad):
    """reps: list of (mask, aut).  Returns per-class results for the complements."""
    out = []
    for f, a in reps:
        comp = ctx.full ^ f
        w = find_pair(ctx, ctx.adj(comp))
        out.append((f, a, comp, w, w is not None and witness_ok(ctx, comp, w)))
    return out


def step_upper7(args, state):
    n, k = 7, 21 - 17
    ctx = Ctx(n)
    fact = math.factorial(n)
    lines = ['', '## 3. Upper bound n = 7: every 17-edge graph is bad', '']
    t0 = time.time()
    classes = {}
    for comb in itertools.combinations(range(ctx.N), k):
        m = 0
        for e in comb:
            m |= 1 << e
        f, a = canon(ctx, m)
        ent = classes.get(f)
        if ent is None:
            classes[f] = [a, 1]
        else:
            if ent[0] != a:
                raise AssertionError('|Aut| disagrees')
            ent[1] += 1
    t_iso = time.time() - t0
    total = sum(c for _, c in classes.values())
    orbit_ok = all(a * c == fact for a, c in classes.values())
    lines.append('- enumerated all C(21,4) = %d labeled 4-edge sets (%d seen); canonical forms give %d isomorphism classes (OEIS A008406: %d); '
                 'every class has exactly 7!/|Aut| labeled members: %s; %.2f s'
                 % (math.comb(21, 4), total, len(classes), A008406[(7, 4)], 'yes' if orbit_ok else 'NO', t_iso))
    t1 = time.time()
    res = check_complements(ctx, sorted((f, v[0]) for f, v in classes.items()), True)
    t_chk = time.time() - t1
    nbad = sum(1 for r in res if r[4])
    for f, a, comp, w, ok in res:
        lines.append('  - complement of %s (|Aut| %d, %d labeled): %s, pair on %d vertices: %s'
                     % (ctx.edges(f), a, fact // a, 'bad, witness verified' if ok else 'NOT SHOWN BAD',
                        popcount(w[0]) if w else 0, fmt_witness(ctx, w)))
    lines.append('- class check: %d/%d complements bad with verified witnesses; %.2f s' % (nbad, len(res), t_chk))
    t2 = time.time()
    lab_bad = lab_tot = 0
    for comb in itertools.combinations(range(ctx.N), k):
        m = 0
        for e in comb:
            m |= 1 << e
        comp = ctx.full ^ m
        w = find_pair(ctx, ctx.adj(comp))
        lab_tot += 1
        if w is not None and witness_ok(ctx, comp, w):
            lab_bad += 1
    t_lab = time.time() - t2
    lines.append('- labeled cross-check with no isomorphism reduction: %d/%d labeled 17-edge graphs bad with verified witnesses; %.2f s'
                 % (lab_bad, lab_tot, t_lab))
    ok = (nbad == len(res) and orbit_ok and total == math.comb(21, 4) and lab_bad == lab_tot == math.comb(21, 4))
    lines.append('- upper bound n = 7 (f(7) <= 16): **%s**; step %.1f s' % ('confirmed' if ok else 'NOT confirmed', time.time() - t0))
    append('\n'.join(lines))
    state['results']['upper7'] = {'ok': ok, 'classes': len(classes), 'labeled_bad': lab_bad,
                                  'seconds': round(time.time() - t0, 2)}
    return ok


def step_upper8(args, state):
    n, k = 8, 28 - 20
    ctx = Ctx(n)
    fact = math.factorial(n)
    t0 = time.time()
    if 'upper8_header' not in state['results']:
        append('\n## 4. Upper bound n = 8: every 20-edge graph is bad\n')
        state['results']['upper8_header'] = True
        save_state(args.state, state)
    done = gen_levels(ctx, k, state, args.state, t0 + args.budget, append)
    if not done:
        append('- progress: level generation paused at the time budget; rerun `upper8` to resume from the checkpoint')
        return None
    reps = [tuple(x) for x in state['levels'][str(n)][str(k)]]
    labeled = sum(fact // a for _, a in reps)
    t1 = time.time()
    res = check_complements(ctx, reps, True)
    t_chk = time.time() - t1
    nbad = sum(1 for r in res if r[4])
    sizes = {}
    for r in res:
        if r[3]:
            s = popcount(r[3][0])
            sizes[s] = sizes.get(s, 0) + 1
    rng = random.Random(8585)
    t2 = time.time()
    samp_bad = 0
    SAMPLES = 3000
    for _ in range(SAMPLES):
        m = 0
        for e in rng.sample(range(ctx.N), 20):
            m |= 1 << e
        w = find_pair(ctx, ctx.adj(m))
        if w is not None and witness_ok(ctx, m, w):
            samp_bad += 1
    t_s = time.time() - t2
    lines = []
    lines.append('- 8-edge graphs on 8 vertices up to isomorphism: %d classes (OEIS A008406: %d); sum 8!/|Aut| = %d vs C(28,8) = %d: %s'
                 % (len(reps), A008406[(8, 8)], labeled, math.comb(28, 8), 'match' if labeled == math.comb(28, 8) else 'MISMATCH'))
    lines.append('- class check: %d/%d complements (20 edges) bad with verified witnesses; witness vertex-set sizes %s; %.2f s'
                 % (nbad, len(res), ', '.join('%d: %d' % (s, sizes[s]) for s in sorted(sizes)), t_chk))
    lines.append('- random labeled sample: %d/%d random 20-edge labeled graphs bad with verified witnesses; %.2f s' % (samp_bad, SAMPLES, t_s))
    ok = nbad == len(res) == A008406[(8, 8)] and labeled == math.comb(28, 8) and samp_bad == SAMPLES
    lines.append('- upper bound n = 8 (f(8) <= 19): **%s**; this run %.1f s (level generation times in the progress lines above)'
                 % ('confirmed' if ok else 'NOT confirmed', time.time() - t0))
    append('\n'.join(lines))
    state['results']['upper8'] = {'ok': ok, 'classes': len(reps), 'labeled': labeled,
                                  'check_seconds': round(t_chk, 2), 'seconds': round(time.time() - t0, 2)}
    return ok


def step_extremal7(args, state):
    n, k = 7, 21 - 16
    ctx = Ctx(n)
    fact = math.factorial(n)
    t0 = time.time()
    classes = {}
    for comb in itertools.combinations(range(ctx.N), k):
        m = 0
        for e in comb:
            m |= 1 << e
        f, a = canon(ctx, m)
        ent = classes.get(f)
        if ent is None:
            classes[f] = [a, 1]
        else:
            ent[1] += 1
    orbit_ok = all(a * c == fact for a, c in classes.values())
    res = check_complements(ctx, sorted((f, v[0]) for f, v in classes.items()), False)
    goods = [r for r in res if r[3] is None]
    bads_ok = all(r[4] for r in res if r[3] is not None)
    good_forms = sorted(canon(ctx, r[2])[0] for r in goods)
    good_lab = sum(fact // r[1] for r in goods)
    reported = state['results'].get('lower', {}).get('7', {}).get('forms')
    same = reported is not None and sorted(reported) == good_forms
    t_cls = time.time() - t0
    t2 = time.time()
    lab_good = 0
    lab_bad_ok = True
    for comb in itertools.combinations(range(ctx.N), k):
        m = 0
        for e in comb:
            m |= 1 << e
        comp = ctx.full ^ m
        w = find_pair(ctx, ctx.adj(comp))
        if w is None:
            lab_good += 1
        elif not witness_ok(ctx, comp, w):
            lab_bad_ok = False
    t_lab = time.time() - t2
    lines = ['', '## 5. Extremal graphs n = 7 (16 edges)', '']
    lines.append('- 5-edge graphs on 7 vertices: %d classes from all %d labeled sets (OEIS A008406: %d), orbit sizes 7!/|Aut|: %s'
                 % (len(classes), math.comb(21, 5), A008406[(7, 5)], 'yes' if orbit_ok else 'NO'))
    lines.append('- good 16-edge classes: %d, %d labeled (sum 7!/|Aut|); all other complements bad with verified witnesses: %s; '
                 'same class set as 585-small-n.md: %s; %.2f s'
                 % (len(goods), good_lab, 'yes' if bads_ok else 'NO', 'yes' if same else 'NO', t_cls))
    for r in goods:
        lines.append('  - good: complement of %s, |Aut| = %d' % (ctx.edges(r[0]), r[1]))
    lines.append('- labeled cross-check: %d of %d labeled 16-edge graphs are good (reported 252); every bad one has a verified witness: %s; %.2f s'
                 % (lab_good, math.comb(21, 5), 'yes' if lab_bad_ok else 'NO', t_lab))
    append('\n'.join(lines))
    state['results']['extremal7'] = {'good_classes': len(goods), 'good_labeled': good_lab, 'labeled_good': lab_good,
                                     'same_as_reported': same, 'seconds': round(time.time() - t0, 2)}
    return True


def step_extremal8(args, state):
    n, k = 8, 28 - 19
    ctx = Ctx(n)
    fact = math.factorial(n)
    t0 = time.time()
    if 'extremal8_header' not in state['results']:
        append('\n## 6. Extremal graphs n = 8 (19 edges)\n')
        state['results']['extremal8_header'] = True
        save_state(args.state, state)
    done = gen_levels(ctx, k, state, args.state, t0 + args.budget, append)
    if not done:
        append('- progress: level generation paused at the time budget; rerun `extremal8` to resume from the checkpoint')
        return None
    reps = [tuple(x) for x in state['levels'][str(n)][str(k)]]
    labeled = sum(fact // a for _, a in reps)
    t1 = time.time()
    res = check_complements(ctx, reps, False)
    goods = [r for r in res if r[3] is None]
    bads_ok = all(r[4] for r in res if r[3] is not None)
    naive_good = sum(1 for r in goods if naive_pair_grouped(naive_cycles(ctx, ctx.adj(r[2]))) is None)
    good_forms = sorted(canon(ctx, r[2])[0] for r in goods)
    good_lab = sum(fact // r[1] for r in goods)
    reported = state['results'].get('lower', {}).get('8', {}).get('forms')
    same = reported is not None and sorted(reported) == good_forms
    t_chk = time.time() - t1
    lines = []
    lines.append('- 9-edge graphs on 8 vertices: %d classes (OEIS A008406: %d); sum 8!/|Aut| = %d vs C(28,9) = %d: %s'
                 % (len(reps), A008406[(8, 9)], labeled, math.comb(28, 9), 'match' if labeled == math.comb(28, 9) else 'MISMATCH'))
    lines.append('- good 19-edge classes: %d (brute force agrees on %d), %d labeled (sum 8!/|Aut|); all other complements bad with verified witnesses: %s; '
                 'same class set as the 12 lists in 585-small-n.md: %s; %.2f s'
                 % (len(goods), naive_good, good_lab, 'yes' if bads_ok else 'NO', 'yes' if same else 'NO', t_chk))
    for r in goods:
        lines.append('  - good: complement of %s, |Aut| = %d' % (ctx.edges(r[0]), r[1]))
    append('\n'.join(lines))
    state['results']['extremal8'] = {'good_classes': len(goods), 'naive_good': naive_good, 'good_labeled': good_lab,
                                     'same_as_reported': same, 'seconds': round(time.time() - t0, 2)}
    return True


def _labeled8_task(prefix):
    """All 8-edge sets whose smallest edge indices are `prefix`; checks each complement."""
    ctx = Ctx(8)
    base = 0
    for e in prefix:
        base |= 1 << e
    cnt = bad = 0
    example = None
    for rest in itertools.combinations(range(prefix[-1] + 1, ctx.N), 8 - len(prefix)):
        m = base
        for e in rest:
            m |= 1 << e
        comp = ctx.full ^ m
        w = find_pair(ctx, ctx.adj(comp))
        cnt += 1
        if w is not None and witness_ok(ctx, comp, w):
            bad += 1
        elif example is None:
            example = comp
    return tuple(prefix), cnt, bad, example


def step_labeled8(args, state):
    """Isomorphism-free cross-check: every labeled 20-edge graph on 8 vertices,
    split into tasks by the two smallest missing-edge indices, run on a process
    pool; finished tasks are checkpointed so a rerun resumes."""
    import multiprocessing as mp
    t0 = time.time()
    res = state['results']
    done = res.setdefault('labeled8', {})
    if 'labeled8_header' not in res:
        append('\n## 7. Labeled cross-check n = 8: all C(28,8) = 3,108,105 labeled 20-edge graphs, no isomorphism reduction\n')
        res['labeled8_header'] = True
        save_state(args.state, state)
    # First chunk ran with 2-edge prefixes (231 tasks, up to 230,230 graphs each; too coarse on a
    # loaded machine), later chunks with 4-edge prefixes (up to 10,626 graphs each); a 4-prefix
    # is skipped when its 2-prefix already finished.  Both kinds are keyed in `done`.
    tasks = [q for q in itertools.combinations(range(24), 4)
             if ','.join(map(str, q)) not in done and '%d,%d' % q[:2] not in done]
    tasks.sort(key=lambda t: -math.comb(27 - t[3], 4))
    workers = max(1, min(16, (os.cpu_count() or 2) - 2))
    paused = False
    if tasks:
        last = time.time()
        pool = mp.Pool(workers)
        try:
            for q, cnt, bad, ex in pool.imap_unordered(_labeled8_task, tasks):
                done[','.join(map(str, q))] = [cnt, bad, ex]
                if time.time() - last > 5:
                    save_state(args.state, state)
                    last = time.time()
                if time.time() - t0 > args.budget:
                    paused = True
                    break
        finally:
            pool.terminate()
            pool.join()
        save_state(args.state, state)
    total = sum(v[0] for v in done.values())
    bad = sum(v[1] for v in done.values())
    examples = [v[2] for v in done.values() if v[2] is not None]
    target = math.comb(28, 8)
    if paused:
        append('- progress: %d prefix tasks done, %d of %d labeled graphs checked (%d remaining), %d bad with verified witnesses; '
               'this chunk %.1f s on %d processes; rerun `labeled8` to resume'
               % (len(done), total, target, target - total, bad, time.time() - t0, workers))
        return None
    ok = total == target and bad == total and not examples
    append('- %d prefix tasks, %d labeled 20-edge graphs checked (C(28,8) = %d); bad with verified witnesses: %d; '
           'graphs not shown bad: %d; last chunk %.1f s on %d processes'
           % (len(done), total, target, bad, total - bad, time.time() - t0, workers))
    append('- labeled cross-check n = 8 (f(8) <= 19 without the canonical form): **%s**' % ('confirmed' if ok else 'NOT confirmed'))
    res['labeled8_ok'] = ok
    return ok


def step_status(args, state):
    r = state['results']
    lo = r.get('lower', {})
    lines = ['', '## Status', '']
    lines.append('| n | claim | lower bound: reported good graph(s) re-checked | upper bound: all (claim+1)-edge graphs bad | classes checked | status |')
    lines.append('|---|---|---|---|---|---|')
    u7 = r.get('upper7', {})
    u8 = r.get('upper8', {})
    for n, u, cls in ((7, u7, '10 classes of 4-edge complements, plus all 5,985 labeled'),
                      (8, u8, '221 classes of 8-edge complements, plus %s' % (
                          'all 3,108,105 labeled' if r.get('labeled8_ok') else '3,000 random labeled'))):
        low = lo.get(str(n), {}).get('ok')
        up = u.get('ok')
        lines.append('| %d | f(%d) = %d | %s | %s | %s | **%s** |'
                     % (n, n, CLAIM[n], 'yes' if low else 'no', 'yes' if up else 'no', cls,
                        ('f(%d) = %d confirmed' % (n, CLAIM[n])) if (low and up) else ('f(%d) not confirmed' % n)))
    e7 = r.get('extremal7', {})
    e8 = r.get('extremal8', {})
    lines.append('')
    lines.append('- extremal class counts: n = 7: %s good 16-edge class(es), %s labeled (reported 1 and 252); n = 8: %s good 19-edge classes, %s labeled (reported 12 and 175560)'
                 % (e7.get('good_classes'), e7.get('good_labeled'), e8.get('good_classes'), e8.get('good_labeled')))
    lines.append('- self-tests: %s' % ('PASS' if r.get('selftest', {}).get('ok') else 'FAIL or not run'))
    diffs = []
    if not (lo.get('7', {}).get('auts_match') and lo.get('8', {}).get('auts_match')):
        diffs.append('reported |Aut| values')
    if (e7.get('good_classes'), e7.get('good_labeled'), e7.get('labeled_good')) != (1, 252, 252) or not e7.get('same_as_reported'):
        diffs.append('n = 7 extremal classes')
    if (e8.get('good_classes'), e8.get('good_labeled')) != (12, 175560) or not e8.get('same_as_reported'):
        diffs.append('n = 8 extremal classes')
    lines.append('- discrepancies with 585-small-n.md: %s' % (', '.join(diffs) if diffs else
                 'none; f(7) = 16, f(8) = 19, the extremal class counts (1 and 12), labeled counts (252 and 175560) and every reported |Aut| reproduce'))
    lines.append('- step times (s): self-test %s, lower %s, upper7 %s, upper8 %s (class check %s), extremal7 %s, extremal8 %s; '
                 ''
                 % (r.get('selftest', {}).get('seconds'), lo.get('seconds'), u7.get('seconds'), u8.get('seconds'),
                    u8.get('check_seconds'), e7.get('seconds'), e8.get('seconds')))
    append('\n'.join(lines))
    return True


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('step', choices=['selftest', 'lower', 'upper7', 'upper8', 'extremal7', 'extremal8', 'labeled8', 'status'])
    ap.add_argument('--state', default=os.path.join(tempfile.gettempdir(), 'erdos585_verify_state.json'))
    ap.add_argument('--budget', type=float, default=180.0, help='seconds before a resumable step checkpoints and stops')
    args = ap.parse_args()
    state = load_state(args.state)
    fn = {'selftest': step_selftest, 'lower': step_lower, 'upper7': step_upper7, 'upper8': step_upper8,
          'extremal7': step_extremal7, 'extremal8': step_extremal8, 'labeled8': step_labeled8,
          'status': step_status}[args.step]
    t = time.time()
    ok = fn(args, state)
    save_state(args.state, state)
    print('%s: %s (%.1f s)' % (args.step, {True: 'ok', False: 'FAILED', None: 'paused, rerun to resume'}[ok], time.time() - t))
    sys.exit(0 if ok else (3 if ok is None else 1))


if __name__ == '__main__':
    main()
