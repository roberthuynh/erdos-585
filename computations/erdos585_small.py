#!/usr/bin/env python3
"""Erdos problem 585, small n (standard library only).

f(n) = max edges of a simple graph on n labeled vertices containing no two
edge-disjoint cycles (simple, >= 3 vertices) with the same vertex set.

Search: branch and bound over the edges in lexicographic order, adding an edge
only if the graph stays good ("good" is closed under edge deletion).
Safe symmetry breaking: vertex 0 has maximum degree d, N(0) = {1..d}, degrees
are non-increasing on 1..d and on d+1..n-1 (every graph has such a labeling).
Bound: current + min(undecided edges, sum_v min(cap_v - deg_v, undecided at v)/2).

Incremental test: after adding e = uv to a good G, a bad pair must be
(C1 through e, C2 in G) with V(C1) = V(C2); C1 = e + a u-v path P in G. For
each such P with vertex set S (|S| >= 5, G[S] with >= 2|S|-1 edges) look for a
Hamiltonian cycle of G[S] edge-disjoint from P.

Independent checks: every extremal class is re-tested from scratch (all cycles,
grouped by vertex set, all pairs); for n <= brute_max a brute-force pass over
all 2^C(n,2) labeled graphs with that from-scratch test.
"""
import argparse, math, random, sys, time


def bc(x):
    return x.bit_count()


def edge_index(n):
    E = [[-1] * n for _ in range(n)]
    edges = []
    for a in range(n):
        for b in range(a + 1, n):
            E[a][b] = E[b][a] = len(edges)
            edges.append((a, b))
    return edges, E


def mask_edges(mask, edges):
    return [edges[i] for i in range(len(edges)) if mask >> i & 1]


def adj_from_mask(n, mask, edges):
    adj = [0] * n
    for i, (a, b) in enumerate(edges):
        if mask >> i & 1:
            adj[a] |= 1 << b
            adj[b] |= 1 << a
    return adj


# ---------------- from-scratch test ----------------
def all_cycles(n, adj, E):
    """Every simple cycle once, as (vertex_mask, edge_mask)."""
    out = []
    full = (1 << n) - 1
    for s in range(n):
        allowed = full & ~((1 << (s + 1)) - 1)   # vertices > s

        def dfs(w, vis, em, second):
            if w != s and second < w and bc(vis) >= 3 and adj[w] >> s & 1:
                out.append((vis, em | (1 << E[w][s])))
            nb = adj[w] & allowed & ~vis
            while nb:
                b = nb & -nb
                nb ^= b
                x = b.bit_length() - 1
                dfs(x, vis | b, em | (1 << E[w][x]), x if second < 0 else second)
        dfs(s, 1 << s, 0, -1)
    return out


def bad_pair_full(n, adj, E):
    groups = {}
    for vm, em in all_cycles(n, adj, E):
        groups.setdefault(vm, []).append(em)
    for vm, lst in groups.items():
        for i in range(len(lst)):
            for j in range(i + 1, len(lst)):
                if lst[i] & lst[j] == 0:
                    return (vm, lst[i], lst[j])
    return None


def is_good_full(n, adj, E):
    return bad_pair_full(n, adj, E) is None


# ---------------- canonical form (individualisation-refinement) ----------------
def canon(n, adj, E):
    """(canonical edge mask, |Aut|). No automorphism pruning, so the number of
    leaves reaching the minimum equals |Aut(G)|."""
    nb = [[w for w in range(n) if adj[v] >> w & 1] for v in range(n)]

    def refine(col):
        k = len(set(col))
        while True:
            sig = [(col[v], tuple(sorted(col[w] for w in nb[v]))) for v in range(n)]
            order = sorted(set(sig))
            idx = {s: i for i, s in enumerate(order)}
            new = [idx[s] for s in sig]
            if len(order) == k:
                return new
            k, col = len(order), new

    best = [None, 0]

    def rec(col):
        if len(set(col)) == n:
            mk = 0
            for a in range(n):
                for b in nb[a]:
                    if b > a:
                        mk |= 1 << E[col[a]][col[b]]
            if best[0] is None or mk < best[0]:
                best[0], best[1] = mk, 1
            elif mk == best[0]:
                best[1] += 1
            return
        cnt = {}
        for c in col:
            cnt[c] = cnt.get(c, 0) + 1
        tc = min(c for c in cnt if cnt[c] > 1)
        for v in range(n):
            if col[v] == tc:
                new = [2 * c + (1 if (c == tc and w != v) else 0) for w, c in enumerate(col)]
                order = sorted(set(new))
                idx = {x: i for i, x in enumerate(order)}
                rec(refine([idx[x] for x in new]))
    rec(refine([0] * n))
    return best[0], best[1]


# ---------------- incremental search ----------------
class Searcher:
    def __init__(self, n):
        self.n = n
        self.edges, self.E = edge_index(n)
        self.m = len(self.edges)
        rem = [[0] * n for _ in range(self.m + 1)]
        for i in range(self.m - 1, -1, -1):
            a, b = self.edges[i]
            rem[i] = rem[i + 1][:]
            rem[i][a] += 1
            rem[i][b] += 1
        self.rem = rem
        self.nodes = 0
        self.checks = 0

    def ham_cycles(self, adj, S):
        E = self.E
        s0 = (S & -S).bit_length() - 1
        out = []

        def dfs(w, vis, em):
            if vis == S:
                if adj[w] >> s0 & 1:
                    out.append(em | (1 << E[w][s0]))
                return
            nb = adj[w] & S & ~vis
            while nb:
                b = nb & -nb
                nb ^= b
                x = b.bit_length() - 1
                dfs(x, vis | b, em | (1 << E[w][x]))
        dfs(s0, 1 << s0, 0)
        return out

    def can_add(self, adj, u, v):
        """adj: good graph without uv. True iff adj + uv is good."""
        self.checks += 1
        E = self.E
        groups = {}

        def dfs(w, vis, em):
            nb = adj[w] & ~vis
            while nb:
                b = nb & -nb
                nb ^= b
                x = b.bit_length() - 1
                if x == v:
                    if bc(vis) >= 4:          # |S| >= 5
                        groups.setdefault(vis | b, []).append(em | (1 << E[w][x]))
                else:
                    dfs(x, vis | b, em | (1 << E[w][x]))
        dfs(u, 1 << u, 0)
        for S, pms in groups.items():
            k = bc(S)
            tot = 0
            s = S
            while s:
                b = s & -s
                s ^= b
                tot += bc(adj[b.bit_length() - 1] & S)
            if tot // 2 + 1 < 2 * k:          # G'[S] needs 2k edges
                continue
            hcs = self.ham_cycles(adj, S)
            for pm in pms:
                for hc in hcs:
                    if pm & hc == 0:
                        return False
        return True

    def search(self, d, best, prune_equal, found):
        n, m, edges, rem = self.n, self.m, self.edges, self.rem
        adj = [0] * n
        deg = [0] * n
        mask = 0
        for j in range(1, d + 1):
            adj[0] |= 1 << j
            adj[j] |= 1
            deg[0] += 1
            deg[j] += 1
            mask |= 1 << (j - 1)          # edge (0, j) has index j - 1
        st = {'best': best}
        cls = [0] + [1] * d + [2] * (n - 1 - d)

        def caps(a):
            # vertices < a are complete; cap later vertices by the last complete
            # vertex of the same class (degrees non-increasing within a class)
            cap = [d] * n
            lastA = min(a - 1, d)                 # last complete vertex in 1..d
            capA = deg[lastA] if lastA >= 1 else d
            lastB = a - 1                         # last complete vertex in d+1..n-1
            capB = deg[lastB] if lastB >= d + 1 else d
            for x in range(1, n):
                if x >= a:
                    cap[x] = capA if cls[x] == 1 else capB
            return cap

        t_start = time.perf_counter()

        def rec(i, c, mask):
            self.nodes += 1
            if self.nodes % 500000 == 0:
                print(f"    progress d={d}: nodes={self.nodes} best={st['best']} "
                      f"{time.perf_counter()-t_start:.0f}s", flush=True)
            if i == m:
                # exact symmetry-breaking check on final degrees
                for x in range(2, n):
                    if cls[x] == cls[x - 1] and deg[x] > deg[x - 1]:
                        return
                if c > st['best']:
                    st['best'] = c
                    found.clear()
                    found.append(mask)
                elif c == st['best']:
                    found.append(mask)
                return
            a, b = edges[i]
            cap = caps(a)
            r = rem[i]
            room = 0
            for v in range(n):
                t = cap[v] - deg[v]
                if t < 0:
                    return
                rv = r[v]
                room += t if t < rv else rv
            ub = c + min(m - i, room // 2)
            bb = st['best']
            if ub < bb or (prune_equal and ub == bb):
                return
            if deg[a] < cap[a] and deg[b] < cap[b] and self.can_add(adj, a, b):
                adj[a] |= 1 << b
                adj[b] |= 1 << a
                deg[a] += 1
                deg[b] += 1
                rec(i + 1, c + 1, mask | (1 << i))
                adj[a] &= ~(1 << b)
                adj[b] &= ~(1 << a)
                deg[a] -= 1
                deg[b] -= 1
            rec(i + 1, c, mask)
        rec(n - 1 if n >= 1 else 0, d, mask)
        return st['best']


def solve(n, seed, prune_equal, log):
    """Returns (f, list of masks found, nodes, checks)."""
    S = Searcher(n)
    best = seed - 1 if prune_equal else seed
    allf = []
    dlist = [0] if n <= 1 else range(n - 1, 0, -1)
    for d in dlist:
        if n >= 2 and n * d // 2 < best + (1 if prune_equal else 0):
            log(f"  n={n} d={d}: skipped (n*d/2 below target)")
            continue
        t0 = time.perf_counter()
        found = []
        nb = S.search(d, best, prune_equal, found)
        if found:
            if nb > best or not allf or bc(allf[0]) < nb:
                allf = list(found)
            else:
                allf.extend(found)
        best = max(best, nb)
        log(f"  n={n} d={d}: best={best} found_here={len(found)} nodes={S.nodes} "
            f"checks={S.checks} {time.perf_counter()-t0:.1f}s")
    allf = [x for x in allf if bc(x) == best]
    return best, allf, S.nodes, S.checks, S


def brute(n):
    edges, E = edge_index(n)
    m = len(edges)
    best, count = -1, 0
    ex = None
    for mask in range(1 << m):
        c = bc(mask)
        if c < best:
            continue
        adj = adj_from_mask(n, mask, edges)
        if is_good_full(n, adj, E):
            if c > best:
                best, count, ex = c, 1, mask
            else:
                count += 1
    return best, count, ex


def brute_top(n, F):
    """From-scratch test on every labeled graph with exactly F+1 edges (all must be
    bad; good is closed under deletion, so this bounds f(n) <= F) and every graph
    with exactly F edges (count the good ones)."""
    from itertools import combinations
    edges, E = edge_index(n)
    m = len(edges)
    good_top = 0
    for comb in combinations(range(m), F + 1):
        mask = 0
        for i in comb:
            mask |= 1 << i
        if is_good_full(n, adj_from_mask(n, mask, edges), E):
            good_top += 1
    good_f = 0
    for comb in combinations(range(m), F):
        mask = 0
        for i in comb:
            mask |= 1 << i
        if is_good_full(n, adj_from_mask(n, mask, edges), E):
            good_f += 1
    return good_top, good_f


def levelwise(n, log):
    """Second method, no symmetry breaking, no bound, no incremental test:
    generate good graphs up to isomorphism one edge at a time (good is closed
    under deletion, so every good graph with k+1 edges extends a good one with k),
    testing each new class from scratch. Returns (max edges, {canon: |Aut|} at max,
    classes per level)."""
    edges, E = edge_index(n)
    m = len(edges)
    level = {0: canon(n, [0] * n, E)[1]}
    sizes = [1]
    while True:
        nxt, rejected = {}, set()
        for g in level:
            for i in range(m):
                if g >> i & 1:
                    continue
                h = g | (1 << i)
                adjh = adj_from_mask(n, h, edges)
                cf, aut = canon(n, adjh, E)
                if cf in nxt or cf in rejected:
                    continue
                if is_good_full(n, adjh, E):
                    nxt[cf] = aut
                else:
                    rejected.add(cf)
        if not nxt:
            return len(sizes) - 1, level, sizes
        level = nxt
        sizes.append(len(level))
        log(f"    levelwise n={n}: {len(sizes)-1} edges -> {len(level)} good classes")


def selftest(n, trials, rng):
    """Compare the incremental test with the from-scratch test on random good graphs."""
    S = Searcher(n)
    edges, E = S.edges, S.E
    agree = 0
    for _ in range(trials):
        order = list(range(len(edges)))
        rng.shuffle(order)
        adj = [0] * n
        stop = rng.randint(0, len(edges))
        for k, i in enumerate(order):
            a, b = edges[i]
            if k >= stop:
                ok_inc = S.can_add(adj, a, b)
                adj[a] |= 1 << b; adj[b] |= 1 << a
                ok_full = is_good_full(n, adj, E)
                adj[a] &= ~(1 << b); adj[b] &= ~(1 << a)
                if ok_inc != ok_full:
                    raise SystemExit(f"SELFTEST MISMATCH n={n} adj={adj} edge={(a, b)}")
                agree += 1
                break
            adj[a] |= 1 << b; adj[b] |= 1 << a
            if not is_good_full(n, adj, E):
                adj[a] &= ~(1 << b); adj[b] &= ~(1 << a)
    return agree


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--nmin', type=int, default=1)
    ap.add_argument('--nmax', type=int, default=7)
    ap.add_argument('--brute-max', type=int, default=6)
    ap.add_argument('--md', default='computations/585-small-n.out.md')
    ap.add_argument('--fresh', action='store_true')
    ap.add_argument('--fprev', type=int, default=None, help='f(nmin-1) when nmin > 1')
    ap.add_argument('--value-only', action='store_true', help='find f(n) with <= pruning, no enumeration')
    ap.add_argument('--selftest', type=int, default=0)
    ap.add_argument('--levelwise', type=int, default=0, help='also run the up-to-isomorphism level-wise check for n <= this')
    ap.add_argument('--seed', type=int, default=None, help='known lower bound on f(n) (overrides f(n-1)+2)')
    ap.add_argument('--brute-top', type=int, default=0, help='for n <= this, from-scratch test of every graph with f and f+1 edges')
    args = ap.parse_args()

    def log(s):
        print(s, flush=True)

    def md(s):
        with open(args.md, 'a') as fh:
            fh.write(s + '\n')

    if args.fresh:
        with open(args.md, 'w') as fh:
            fh.write('# Erdos 585, small n: exact f(n)\n\n'
                     'f(n) = max edges of a simple graph on n labeled vertices with no two '
                     'edge-disjoint cycles (>= 3 vertices) on the same vertex set.\n'
                     'Produced by `computations/erdos585_small.py` (Python 3, stdlib only); each '
                     'section is appended as soon as that n finishes.\n\n')
    rng = random.Random(585)
    if args.selftest:
        for n in (5, 6, 7):
            t0 = time.perf_counter()
            k = selftest(n, args.selftest, rng)
            log(f"selftest n={n}: {k} incremental-vs-scratch comparisons agree ({time.perf_counter()-t0:.1f}s)")
            md(f"- self-test n={n}: {k} random (good graph, new edge) cases, incremental test "
               f"agrees with the from-scratch test ({time.perf_counter()-t0:.1f}s)")
    fprev = args.fprev
    for n in range(args.nmin, args.nmax + 1):
        if n == 1:
            seed = 0
        elif n == 2:
            seed = 1
        else:
            seed = fprev + 2   # extremal graph on n-1 vertices plus a vertex of degree 2
        if args.seed is not None:
            seed = args.seed
        t0 = time.perf_counter()
        f, masks, nodes, checks, S = solve(n, seed, args.value_only, log)
        dt = time.perf_counter() - t0
        edges, E = S.edges, S.E
        if not masks:
            raise SystemExit(f"n={n}: no graph with >= seed {seed} edges found; bug")
        classes = {}
        for mk in masks:
            adj = adj_from_mask(n, mk, edges)
            cf, aut = canon(n, adj, E)
            classes[cf] = aut
        for cf in classes:
            if not is_good_full(n, adj_from_mask(n, cf, edges), E):
                raise SystemExit(f"n={n}: extremal class fails the from-scratch test; bug")
        labeled = sum(math.factorial(n) // a for a in classes.values())
        reps = sorted(classes)
        rep = reps[0]
        degs = [bc(x) for x in adj_from_mask(n, rep, edges)]
        m = n * (n - 1) // 2
        mode = 'value only (<= pruning; classes listed are only those met)' if args.value_only else 'all extremal graphs enumerated'
        log(f"n={n}: f={f} C(n,2)={m} classes={len(classes)} labeled={labeled} "
            f"({mode}) nodes={nodes} checks={checks} {dt:.1f}s")
        md(f"## n = {n}\n")
        md(f"- f({n}) = **{f}** (C({n},2) = {m}, gap {m - f}); search: {mode}; "
           f"{dt:.2f} s, {nodes} nodes, {checks} incremental tests")
        md(f"- extremal graph (edge list): {mask_edges(rep, edges)}; degrees {degs}")
        if not args.value_only:
            md(f"- extremal graphs: {len(classes)} isomorphism classes (deduplicated by canonical form), "
               f"{labeled} labeled graphs (sum of n!/|Aut|); {len(masks)} labeled representatives met under symmetry breaking")
            if len(classes) <= 12:
                for cf in reps:
                    md(f"  - |Aut| = {classes[cf]}: {mask_edges(cf, edges)}")
        if n <= args.brute_max:
            t1 = time.perf_counter()
            bf, bcnt, bex = brute(n)
            dtb = time.perf_counter() - t1
            ok = (bf == f) and (args.value_only or bcnt == labeled)
            log(f"  brute n={n}: f={bf} labeled extremal={bcnt} {dtb:.1f}s match={ok}")
            md(f"- brute force over all 2^{m} labeled graphs (from-scratch test): f = {bf}, "
               f"{bcnt} labeled extremal graphs, {dtb:.2f} s; "
               f"{'MATCHES' if ok else 'MISMATCH'} the backtracking")
        if args.brute_max < n <= args.brute_top:
            t1 = time.perf_counter()
            gt, gf = brute_top(n, f)
            dtb = time.perf_counter() - t1
            ok = gt == 0 and (args.value_only or gf == labeled)
            log(f"  brute-top n={n}: good graphs with {f+1} edges={gt}, with {f} edges={gf} {dtb:.1f}s match={ok}")
            md(f"- top-level brute force (from-scratch test on all C({m},{f+1}) + C({m},{f}) labeled graphs): "
               f"{gt} good graphs with {f+1} edges, {gf} good graphs with {f} edges, {dtb:.2f} s; "
               f"{'MATCHES' if ok else 'MISMATCH'} the backtracking")
        if n <= args.levelwise:
            t1 = time.perf_counter()
            lf, lclasses, sizes = levelwise(n, log)
            dtl = time.perf_counter() - t1
            llab = sum(math.factorial(n) // a for a in lclasses.values())
            ok = lf == f and (args.value_only or (set(lclasses) == set(classes) and llab == labeled))
            log(f"  levelwise n={n}: f={lf} classes={len(lclasses)} labeled={llab} {dtl:.1f}s match={ok}")
            md(f"- level-wise check (good graphs up to isomorphism, one edge at a time, from-scratch test, "
               f"no symmetry breaking or bound): f = {lf}, {len(lclasses)} extremal classes, {llab} labeled, "
               f"{dtl:.2f} s; good classes per edge count {sizes}; {'MATCHES' if ok else 'MISMATCH'} the backtracking")
        md("")
        fprev = f


if __name__ == '__main__':
    main()
