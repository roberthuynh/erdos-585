"""Exact pair finder by block decomposition (written from scratch for this review).

A pair (C1, C2) on S is the same thing as a colouring c: E -> {0, R, B} such that
  (V) every vertex has (red degree, blue degree) in {(0, 0), (2, 2)}, and
  (G) the red edges form exactly one cycle and the blue edges form exactly one cycle.
(V) makes V(red) = V(blue) = S automatically; (G) makes each colour a single cycle.

Take ANY partition of V into blocks. (V) is local to blocks: restricted to the edges with an
end in block P (internal edges and boundary edges), c is a "local colouring" of P that satisfies
(V) at every vertex of P. Conversely, local colourings that agree on every boundary edge glue to
a global colouring satisfying (V). For (G), record per local colouring its signature:
  - the colours of the boundary edges,
  - for each colour X, the perfect matching of the X-coloured boundary edges given by the
    X-paths inside P, and the number of closed X-cycles lying entirely inside P.
The global X-subgraph is then a disjoint union of the internal closed X-cycles and of the cycles
of the "link structure" (nodes: X-coloured edges between blocks; one arc per matched pair in each
block). So the number of global X-cycles is (#internal closed X-cycles) + (#components of the link
structure), and (G) holds iff both counts are 1. Enumerating ALL local colourings of every block
(exhaustive backtracking) and ALL signature combinations that agree on the boundary edges is
therefore an exact and complete test for a pair. Nothing about gadgets is assumed; the
partition only affects speed.
"""
import itertools
import sys
from collections import defaultdict

from common import adjacency, verify_pair, cycle_order

_PAT = {}


def vertex_patterns(k):
    """All colour vectors on k incident edges allowed by (V): all 0, or 2 R + 2 B + rest 0."""
    if k in _PAT:
        return _PAT[k]
    pats = [tuple([0] * k)]
    for rs in itertools.combinations(range(k), 2):
        rest = [i for i in range(k) if i not in rs]
        for bs in itertools.combinations(rest, 2):
            p = [0] * k
            for i in rs:
                p[i] = 1
            for i in bs:
                p[i] = 2
            pats.append(tuple(p))
    _PAT[k] = pats
    return pats


class Block:
    def __init__(self, n, edges, adj, verts, blk_of):
        self.verts = list(verts)
        vset = set(verts)
        self.local = []  # global edge indices with at least one end in the block
        seen = set()
        for v in self.verts:
            for (w, ei) in adj[v]:
                if ei not in seen:
                    seen.add(ei)
                    self.local.append(ei)
        self.boundary = [ei for ei in self.local if not (edges[ei][0] in vset and edges[ei][1] in vset)]
        self.internal = [ei for ei in self.local if ei not in set(self.boundary)]
        self.lidx = {ei: i for i, ei in enumerate(self.local)}
        # vertex order: BFS inside the block, starting from a vertex with most boundary edges
        start = self.verts[0]
        order = []
        seenv = {start}
        queue = [start]
        while queue:
            x = queue.pop(0)
            order.append(x)
            for (w, ei) in adj[x]:
                if w in vset and w not in seenv:
                    seenv.add(w)
                    queue.append(w)
        for v in self.verts:  # disconnected block parts
            if v not in seenv:
                seenv.add(v)
                order.append(v)
                q2 = [v]
                while q2:
                    x = q2.pop(0)
                    for (w, ei) in adj[x]:
                        if w in vset and w not in seenv:
                            seenv.add(w)
                            order.append(w)
                            q2.append(w)
        self.order = order
        self.inc = {v: [self.lidx[ei] for (w, ei) in adj[v]] for v in self.verts}
        self.edges = edges
        self.vset = vset

    def enumerate_local(self):
        """Yield every local colouring (a list indexed like self.local) satisfying (V)."""
        m = len(self.local)
        col = [-1] * m
        order = self.order
        inc = self.inc

        def rec(i):
            if i == len(order):
                yield col
                return
            v = order[i]
            ie = inc[v]
            pats = vertex_patterns(len(ie))
            for p in pats:
                ok = True
                for j, li in enumerate(ie):
                    c = col[li]
                    if c != -1 and c != p[j]:
                        ok = False
                        break
                if not ok:
                    continue
                newly = []
                for j, li in enumerate(ie):
                    if col[li] == -1:
                        col[li] = p[j]
                        newly.append(li)
                yield from rec(i + 1)
                for li in newly:
                    col[li] = -1

        yield from rec(0)

    def signature(self, col):
        """(bcol, rpair, rcyc, bpair, bcyc) for one local colouring."""
        edges = self.edges
        vset = self.vset
        bcol = tuple(col[self.lidx[ei]] for ei in self.boundary)
        out = [bcol]
        for X in (1, 2):
            nb = defaultdict(list)  # vertex -> list of ('v', w, ei) or ('t', ei)
            for ei in self.local:
                if col[self.lidx[ei]] != X:
                    continue
                u, w = edges[ei]
                if u in vset and w in vset:
                    nb[u].append(("v", w, ei))
                    nb[w].append(("v", u, ei))
                else:
                    x = u if u in vset else w
                    nb[x].append(("t", None, ei))
            pairs = []
            visited = set()  # terminals already paired
            reached = set()  # block vertices on a terminal-to-terminal path
            for ei in self.boundary:
                if col[self.lidx[ei]] != X or ei in visited:
                    continue
                visited.add(ei)
                u, w = edges[ei]
                cur = u if u in vset else w
                came = ei
                while True:
                    reached.add(cur)
                    nxt = [it for it in nb[cur] if it[2] != came]
                    assert len(nxt) == 1, "vertex constraint violated in walk"
                    kind, w2, e2 = nxt[0]
                    if kind == "t":
                        visited.add(e2)
                        pairs.append((min(ei, e2), max(ei, e2)))
                        break
                    came = e2
                    cur = w2
            # internal closed cycles: vertices with X-degree 2 not reached from a terminal
            rest = [v for v in nb if v not in reached]
            ncyc = 0
            seen = set()
            for v in rest:
                if v in seen:
                    continue
                ncyc += 1
                stack = [v]
                seen.add(v)
                while stack:
                    x = stack.pop()
                    for (kind, w2, e2) in nb[x]:
                        if kind == "v" and w2 not in seen:
                            seen.add(w2)
                            stack.append(w2)
            out.append(tuple(sorted(pairs)))
            out.append(min(ncyc, 2))
        return tuple(out)


def local_signatures(blk):
    """All signatures of one block, each with one witness local colouring.
    Returns (dict bcol -> dict (rpair, rc, bpair, bc) -> witness {edge: colour}, #colourings)."""
    d = defaultdict(dict)
    cnt = 0
    for col in blk.enumerate_local():
        cnt += 1
        s = blk.signature(col)
        key = s[1:]
        if key not in d[s[0]]:
            d[s[0]][key] = {ei: col[blk.lidx[ei]] for ei in blk.local}
    return dict(d), cnt


def find_pair(n, edges, blocks, verbose=False, log=None, stop_at_first=True, precomputed=None):
    """Exact pair test. blocks: list of vertex lists partitioning range(n).
    precomputed: optional list (one per block) of (sig dict, #colourings) from local_signatures.
    Returns (pair_or_None, stats). pair = (red edge indices, blue edge indices)."""
    adj = adjacency(n, edges)
    blk_of = {}
    for b, vs in enumerate(blocks):
        for v in vs:
            assert v not in blk_of
            blk_of[v] = b
    assert len(blk_of) == n
    B = [Block(n, edges, adj, vs, blk_of) for vs in blocks]
    stats = {"local_colourings": [], "signatures": [], "bcols": []}
    sigs = []  # per block: dict bcol -> dict (rpair, rc, bpair, bc) -> witness colouring (dict ei->c)
    for b, blk in enumerate(B):
        if precomputed is not None:
            d, cnt = precomputed[b]
        else:
            d, cnt = local_signatures(blk)
        # Sound filter. A signature cannot occur in a pair if, for some colour X, the block has
        # >= 2 internal closed X-cycles, or has an internal closed X-cycle and also an X-coloured
        # boundary edge: in both cases the global X-subgraph has >= 2 components (an internal
        # closed cycle touches no boundary edge, so it is a component of its own).
        filt = {}
        for bcol, keys in d.items():
            hasR = any(c == 1 for c in bcol)
            hasB = any(c == 2 for c in bcol)
            kept = {key: w for key, w in keys.items()
                    if key[1] <= 1 and key[3] <= 1
                    and not (key[1] == 1 and hasR) and not (key[3] == 1 and hasB)}
            if kept:
                filt[bcol] = kept
        stats.setdefault("signatures_before_filter", []).append(sum(len(x) for x in d.values()))
        d = filt
        sigs.append(d)
        stats["local_colourings"].append(cnt)
        stats["signatures"].append(sum(len(x) for x in d.values()))
        stats["bcols"].append(len(d))
        if verbose:
            msg = "block %d: %d vertices, %d internal + %d boundary edges, %d local colourings, %d boundary colourings, %d signatures" % (
                b, len(blk.verts), len(blk.internal), len(blk.boundary), cnt, len(d), stats["signatures"][-1])
            print(msg)
            if log:
                log.write(msg + "\n")
                log.flush()

    # global search over boundary colourings, then over signature choices
    linkcol = {}
    found = []
    leaves = [0]
    combos = [0]
    nb = len(B)
    # block order: greedy, next block = most boundary edges shared with already placed blocks
    placed = []
    remaining = set(range(nb))
    while remaining:
        best = max(remaining, key=lambda b: (sum(1 for ei in B[b].boundary
                                                  if any(blk_of[x] in placed for x in edges[ei] if blk_of[x] != b)), -b))
        placed.append(best)
        remaining.remove(best)
    order = placed

    def global_check(choice):
        # choice: list over blocks of (bcol, key)
        res = []
        for X, pi, ci in ((1, 0, 1), (2, 2, 3)):
            nodes = [ei for ei, c in linkcol.items() if c == X]
            parent = {ei: ei for ei in nodes}

            def find(a):
                while parent[a] != a:
                    parent[a] = parent[parent[a]]
                    a = parent[a]
                return a
            internal = 0
            for b in range(nb):
                key = choice[b][1]
                for (e1, e2) in key[pi]:
                    ra, rb = find(e1), find(e2)
                    if ra != rb:
                        parent[ra] = rb
                internal += key[ci]
            comps = len(set(find(a) for a in nodes))
            res.append(comps + internal)
        return res[0] == 1 and res[1] == 1

    def rec(i, choice):
        if found and stop_at_first:
            return
        if i == nb:
            leaves[0] += 1
            if verbose and leaves[0] % 100000 == 0:
                print("  progress: %d boundary-consistent assignments, %d combinations" % (leaves[0], combos[0]),
                      file=sys.stderr, flush=True)
            opts = [list(sigs[b][choice[b]].keys()) for b in range(nb)]
            for combo in itertools.product(*opts):
                combos[0] += 1
                ch = [(choice[b], combo[b]) for b in range(nb)]
                if global_check(ch):
                    found.append(ch)
                    if stop_at_first:
                        return
            return
        b = order[i]
        bd = B[b].boundary
        for bcol in sigs[b]:
            ok = True
            for ei, c in zip(bd, bcol):
                lc = linkcol.get(ei)
                if lc is not None and lc != c:
                    ok = False
                    break
            if not ok:
                continue
            newly = []
            for ei, c in zip(bd, bcol):
                if ei not in linkcol:
                    linkcol[ei] = c
                    newly.append(ei)
            choice[b] = bcol
            rec(i + 1, choice)
            choice[b] = None
            for ei in newly:
                del linkcol[ei]
            if found and stop_at_first:
                return

    rec(0, [None] * nb)
    stats["consistent_boundary_assignments"] = leaves[0]
    stats["signature_combinations_checked"] = combos[0]
    if not found:
        return None, stats
    ch = found[0]
    colour = {}
    for b in range(nb):
        bcol, key = ch[b]
        for ei, c in sigs[b][bcol][key].items():
            if ei in colour:
                assert colour[ei] == c
            colour[ei] = c
    red = [ei for ei, c in colour.items() if c == 1]
    blue = [ei for ei, c in colour.items() if c == 2]
    return (red, blue), stats


def describe_pair(n, edges, pair):
    red, blue = pair
    ok, msg = verify_pair(n, edges, red, blue)
    r = cycle_order([edges[i] for i in red])
    b = cycle_order([edges[i] for i in blue])
    return ok, msg, r, b
