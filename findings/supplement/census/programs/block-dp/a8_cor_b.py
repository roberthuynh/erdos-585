"""Machine check of the multigraphs in Corollary B: K, L6 (every a/c attachment), L6b.

Exact multigraph pair test (fast form): a pair is either two 2-cycles on one vertex pair (needs
multiplicity >= 4) or two cycles of length >= 3 with the same vertex set; each of those projects
onto a simple cycle of the underlying graph with that vertex set (a cycle of length >= 3 uses at
most one edge per parallel class), so it suffices to try every ordered choice (c1, c2) of simple
cycles with equal vertex sets, c1 = c2 allowed, and ask whether every underlying edge has
multiplicity >= its number of uses. Cross-checked against plain enumeration of all multigraph
cycles (common.multigraph_pair) on K and on random small multigraphs."""
import itertools
from collections import Counter, defaultdict

from common import simple_cycles_undirected, multigraph_pair


def mg_pair_fast(mult, nv):
    if any(mm >= 4 for mm in mult.values()):
        return "two 2-cycles"
    und = sorted(mult)
    groups = defaultdict(list)
    for cyc in simple_cycles_undirected(nv, und):
        vs = frozenset(x for i in cyc for x in und[i])
        groups[vs].append(frozenset(cyc))
    for vs, lst in groups.items():
        for i in range(len(lst)):
            for j in range(i, len(lst)):
                use = Counter()
                for e in lst[i]:
                    use[e] += 1
                for e in lst[j]:
                    use[e] += 1
                if all(use[e] <= mult[und[e]] for e in use):
                    return "cycles %s / %s" % (sorted(und[e] for e in lst[i]), sorted(und[e] for e in lst[j]))
    return None


def add(mult, a, b, k=1):
    key = (min(a, b), max(a, b))
    mult[key] = mult.get(key, 0) + k


def degrees(mult, nv):
    d = Counter()
    for (a, b), mm in mult.items():
        assert a != b
        d[a] += mm
        d[b] += mm
    return [d[v] for v in range(nv)]


def bipartite(mult, nv):
    adj = defaultdict(list)
    for (a, b) in mult:
        adj[a].append(b)
        adj[b].append(a)
    col = {}
    for s in range(nv):
        if s in col:
            continue
        col[s] = 0
        st = [s]
        while st:
            x = st.pop()
            for y in adj[x]:
                if y not in col:
                    col[y] = 1 - col[x]
                    st.append(y)
                elif col[y] == col[x]:
                    return False
    return True


# cross-check of the fast test against plain enumeration on random small multigraphs
import random
rng = random.Random(11)
agree = npos = 0
for t in range(400):
    nv = rng.randint(2, 6)
    M = {}
    for a in range(nv):
        for b in range(a + 1, nv):
            if rng.random() < 0.6:
                M[(a, b)] = rng.randint(1, 4)
    if not M:
        continue
    f1 = mg_pair_fast(M, nv) is not None
    f2 = multigraph_pair(M, nv)[0] is not None
    assert f1 == f2, ("fast and plain disagree", M)
    agree += 1
    npos += f1
print("fast multigraph test agrees with plain enumeration on %d random multigraphs (%d with a pair)" % (agree, npos))

Kedges = [(0, 3), (0, 3), (0, 3), (1, 2), (1, 2), (1, 2), (0, 2), (1, 3)]
K = {}
for a, b in Kedges:
    add(K, a, b)
print("K degrees", degrees(K, 4))
# two edge-disjoint Hamilton cycles of K = a pair on all 4 vertices
r, nc = multigraph_pair(K, 4)
print("K: %d multigraph cycles; pair: %s" % (nc, r))
ham_pair = r is not None and len(set(x for (p, _) in r[0] for x in p)) == 4
print("K has two edge-disjoint Hamilton cycles:", ham_pair)

# L6: piece u = triangle a=3u, b=3u+1, c=3u+2; ab, bc tripled, ca single
ends = defaultdict(list)  # piece -> list of K-edge indices at it
for i, (a, b) in enumerate(Kedges):
    ends[a].append(i)
    ends[b].append(i)
bad = 0
count = 0
slow_checked = 0
for choice in itertools.product(*[list(itertools.combinations(range(4), 2)) for _ in range(4)]):
    M = {}
    for u in range(4):
        add(M, 3 * u, 3 * u + 1, 3)
        add(M, 3 * u + 1, 3 * u + 2, 3)
        add(M, 3 * u + 2, 3 * u, 1)
    endpoint = {}  # (K-edge index, piece) -> vertex
    for u in range(4):
        for k, ei in enumerate(ends[u]):
            endpoint[(ei, u, k)] = 3 * u if k in choice[u] else 3 * u + 2
    used = Counter()
    for i, (a, b) in enumerate(Kedges):
        # the K-edge i appears once in ends[a] and once in ends[b]; for parallel edges the
        # position k distinguishes the copies
        ka = ends[a].index(i)
        kb = ends[b].index(i)
        add(M, endpoint[(i, a, ka)], endpoint[(i, b, kb)])
    assert degrees(M, 12) == [6] * 12
    count += 1
    res = mg_pair_fast(M, 12)
    if res is not None:
        bad += 1
        print("L6 attachment", choice, "HAS A PAIR:", res)
print("L6: %d attachments checked, all 6-regular, %d with a pair" % (count, bad))

# L6b: piece u = 4-cycle a=4u, b=4u+1, c=4u+2, d=4u+3; ab, bc, cd tripled, da single
arcs = [(0, 3), (0, 3), (3, 0), (3, 1), (1, 2), (1, 2), (2, 1), (2, 0)]
assert Counter(tuple(sorted(a)) for a in arcs) == Counter(tuple(sorted(e)) for e in Kedges)
M = {}
for u in range(4):
    add(M, 4 * u, 4 * u + 1, 3)
    add(M, 4 * u + 1, 4 * u + 2, 3)
    add(M, 4 * u + 2, 4 * u + 3, 3)
    add(M, 4 * u + 3, 4 * u, 1)
for (u, w) in arcs:
    add(M, 4 * u + 3, 4 * w)
print("L6b degrees", degrees(M, 16), "bipartite:", bipartite(M, 16))
res = mg_pair_fast(M, 16)
print("L6b: pair (fast exact test): %s" % (res,))
