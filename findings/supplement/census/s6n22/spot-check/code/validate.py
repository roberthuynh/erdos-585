#!/usr/bin/env python3
"""validate.py (wave8/s6spot): controls for e10cut and spantest.

  validate.py controls         build K66 (= K_{6,6}) and NEG24 (two copies of K_{6,6} minus an
                               edge, joined by two edges: a 2-edge cut, so no test can have a pair)
                               as graph6 files in data/val/ for the e10cut and spantest runs
  validate.py witness          corrupted witnesses must be rejected by spantest.verify_pair
  validate.py flow G6 CUT [IDX ...]
                               recompute the minimum essential cut of the listed graphs (default:
                               all) by max-flow (networkx): min over vertex-disjoint edges e, f of
                               the min cut separating e from f; compare with e10cut's value.
                               (An essential S with |delta(S)| <= 10 < 12 <= 6|S| is not independent,
                               nor is its complement, so it separates two disjoint edges; an edge
                               itself is essential with cut 10, so the two minima agree.)
"""
import sys, os, json, itertools, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import spantest as sp

D = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "data", "val")


def encode_g6(n, edges):
    bits = []
    es = set((min(u, v), max(u, v)) for u, v in edges)
    for j in range(1, n):
        for i in range(j):
            bits.append(1 if (i, j) in es else 0)
    while len(bits) % 6:
        bits.append(0)
    out = chr(n + 63)
    for k in range(0, len(bits), 6):
        val = 0
        for b in bits[k:k + 6]:
            val = 2 * val + b
        out += chr(63 + val)
    return out


def controls():
    k66 = [(a, b) for a in range(6) for b in range(6, 12)]
    # NEG24: sides A = 0..11, B = 12..23; copy 1 on {0..5} x {12..17} minus (0,12),
    # copy 2 on {6..11} x {18..23} minus (6,18); joining edges (0,18), (6,12).
    neg = [(a, b) for a in range(6) for b in range(12, 18) if (a, b) != (0, 12)]
    neg += [(a, b) for a in range(6, 12) for b in range(18, 24) if (a, b) != (6, 18)]
    neg += [(0, 18), (6, 12)]
    for name, n, E in (("K66", 12, k66), ("NEG24", 24, neg)):
        g = encode_g6(n, E)
        n2, E2 = sp.decode_g6(g)
        assert n2 == n and E2 == sorted(E), name
        with open(os.path.join(D, name + ".g6"), "w") as f:
            f.write(g + "\n")
        print(name, "n=%d edges=%d written" % (n, len(E)))


def witness():
    n, edges = 12, [(a, b) for a in range(6) for b in range(6, 12)]
    es = set(edges)
    g = sp.GraphSAT(n, edges, "minisat22")
    ans, r, (c1, c2) = g.test(0, 6)
    g.close()
    assert ans == "SPAN" and sp.verify_pair(n, es, 0, 6, c1, c2)
    bad = {
        "same cycle twice": (c1, list(c1)),
        "reversed copy": (c1, list(reversed(c1))),
        "vertex o included": ([0] + c1[1:], c2),
        "vertex dropped": (c1[:-1], c2),
        "vertex repeated": (c1[:-1] + [c1[0]], c2),
        "non-edge (two A-vertices adjacent)": (sorted(c1, key=lambda v: v >= 6), c2),
        "swap two entries": (c1[:1] + [c1[2], c1[1]] + c1[3:], c2),
    }
    rej = 0
    for k, (a, b) in bad.items():
        ok = sp.verify_pair(n, es, 0, 6, a, b)
        print("%-40s %s" % (k, "ACCEPTED (BAD)" if ok else "rejected"))
        rej += (not ok)
    # many random permutations: verify_pair must agree with a direct recount
    rnd = random.Random(1)
    acc = 0
    for _ in range(20000):
        a = c1[:]
        b = c2[:]
        rnd.shuffle(a if rnd.random() < 0.5 else b)
        ok = sp.verify_pair(n, es, 0, 6, a, b)
        # direct: both are Hamilton cycles of K66 - 0 - 6 and edge-disjoint
        def ham(c):
            return sorted(c) == [v for v in range(12) if v not in (0, 6)] and all(
                ((c[i] < 6) != (c[(i + 1) % 10] < 6)) for i in range(10))
        def es_(c):
            return set(tuple(sorted((c[i], c[(i + 1) % 10]))) for i in range(10))
        direct = ham(a) and ham(b) and not (es_(a) & es_(b))
        assert ok == direct
        acc += ok
    print("random shuffles: agree with a direct recount on 20000 cases; accepted", acc)
    print("WITNESS_CHECK", "PASS" if rej == len(bad) else "FAIL")


def flow(g6, cut, idx):
    import networkx as nx
    lines = open(g6).read().split("\n")
    cuts = [l.split() for l in open(cut).read().strip().split("\n")]
    if not idx:
        idx = list(range(len(cuts)))
    agree = 0
    for i in idx:
        n, edges = sp.decode_g6(lines[i])
        H = nx.DiGraph()
        for u, v in edges:
            H.add_edge(u, v, capacity=1)
            H.add_edge(v, u, capacity=1)
        best = None
        for (a, b), (c, d) in itertools.combinations(edges, 2):
            if len({a, b, c, d}) < 4:
                continue
            H.add_edge("s", a, capacity=1000)
            H.add_edge("s", b, capacity=1000)
            H.add_edge(c, "t", capacity=1000)
            H.add_edge(d, "t", capacity=1000)
            val = nx.maximum_flow_value(H, "s", "t")
            H.remove_node("s")
            H.remove_node("t")
            if best is None or val < best:
                best = val
        mine = int(cuts[i][1])
        same = (best == mine)
        agree += same
        print("graph %d: e10cut=%d flow=%d %s" % (i, mine, best, "agree" if same else "DISAGREE"))
    print("FLOW_CHECK %d/%d agree" % (agree, len(idx)))


if __name__ == "__main__":
    cmd = sys.argv[1]
    if cmd == "controls":
        controls()
    elif cmd == "witness":
        witness()
    elif cmd == "flow":
        flow(sys.argv[2], sys.argv[3], [int(x) for x in sys.argv[4:]])
