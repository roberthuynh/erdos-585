"""selftest.py -- cross-validate the method B deciders (wave8/exb).

Builds test graphs, runs the C decider (bin/h4filt -a) on all of them, and
compares with the PySAT decider (all graphs) and the flow decider (small
bipartite graphs).  Any disagreement is printed and the exit code is 1.

Test sets (graph6 files are written to data/selftest/):
  known   the 23,094 graphs of census/f1/q4free_bip_n15_e33-45.g6
          (census lane: no 4-regular subgraph; here they are only test input)
  plus1   each of 4,000 sampled 'known' graphs plus one random edge
          (same colour classes, max degree <= 6)
  rbip    random bipartite graphs, sides 4..10, max degree <= 6 (some 7)
  rgen    random general graphs, n = 5..12, max degree <= 6
  small   random bipartite graphs with n <= 13, also run through flow
Usage: python selftest.py [seed]
"""

import os
import random
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import deciders as D  # noqa: E402

ROOT = os.path.dirname(HERE)
OUT = os.path.join(ROOT, "data", "selftest")
KNOWN = os.path.join(ROOT, "..", "..", "census", "f1", "q4free_bip_n15_e33-45.g6")
H4FILT = os.path.join(HERE, "bin", "h4filt")


def rand_bip(rng, a, b, m, dmax):
    n = a + b
    pairs = [(i, a + j) for i in range(a) for j in range(b)]
    rng.shuffle(pairs)
    deg = [0] * n
    edges = []
    for u, w in pairs:
        if len(edges) >= m:
            break
        if deg[u] < dmax and deg[w] < dmax:
            edges.append((u, w))
            deg[u] += 1
            deg[w] += 1
    perm = list(range(n))
    rng.shuffle(perm)
    return n, sorted(tuple(sorted((perm[u], perm[w]))) for u, w in edges)


def rand_gen(rng, n, m, dmax):
    pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
    rng.shuffle(pairs)
    deg = [0] * n
    edges = []
    for u, w in pairs:
        if len(edges) >= m:
            break
        if deg[u] < dmax and deg[w] < dmax:
            edges.append((u, w))
            deg[u] += 1
            deg[w] += 1
    return n, sorted(edges)


def plus_one(rng, n, edges):
    col = D.bicolour(n, edges)
    deg = [0] * n
    for u, w in edges:
        deg[u] += 1
        deg[w] += 1
    es = set(edges)
    cand = [(u, w) for u in range(n) for w in range(u + 1, n)
            if col[u] != col[w] and (u, w) not in es and deg[u] < 6 and deg[w] < 6]
    if not cand:
        return None
    return n, sorted(es | {rng.choice(cand)})


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 585
    rng = random.Random(seed)
    os.makedirs(OUT, exist_ok=True)
    sets = {}

    known = [D.parse_g6(l) for l in open(KNOWN) if l.strip()]
    sets["known"] = known
    sample = rng.sample(known, 4000)
    p1 = [plus_one(rng, n, e) for n, e in sample]
    sets["plus1"] = [g for g in p1 if g is not None]
    rb = []
    for _ in range(20000):
        a = rng.randint(4, 10)
        b = rng.randint(4, 10)
        dmax = 7 if rng.random() < 0.1 else 6
        m = rng.randint(10, min(a * b, dmax * min(a, b)))
        rb.append(rand_bip(rng, a, b, m, dmax))
    sets["rbip"] = rb
    rg = []
    for _ in range(5000):
        n = rng.randint(5, 12)
        m = rng.randint(n, 3 * n)
        rg.append(rand_gen(rng, n, m, 6))
    sets["rgen"] = rg
    sm = []
    for _ in range(1500):
        a = rng.randint(4, 7)
        b = rng.randint(4, 13 - a) if 13 - a >= 4 else 4
        m = rng.randint(14, min(a * b, 6 * min(a, b)))
        sm.append(rand_bip(rng, a, b, m, 6))
    sets["small"] = sm

    # graph6 round trip against networkx
    import networkx as nx
    bad_rt = 0
    for name in ("rbip", "rgen"):
        for n, e in sets[name][:2000]:
            s = D.to_g6(n, e)
            G = nx.from_graph6_bytes(s.encode())
            if sorted(tuple(sorted(x)) for x in G.edges()) != e or G.number_of_nodes() != n:
                bad_rt += 1
            if nx.to_graph6_bytes(G, header=False).decode().strip() != s:
                bad_rt += 1
            if (lambda p: (p[0], sorted(p[1])))(D.parse_g6(s)) != (n, e):
                bad_rt += 1
    print(f"graph6 round trip vs networkx: {bad_rt} mismatches")

    fails = bad_rt
    for name, graphs in sets.items():
        path = os.path.join(OUT, f"{name}.g6")
        with open(path, "w") as f:
            for n, e in graphs:
                f.write(D.to_g6(n, e) + "\n")
        t0 = time.time()
        r = subprocess.run([H4FILT, "-a", "-q"], stdin=open(path), capture_output=True,
                           text=True, check=True)
        tc = time.time() - t0
        cver = [ln.split()[1] == "H" for ln in r.stdout.splitlines()]
        assert len(cver) == len(graphs), (name, len(cver), len(graphs))
        t0 = time.time()
        sver = [D.sat_has_h4(n, e)[0] for n, e in graphs]
        ts = time.time() - t0
        mis = [i for i in range(len(graphs)) if cver[i] != sver[i]]
        fl = ""
        if name == "small":
            t0 = time.time()
            fver = [D.flow_has_h4(n, e) for n, e in graphs]
            tf = time.time() - t0
            mf = [i for i in range(len(graphs)) if fver[i] != sver[i]]
            fl = f"; flow vs SAT mismatches {len(mf)} ({tf:.1f} s)"
            fails += len(mf)
        if name == "known":
            fl += f"; graphs with H: {sum(sver)} (expected 0)"
            fails += sum(sver)
        print(f"{name}: {len(graphs)} graphs, with H {sum(sver)}, without {len(graphs) - sum(sver)}; "
              f"C vs SAT mismatches {len(mis)} (C {tc:.2f} s, SAT {ts:.1f} s){fl}")
        for i in mis[:5]:
            print("   mismatch:", D.to_g6(*graphs[i]), "C", cver[i], "SAT", sver[i])
        fails += len(mis)
    # tiny graphs: brute force
    tiny = []
    for _ in range(60):
        a = rng.randint(4, 5)
        b = rng.randint(4, 5)
        tiny.append(rand_bip(rng, a, b, rng.randint(14, min(a * b, 18)), 6))
    bm = sum(D.brute_has_h4(n, e) != D.sat_has_h4(n, e)[0] for n, e in tiny)
    print(f"tiny: {len(tiny)} graphs, with H {sum(D.sat_has_h4(n, e)[0] for n, e in tiny)}; "
          f"brute vs SAT mismatches {bm}")
    fails += bm
    print("SELFTEST", "PASS" if fails == 0 else f"FAIL ({fails})")
    return 0 if fails == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
