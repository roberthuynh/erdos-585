#!/usr/bin/env python3
"""Compare rvpairtest (reviewer's C pair test) with tools/brute.py on random graphs.
Usage: validate_rvpair.py COUNT SEED [OUT_GRAPHS_FILE]"""
import random, subprocess, sys, time, os
sys.path.insert(0, "[local path]")
import brute  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))
count, seed = int(sys.argv[1]), int(sys.argv[2])
rng = random.Random(seed)


def rand_graph():
    kind = rng.random()
    n = rng.randint(5, 12)
    pairs = [(a, b) for a in range(n) for b in range(a + 1, n)]
    rng.shuffle(pairs)
    deg = [0] * n
    edges = []
    if kind < 0.5:  # degree-capped at 6, target edge count around 2.2n..3.2n
        target = rng.randint(int(2.0 * n), int(3.3 * n))
        for a, b in pairs:
            if len(edges) >= target:
                break
            if deg[a] < 6 and deg[b] < 6:
                edges.append((a, b)); deg[a] += 1; deg[b] += 1
    else:  # uncapped G(n,p)
        n = rng.randint(5, 10)
        p = rng.uniform(0.3, 0.8)
        edges = [(a, b) for a in range(n) for b in range(a + 1, n) if rng.random() < p]
    return n, edges


graphs = []
# fixed cases: K5 (pair), K2 v C5 (no pair), K6 minus an edge (pair), 5-cycle (no pair)
k5 = [(a, b) for a in range(5) for b in range(a + 1, 5)]
k2c5 = [(0, 1)] + [(a, b) for a in (0, 1) for b in range(2, 7)] + [(2, 3), (3, 4), (4, 5), (5, 6), (6, 2)]
k6e = [(a, b) for a in range(6) for b in range(a + 1, 6) if (a, b) != (0, 1)]
graphs += [(5, k5), (7, k2c5), (6, k6e), (5, [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)])]
while len(graphs) < count:
    graphs.append(rand_graph())

inp = "".join(f"{n} {len(e)} " + " ".join(f"{a} {b}" for a, b in e) + "\n" for n, e in graphs)
t0 = time.time()
out = subprocess.run([os.path.join(HERE, "rvpairtest")] + (["v" + os.environ.get("RVVER", "1")]), input=inp, capture_output=True, text=True, timeout=200)
mine = [int(x) for x in out.stdout.split()]
t1 = time.time()
assert len(mine) == len(graphs), (len(mine), len(graphs), out.stderr)
dis = 0
npair = 0
for (n, e), m in zip(graphs, mine):
    b = brute.decide(n, e)["status"] == "PAIR"
    npair += b
    if b != bool(m):
        dis += 1
        print("DISAGREE", n, e, "brute", b, "mine", m)
t2 = time.time()
print(f"graphs={len(graphs)} brute_pair={npair} brute_nopair={len(graphs)-npair} disagreements={dis} "
      f"c_time={t1-t0:.2f}s brute_time={t2-t1:.1f}s {out.stderr.strip()}")
if len(sys.argv) > 3:
    with open(sys.argv[3], "w") as f:
        f.write(inp)
