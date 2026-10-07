#!/usr/bin/env python3
"""Cross-check gen585's C pair test (-p mode) against LANE/tools/pair_oracle.decide and brute.decide.

Random graphs: G(n, p) and random max-degree-6 graphs, n = 6..13, seeded. Prints disagreements.
Run: timeout 240 [temporary path] test_pair.py 600
"""
import json, os, random, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
LANE = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, os.path.join(LANE, "tools"))
import pair_oracle, brute  # noqa: E402


def rand_maxdeg(n, m, D, rng):
    deg = [0] * n
    E = set()
    tries = 0
    while len(E) < m and tries < 20000:
        tries += 1
        a, b = rng.sample(range(n), 2)
        e = (min(a, b), max(a, b))
        if e in E or deg[a] >= D or deg[b] >= D:
            continue
        E.add(e)
        deg[a] += 1
        deg[b] += 1
    return sorted(E)


def main():
    count = int(sys.argv[1]) if len(sys.argv) > 1 else 300
    rng = random.Random(58513)
    graphs = []
    for i in range(count):
        n = rng.randint(6, 13)
        if i % 2 == 0:
            p = rng.uniform(0.3, 0.8)
            E = [(a, b) for a in range(n) for b in range(a + 1, n) if rng.random() < p]
        else:
            m = rng.randint(2 * n, 3 * n - 1)
            E = rand_maxdeg(n, m, 6, rng)
        graphs.append((n, E))
    inp = "".join("%d %d %s\n" % (n, len(E), " ".join("%d %d" % e for e in E)) for n, E in graphs)
    out = subprocess.run([os.path.join(HERE, "gen585"), "-p"], input=inp, capture_output=True, text=True,
                         check=True).stdout.split()
    bad = 0
    stats = {"pair": 0, "nopair": 0}
    for (n, E), c in zip(graphs, out):
        r = pair_oracle.decide(n, E, seconds=30)
        if r["status"] == "TIMEOUT":
            r = brute.decide(n, E)
        o = 1 if r["status"] == "PAIR" else 0
        if n <= 11:
            b = 1 if brute.decide(n, E)["status"] == "PAIR" else 0
            if b != o:
                print("ORACLE/BRUTE DISAGREE", n, E)
        stats["pair" if o else "nopair"] += 1
        if int(c) != o:
            bad += 1
            print("DISAGREE n=%d C=%s oracle=%d edges=%s" % (n, c, o, E))
    print(json.dumps({"graphs": len(graphs), "disagreements": bad, **stats}))


if __name__ == "__main__":
    main()
