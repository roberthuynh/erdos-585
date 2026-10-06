"""Cross-check pairbf (C) against the Python brute force and the DP on random small graphs,
and check every pair pairbf prints with verify_pair (parsed from its output)."""
import os
import random
import subprocess
import sys
import time

import networkx as nx

from common import brute_force_pair, verify_pair
from pairdp import find_pair

BIN = os.path.join(os.path.dirname(os.path.abspath(__file__)), "pairbf")
TMP = "tmp_pairbf_test.edges"


def run_pairbf(edges, tmax=60):
    with open(TMP, "w") as f:
        f.write("# test\n")
        for a, b in edges:
            f.write("%d %d\n" % (a, b))
    out = subprocess.run([BIN, TMP, str(tmax)], capture_output=True, text=True, timeout=tmax + 30).stdout
    return out


def parse_pair(out, edges):
    c1 = c2 = None
    for line in out.splitlines():
        if line.startswith("C1:"):
            c1 = list(map(int, line[3:].split()))
        if line.startswith("C2:"):
            c2 = list(map(int, line[3:].split()))
    idx = {}
    for i, (a, b) in enumerate(edges):
        idx[(min(a, b), max(a, b))] = i

    def to_edges(seq):
        es = []
        for i in range(len(seq)):
            a, b = seq[i], seq[(i + 1) % len(seq)]
            k = (min(a, b), max(a, b))
            if k not in idx:
                return None
            es.append(idx[k])
        return es
    return to_edges(c1), to_edges(c2)


if __name__ == "__main__":
    rng = random.Random(99)
    t0 = time.time()
    budget = float(sys.argv[1]) if len(sys.argv) > 1 else 60
    cases = mism = bad = pos = 0
    while time.time() - t0 < budget:
        kind = rng.choice(["gnp", "reg4", "reg5", "bip"])
        if kind == "gnp":
            n = rng.randint(5, 10)
            G = nx.gnp_random_graph(n, rng.uniform(0.3, 0.7), seed=rng.randint(0, 10**9))
        elif kind == "reg4":
            n = rng.choice([6, 8, 10, 12])
            G = nx.random_regular_graph(4, n, seed=rng.randint(0, 10**9))
        elif kind == "reg5":
            n = rng.choice([6, 8])
            G = nx.random_regular_graph(5, n, seed=rng.randint(0, 10**9))
        else:
            G = nx.convert_node_labels_to_integers(
                nx.bipartite.random_graph(rng.randint(3, 5), rng.randint(3, 5), rng.uniform(0.5, 0.9),
                                          seed=rng.randint(0, 10**9)))
        edges = list(G.edges())
        if rng.random() < 0.5 and len(edges) > 4:
            for _ in range(rng.randint(1, 4)):
                edges.pop(rng.randrange(len(edges)))
        if not edges:
            continue
        n = 1 + max(x for e in edges for x in e)
        out = run_pairbf(edges)
        has_c = out.startswith("PAIR")
        bf = brute_force_pair(n, edges)
        dp = None
        if n <= 7:
            dp, _ = find_pair(n, edges, [list(range(n))])
        cases += 1
        if has_c:
            pos += 1
            r, b = parse_pair(out, edges)
            ok = r is not None and b is not None and verify_pair(n, edges, r, b)[0]
            if not ok:
                bad += 1
                print("BAD PAIR from pairbf", edges, out)
        if has_c != (bf is not None) or (n <= 7 and has_c != (dp is not None)):
            mism += 1
            print("MISMATCH", kind, edges, out, bf, dp)
    msg = ("pairbf vs python brute force (all graphs) and vs DP (graphs with <= 7 vertices): %d graphs (%d with a pair), %d mismatches, %d invalid pairs (%.0fs)"
           % (cases, pos, mism, bad, time.time() - t0))
    print(msg)
    open("test_pairbf.log", "w").write(msg + "\n")
    os.remove(TMP)
