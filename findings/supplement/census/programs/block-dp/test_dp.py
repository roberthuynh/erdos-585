"""Validate pairdp.find_pair against brute force on random small graphs.

1. Local enumerator vs naive 3^m enumeration on tiny blocks.
2. DP verdict (random partitions) vs brute_force_pair verdict (all cycles grouped by vertex set).
Every pair found by either method is checked with verify_pair.
"""
import itertools
import random
import sys
import time

import networkx as nx

from common import adjacency, brute_force_pair, verify_pair
from pairdp import Block, find_pair

out = open("test_dp.log", "a")  # runs append; each run logs its seed


def log(s):
    print(s)
    out.write(s + "\n")
    out.flush()


def naive_local_count(n, edges, blockverts):
    adj = adjacency(n, edges)
    blk = Block(n, edges, adj, blockverts, None)
    m = len(blk.local)
    cnt = 0
    for col in itertools.product((0, 1, 2), repeat=m):
        ok = True
        for v in blk.verts:
            r = sum(1 for li in blk.inc[v] if col[li] == 1)
            b = sum(1 for li in blk.inc[v] if col[li] == 2)
            if (r, b) not in ((0, 0), (2, 2)):
                ok = False
                break
        if ok:
            cnt += 1
    fast = sum(1 for _ in blk.enumerate_local())
    return cnt, fast, m


SEED = int(sys.argv[2]) if len(sys.argv) > 2 else 20261004
rng = random.Random(SEED)
log("run with seed %d" % SEED)

# ---- 1. local enumeration counts
t0 = time.time()
bad = 0
tested = 0
while tested < 60:
    n = rng.randint(4, 8)
    G = nx.gnp_random_graph(n, rng.uniform(0.4, 0.9), seed=rng.randint(0, 10**9))
    edges = list(G.edges())
    if not edges:
        continue
    k = rng.randint(1, n)
    bv = rng.sample(range(n), k)
    adj = adjacency(n, edges)
    m = len(set(ei for v in bv for (_, ei) in adj[v]))
    if m > 13:
        continue
    c1, c2, m = naive_local_count(n, edges, bv)
    tested += 1
    if c1 != c2:
        bad += 1
        log("LOCAL MISMATCH n=%d edges=%s block=%s naive=%d fast=%d" % (n, edges, bv, c1, c2))
log("local enumeration: %d random blocks, %d mismatches (%.1fs)" % (tested, bad, time.time() - t0))

# ---- 2. DP vs brute force
t0 = time.time()
stats = {"pos": 0, "neg": 0, "mismatch": 0, "badpair": 0}
cases = 0
while time.time() - t0 < float(sys.argv[1] if len(sys.argv) > 1 else 150):
    kind = rng.choice(["gnp", "reg4", "reg5", "reg6", "bip"])
    if kind == "gnp":
        n = rng.randint(5, 9)
        G = nx.gnp_random_graph(n, rng.uniform(0.3, 0.7), seed=rng.randint(0, 10**9))
    elif kind == "reg4":
        n = rng.choice([6, 7, 8, 9, 10, 11, 12])
        G = nx.random_regular_graph(4, n, seed=rng.randint(0, 10**9))
    elif kind == "reg5":
        n = rng.choice([6, 8])
        G = nx.random_regular_graph(5, n, seed=rng.randint(0, 10**9))
    elif kind == "reg6":
        n = 7
        G = nx.random_regular_graph(6, n, seed=rng.randint(0, 10**9))
    else:
        a = rng.randint(3, 5)
        G = nx.bipartite.random_graph(a, rng.randint(3, 5), rng.uniform(0.5, 0.9), seed=rng.randint(0, 10**9))
        G = nx.convert_node_labels_to_integers(G)
    # random edge deletions to create negatives too
    edges = list(G.edges())
    if rng.random() < 0.5 and len(edges) > 4:
        for _ in range(rng.randint(1, 4)):
            edges.pop(rng.randrange(len(edges)))
    n = G.number_of_nodes()
    bf = brute_force_pair(n, edges)
    nblocks = rng.randint(1, min(4, n))
    perm = list(range(n))
    rng.shuffle(perm)
    cuts = sorted(rng.sample(range(1, n), nblocks - 1)) if nblocks > 1 else []
    blocks = []
    prev = 0
    for c in cuts + [n]:
        blocks.append(perm[prev:c])
        prev = c
    tc = time.time()
    dp, st = find_pair(n, edges, blocks)
    cases += 1
    if time.time() - tc > 5:
        log("  slow case: kind=%s n=%d m=%d blocks=%d %.1fs" % (kind, n, len(edges), len(blocks), time.time() - tc))
    if bf is not None:
        stats["pos"] += 1
        ok, _ = verify_pair(n, edges, bf[0], bf[1])
        if not ok:
            stats["badpair"] += 1
            log("BRUTE FORCE PAIR FAILS VERIFY: %s" % (edges,))
    else:
        stats["neg"] += 1
    if dp is not None:
        ok, msg = verify_pair(n, edges, dp[0], dp[1])
        if not ok:
            stats["badpair"] += 1
            log("DP PAIR FAILS VERIFY (%s): n=%d edges=%s blocks=%s" % (msg, n, edges, blocks))
    if (bf is None) != (dp is None):
        stats["mismatch"] += 1
        log("MISMATCH kind=%s n=%d edges=%s blocks=%s bf=%s dp=%s" % (kind, n, edges, blocks, bf, dp))
log("DP vs brute force: %d graphs (%d with a pair, %d without), %d verdict mismatches, %d invalid pairs (%.1fs)"
    % (cases, stats["pos"], stats["neg"], stats["mismatch"], stats["badpair"], time.time() - t0))
