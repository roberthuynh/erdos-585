"""Referee 2: adversarial searches against the conclusions (own code).

  G1  greedy maximal quartic-free bipartite graphs with max degree <= 6: add random edges
      (sides p, q chosen at random, |p - q| <= 2) while SAT says no quartic subgraph; record
      max of e - 3n. Theorem 4.3 / Cor 5.3 predict e - 3n <= -5 always.
  G2  random E4 and C1 instances at larger n (s up to 30): SAT must find a quartic subgraph.
  G3  random general (non-bipartite) graphs with max degree <= 6 and e = 3n - 2 (P_2), plus the
      Theorem 5 shape (C0 instance plus one edge inside the larger side): SAT must find one.
Usage: r2_adversarial.py SEED BUDGET_SECONDS PART   (PART = G1 | G2 | G3)
Writes out_adv_<PART>_<SEED>.json; exit 1 if any prediction fails.
"""
import json
import os
import random
import sys
import time
from r2common import random_C1, random_bip_degseq, quartic_subgraph

HERE = os.path.dirname(os.path.abspath(__file__))


def greedy_q4free(p, q, rng):
    n = p + q
    deg = [0] * n
    edges = []
    eset = set()
    cand = [(u, p + w) for u in range(p) for w in range(q)]
    rng.shuffle(cand)
    for (u, w) in cand:
        if deg[u] >= 6 or deg[w] >= 6:
            continue
        trial = edges + [(u, w)]
        if quartic_subgraph(n, trial) is None:
            edges = trial
            deg[u] += 1
            deg[w] += 1
    return edges


def part_G1(rng, budget):
    t0 = time.time()
    best = {}
    fails = []
    runs = 0
    while time.time() - t0 < budget:
        p = rng.randint(6, 13)
        q = p + rng.choice([0, 0, 1, 1, 2])
        edges = greedy_q4free(p, q, rng)
        n = p + q
        val = len(edges) - 3 * n
        runs += 1
        key = str(n)
        if key not in best or val > best[key][0]:
            best[key] = (val, p, q, edges)
        if val >= -4:
            fails.append(dict(p=p, q=q, edges=edges))
    summary = {k: v[0] for k, v in sorted(best.items(), key=lambda x: int(x[0]))}
    return dict(runs=runs, max_e_minus_3n_by_n=summary, fails=fails), fails


def part_G2(rng, budget):
    t0 = time.time()
    fails = []
    cnt = {"C1": 0, "E4": 0}
    while time.time() - t0 < budget:
        s = rng.randint(8, 30)
        if rng.random() < 0.5:
            G = random_C1(s, rng.choice([0, 1]), rng.choice([1, 2, 3]), rng)
            kind = "C1"
        else:
            # E4(s): both sides s, deficiency d <= 4 on each side
            d = rng.choice([0, 1, 2, 3, 4])
            udef = [0] * s
            wdef = [0] * s
            for _ in range(d):
                udef[rng.randrange(s)] += 1
                wdef[rng.randrange(s)] += 1
            if max(udef) > 2 or max(wdef) > 2:
                continue
            G = random_bip_degseq(s, s, [6 - x for x in udef], [6 - x for x in wdef], rng)
            kind = "E4"
        if G is None:
            continue
        cnt[kind] += 1
        if quartic_subgraph(G.n, G.edges) is None:
            fails.append(dict(kind=kind, s=G.s, edges=G.edges))
    return dict(counts=cnt, fails=fails), fails


def random_general(n, m, rng):
    """random simple graph with max degree <= 6 and exactly m edges, or None"""
    for _ in range(200):
        deg = [0] * n
        es = set()
        tries = 0
        while len(es) < m and tries < 50 * m:
            tries += 1
            a, b = rng.randrange(n), rng.randrange(n)
            if a == b:
                continue
            a, b = min(a, b), max(a, b)
            if (a, b) in es or deg[a] >= 6 or deg[b] >= 6:
                continue
            es.add((a, b))
            deg[a] += 1
            deg[b] += 1
        if len(es) == m:
            return sorted(es)
    return None


def part_G3(rng, budget):
    t0 = time.time()
    fails = []
    cnt = {"random": 0, "thm5shape": 0}
    while time.time() - t0 < budget:
        if rng.random() < 0.5:
            n = rng.randint(7, 40)
            es = random_general(n, 3 * n - 2, rng)
            if es is None:
                continue
            cnt["random"] += 1
            if quartic_subgraph(n, es) is None:
                fails.append(dict(kind="random", n=n, edges=es))
        else:
            s = rng.randint(5, 25)
            G = random_C1(s, 0, rng.choice([1, 2]), rng)
            if G is None:
                continue
            # add one edge inside W (the larger side) between two degree-<=5 vertices
            W5 = [w for w in G.W if G.deg[w] <= 5]
            if len(W5) < 2:
                continue
            a, b = rng.sample(W5, 2)
            es = list(G.edges) + [(min(a, b), max(a, b))]
            cnt["thm5shape"] += 1
            if quartic_subgraph(G.n, es) is None:
                fails.append(dict(kind="thm5", s=s, edges=es))
    return dict(counts=cnt, fails=fails), fails


def main(seed, budget, part):
    rng = random.Random(seed)
    fn = {"G1": part_G1, "G2": part_G2, "G3": part_G3}[part]
    res, fails = fn(rng, budget)
    res["seed"] = seed
    with open(os.path.join(HERE, f"out_adv_{part}_{seed}.json"), "w") as f:
        json.dump(res, f)
    short = {k: v for k, v in res.items() if k != "fails"}
    short["n_fails"] = len(fails)
    print(json.dumps(short))
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main(int(sys.argv[1]), float(sys.argv[2]), sys.argv[3]))
