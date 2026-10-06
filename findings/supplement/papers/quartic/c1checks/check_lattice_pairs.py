"""Lemma 4.2 on distinct petals (C1-PAPER.md). For built sub-case instances, every bad port y gets its
two extreme violations of G - y (minimal and maximal minimum cuts, from the residual graph of one max
flow), so up to two petals per port. For every pair of petals (Q, Q'), checked: union != V; the
intersection is not {u1} whenever both Q - u1, Q' - u1 have g >= 10; g(cap) + g(cup) <= 20; and when
g(cap), g(cup) >= 10 (true in a sparse instance), both are in P. Also every petal's forced data.
Usage: check_lattice_pairs.py SEED_OFFSET"""
import json, random, sys, time
import networkx as nx
from c1build import build
from c1common import has_4factor, popcount

off = int(sys.argv[1]) if len(sys.argv) > 1 else 0
rng = random.Random(5150 + off)
t0 = time.time()
fails, st = [], {"instances": 0, "petals": 0, "distinct_pairs": 0, "pairs_cap_cup_in_P": 0,
                 "pairs_premise_failed": 0, "ports_with_two_extremes": 0}


def extreme_petals(G, y):
    H = nx.DiGraph()
    for u in G.U:
        H.add_edge("s", u, capacity=4)
    for w in G.W:
        if w != y:
            H.add_edge(w, "t", capacity=4)
    for (a, b) in G.gedges:
        if b != y:
            H.add_edge(a, b, capacity=1)
    val, flow = nx.maximum_flow(H, "s", "t")
    R = nx.DiGraph()
    for a, nbrs in flow.items():
        for b, f in nbrs.items():
            cap = H[a][b]["capacity"]
            if f < cap:
                R.add_edge(a, b)
            if f > 0:
                R.add_edge(b, a)
    src = nx.descendants(R, "s") | {"s"} if "s" in R else {"s"}
    tsink = nx.ancestors(R, "t") | {"t"} if "t" in R else {"t"}
    out = []
    for side in (src, set(H.nodes()) - tsink):
        U1 = {v for v in side if isinstance(v, int) and v < G.nu}
        W1 = {v for v in side if isinstance(v, int) and v >= G.nu}
        A = [w for w in G.W if w != y and w not in W1]
        C = [u for u in G.U if u not in U1]
        Sm = sum(1 << v for v in A + C)
        out.append(G.full ^ Sm)
    return out, val


for i in range(400):
    if time.time() - t0 > 200:
        break
    c, t = rng.choice([4, 5, 6]), rng.choice([7, 8, 9, 10])
    eps, v = rng.choice([(0, "y55"), (1, "e1"), (0, "y4")])
    o = build(c, t, eps, v, rng)
    if not o:
        continue
    G, I = o
    st["instances"] += 1
    u1, full = I["u1"], G.full
    inP = lambda Q: Q != full and popcount(Q) >= 2 and G.g(Q) == 10 and G.kappa(Q) == 1 and (Q >> u1) & 1
    petals = []
    for w in [x for x in G.W if G.deg[x] <= 5]:
        if has_4factor(G, delete=[w]):
            continue
        qs, val = extreme_petals(G, w)
        if qs[0] != qs[1]:
            st["ports_with_two_extremes"] += 1
        for Q in qs:
            Sm = full ^ Q
            k = popcount(Sm & G.Wmask) - popcount(Sm & G.Umask)
            sig = val - 4 * G.nu
            if G.g(Q) >= 10 and not (k == 2 and sig == -1 and inP(Q)):
                fails.append("forced data")
            if Q not in petals:
                petals.append(Q)
    st["petals"] += len(petals)
    for a in range(len(petals)):
        for b in range(a + 1, len(petals)):
            Q, Qp = petals[a], petals[b]
            st["distinct_pairs"] += 1
            if (Q | Qp) == full:
                fails.append("union = V")
            if G.g(Q ^ (1 << u1)) >= 10 and G.g(Qp ^ (1 << u1)) >= 10 and (Q & Qp) == (1 << u1):
                fails.append("meet only in u1 despite U-step premise")
            if G.g(Q & Qp) + G.g(Q | Qp) > 20:
                fails.append("submodularity")
            if G.g(Q & Qp) >= 10 and G.g(Q | Qp) >= 10:
                if inP(Q & Qp) and inP(Q | Qp):
                    st["pairs_cap_cup_in_P"] += 1
                else:
                    fails.append("cap/cup not in P")
            else:
                st["pairs_premise_failed"] += 1
st["seconds"] = round(time.time() - t0, 1)
st["failures"] = fails[:10]
st["RESULT"] = "PASS" if not fails else "FAIL"
json.dump(st, open(f"out_lattice_pairs_{off}.json", "w"), indent=1)
print(json.dumps(st))
sys.exit(0 if not fails else 1)
