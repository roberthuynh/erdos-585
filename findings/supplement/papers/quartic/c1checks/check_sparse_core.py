"""Core lemma (C1-PAPER.md Lemma 4.4) on built sub-case instances, with exact flow-based sparsity.
For each instance: bad ports (flow), a min-cut violation per bad port and its complement Q; exact
min of g over proper sets with >= 2 vertices (c1common.min_g_proper). If sparse: every Q is in P
(g = 10, kappa = 1, u1 in Q), every pair has cap and cup in P, the union of all Q is in P, and the
bad ports have total deficiency <= 2. Usage: check_sparse_core.py CHUNK NCHUNKS"""
import json, random, sys, time
from c1build import build
from c1common import has_4factor, min_cut_violation, min_g_proper, popcount

CH, NCH = int(sys.argv[1]), int(sys.argv[2])
rng = random.Random(777 + 1000 * CH)
t0 = time.time()
plan = [(c, t, eps, v) for (eps, v) in ((0, "y55"), (1, "e1"), (0, "y4")) for c in (4, 5, 6) for t in (8, 9, 10)]
st = {"tested": 0, "sparse": 0, "sparse_bad_ports": {}, "min_g": {}, "pairs": 0, "examples": []}
fails = []
for i, (c, t, eps, v) in enumerate(plan):
    if i % NCH != CH or time.time() - t0 > 200:
        continue
    out = None
    for _ in range(80):
        out = build(c, t, eps, v, rng)
        if out:
            break
    if not out:
        continue
    G, I = out
    u1, full = I["u1"], G.full
    ports = [w for w in G.W if G.deg[w] <= 5]
    bad = [w for w in ports if not has_4factor(G, delete=[w])]
    Qs = []
    for w in bad:
        Sm, sig = min_cut_violation(G, w)
        Qs.append(full ^ Sm)
    mg, wit = min_g_proper(G)
    st["tested"] += 1
    st["min_g"][str(mg)] = st["min_g"].get(str(mg), 0) + 1
    ex = {"c": c, "t": t, "eps": eps, "variant": v, "min_g": mg, "bad": len(bad),
          "bad_def": sum(6 - G.deg[w] for w in bad), "distinct_petals": len(set(Qs))}
    if mg >= 10:
        st["sparse"] += 1
        key = str(len(bad))
        st["sparse_bad_ports"][key] = st["sparse_bad_ports"].get(key, 0) + 1
        inP = lambda Q: Q != full and G.g(Q) == 10 and G.kappa(Q) == 1 and (Q >> u1) & 1
        for Q in Qs:
            if not inP(Q):
                fails.append(f"petal not in P {ex}")
        for a in range(len(Qs)):
            for b in range(a + 1, len(Qs)):
                st["pairs"] += 1
                if not (inP(Qs[a] & Qs[b]) and inP(Qs[a] | Qs[b])):
                    fails.append(f"cap/cup not in P {ex}")
        R = 0
        for Q in Qs:
            R |= Q
        if Qs and not inP(R):
            fails.append(f"union not in P {ex}")
        if ex["bad_def"] > 2:
            fails.append(f"bad deficiency > 2 {ex}")
    st["examples"].append(ex)
    print(json.dumps(ex), f"{time.time()-t0:.0f}s", flush=True)
st["seconds"] = round(time.time() - t0, 1)
st["failures"] = fails
st["RESULT"] = "PASS" if not fails else "FAIL"
json.dump(st, open(f"out_sparse_core_{CH}of{NCH}.json", "w"), indent=1)
print("RESULT", st["RESULT"], st["tested"], st["sparse"])
sys.exit(0 if not fails else 1)
