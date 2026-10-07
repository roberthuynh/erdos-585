"""Build sub-case instances (rc_build.py), keep the exactly sparse ones (flow test, then brute force for
n <= NMAX), and run the full brute-force Lemma 4.1 / 4.2 / 4.4 test of rc_lattice.test_instance on them.
Also checks, per built instance (sparse or not): the planted cut has slack -1 in G - y, maxflow(G - y)
= 4s - 1 when sparse, and Lemma 3.1's g(Q) = 10, kappa(Q) = 1 for the planted petal.
Usage: rc_built.py SEED BUDGET_SECONDS NMAX"""
import sys, json, random, time
from rc_common import *
from rc_build import build
import rc_lattice as L

seed, budget, NMAX = int(sys.argv[1]), float(sys.argv[2]), int(sys.argv[3])
rng = random.Random(seed)
t0 = time.time()
stats = {"built": 0, "sparse": 0, "lattice_tested": 0, "P_sizes": {}, "bad_def": {}, "by_ct": {}}
while time.time() - t0 < budget:
    c = rng.choice([4, 4, 5])
    tmax = (NMAX - 1) // 2 - c
    if tmax < 6:
        continue
    t = rng.randint(6, tmax)
    eps = rng.choice([0, 1])
    r = build(c, t, eps, rng)
    if r is None:
        continue
    G, info = r
    stats["built"] += 1
    A = mask_of(info["A"]); C = mask_of(info["C"]); y = info["y"]
    k = popc(A) - popc(C)
    sig = G.e_between(A, G.Umask & ~C) - 4 * k
    L.ok("built: planted cut slack -1, k = 2", sig == -1 and k == 2)
    Q = G.Vmask & ~(A | C)
    L.ok("built: planted petal g = 10, kappa = 1, contains y and u1",
         G.g(Q) == 10 and G.kappa(Q) == 1 and (Q >> y) & 1 and (Q >> info["u1"]) & 1)
    mg = min_proper_g(G, cap=10)
    if mg < 10:
        continue
    stats["sparse"] += 1
    key = "c%d_t%d_eps%d" % (c, t, eps)
    stats["by_ct"][key] = stats["by_ct"].get(key, 0) + 1
    val = has_4factor_minus(G, y)[1]
    L.ok("built sparse: maxflow(G - y) = 4s - 1", val == 4 * G.su - 1, val)
    if G.n <= NMAX:
        rec = L.test_instance(G, "built:%d:%s" % (seed, key))
        stats["lattice_tested"] += 1
        ps = str(rec["P_size"])
        stats["P_sizes"][ps] = stats["P_sizes"].get(ps, 0) + 1
        bd = str(rec.get("bad_def"))
        stats["bad_def"][bd] = stats["bad_def"].get(bd, 0) + 1
        if rec["P_size"] >= 2 and "multi_P" not in L.examples:
            L.examples["multi_P"] = {"seed": seed, "key": key, "P_size": rec["P_size"],
                                     "members_with_port": rec.get("P_members_with_port")}
res = {"seed": seed, "stats": stats, "checks": L.cnt, "failures": len(L.fails), "examples": L.examples,
       "seconds": round(time.time() - t0, 1)}
print(json.dumps(res, indent=1))
json.dump(res, open("out_built_%d.json" % seed, "w"), indent=1)
sys.exit(1 if L.fails else 0)
