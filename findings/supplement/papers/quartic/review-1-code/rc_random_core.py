"""Lemma 4.4 at larger s with flows only (no brute force). Random C0 gadgets (W-degrees >= 5) and C1
instances with D_U = 1 and W-degrees >= 4 (so no trivially non-sparse V - w). For each: bad ports by
max flow; exact sparsity (min_proper_g). Checks: sparse C0 => no bad port; sparse C1 => bad-port
deficiency <= 2 and every bad port has maxflow(G - y) = 4s - 1; and the contrapositive the theorem
needs: every port bad => not sparse. Usage: rc_random_core.py SEED BUDGET SMIN SMAX"""
import sys, json, random, time
from rc_common import *

seed, budget, smin, smax = int(sys.argv[1]), float(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
rng = random.Random(seed)
t0 = time.time()
cnt = {}; fails = []
st = {"inst": 0, "sparse": 0, "with_bad": 0, "all_bad": 0, "sparse_with_bad": 0, "by_DU": {"0": 0, "1": 0}}


def ok(k, c, info=None):
    cnt[k] = cnt.get(k, 0) + 1
    if not c:
        fails.append((k, info)); print("FAIL", k, info, flush=True)


while time.time() - t0 < budget:
    s = rng.randint(smin, smax)
    DU = rng.choice([0, 1])
    G = random_c1(s, DU, 5 if DU == 0 else 4, rng)
    if G is None:
        continue
    st["inst"] += 1; st["by_DU"][str(DU)] += 1
    ports = [w for w in bits(G.Wmask) if G.deg[w] <= 5]
    flows = {y: has_4factor_minus(G, y) for y in ports}
    bad = [y for y in ports if not flows[y][0]]
    st["with_bad"] += int(bool(bad))
    need_sparsity = bool(bad)
    sparse = None
    if need_sparsity or rng.random() < 0.1:
        sparse = min_proper_g(G, cap=10) >= 10
        st["sparse"] += int(sparse)
    if bad and len(bad) == len(ports):
        st["all_bad"] += 1
        ok("every port bad => not sparse", not sparse)
    if sparse and bad:
        st["sparse_with_bad"] += 1
        if DU == 0:
            ok("sparse C0 => no bad port", False, bad)
        else:
            ok("sparse C1 => bad-port deficiency <= 2", sum(6 - G.deg[y] for y in bad) <= 2)
            ok("sparse C1 => maxflow(G - y) = 4s - 1 at bad ports", all(flows[y][1] == 4 * s - 1 for y in bad))
res = {"seed": seed, "stats": st, "checks": cnt, "failures": len(fails), "seconds": round(time.time() - t0, 1)}
print(json.dumps(res)); json.dump(res, open("out_rcore_%d.json" % seed, "w"))
sys.exit(1 if fails else 0)
