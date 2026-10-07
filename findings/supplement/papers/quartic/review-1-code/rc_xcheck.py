"""Cross-check: P from min-cut enumeration (rc_chain.family_via_mincuts) equals P from brute force over all
subsets (rc_lattice.enumerate_all), on built sub-case instances and random sparse C1 instances, n <= 21."""
import sys, json, random, time
from rc_common import *
from rc_build import build
import rc_lattice as L
import rc_chain as RC
seed, budget = int(sys.argv[1]), float(sys.argv[2])
rng = random.Random(seed); t0 = time.time(); st = {"built": 0, "random": 0, "nonempty": 0}
while time.time() - t0 < budget:
    if rng.random() < 0.6:
        r = build(4, 6, rng.choice([0, 1]), rng)
        if r is None: continue
        G = r[0]; st["built"] += 1
    else:
        G = random_c1(rng.choice([7, 8]), 1, 4, rng)
        if G is None: continue
        st["random"] += 1
    best, famb, _ = L.enumerate_all(G)
    if best < 10: continue
    fam, low, trunc, ncuts = RC.family_via_mincuts(G)
    L.ok("xcheck: min-cut P == brute-force P (sparse)", set(famb) == fam and not low and not trunc)
    st["nonempty"] += int(bool(fam))
res = {"seed": seed, "stats": st, "checks": L.cnt, "failures": len(L.fails), "seconds": round(time.time() - t0, 1)}
print(json.dumps(res)); json.dump(res, open("out_xcheck_%d.json" % seed, "w"))
sys.exit(1 if L.fails else 0)
