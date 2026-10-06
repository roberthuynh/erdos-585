"""Lemma 1.5 on every violation of every graph in a genbg E4 class (graph6 on stdin, first class size a).
Checks k = 1, eps <= 1, D_A >= 3 + eps, piece deficiencies eps and <= 1, sizes sum a - 1, at least one
piece of positive size; also maxflow-4a = min slack. Usage: genbg ... | rc_e4.py a LABEL"""
import sys, json, time
from rc_common import *
a = int(sys.argv[1]); label = sys.argv[2]
cnt = {}; fails = []; t0 = time.time(); ng = 0; nno4 = 0; nviol = 0
def ok(k, c, info=None):
    cnt[k] = cnt.get(k, 0) + 1
    if not c: fails.append((k, info)); print("FAIL", k, info, flush=True)
for line in sys.stdin:
    if not line.strip() or line.startswith('>'): continue
    n, edges = g6decode(line)
    H = Bip(a, a, [(i, j) if i < a else (j, i) for (i, j) in edges]); ng += 1
    for (P, Qs) in ((H.Umask, H.Wmask), (H.Wmask, H.Umask)):
        Pl, Ql = bits(P), bits(Qs)
        val, _ = fourfactor_flow(H, P, Qs)
        best = None
        for am in range(1 << a):
            A = mask_of(Pl[i] for i in range(a) if (am >> i) & 1)
            eAQ = [popc(H.adj[x] & Qs) for x in Pl]
            for cm in range(1 << a):
                C = mask_of(Ql[i] for i in range(a) if (cm >> i) & 1)
                k = popc(A) - popc(C)
                sl = H.e_between(A, Qs & ~C) - 4 * k
                best = sl if best is None or sl < best else best
                if sl >= 0: continue
                nviol += 1
                eps = H.defG(C) + H.e_between(P & ~A, C); DA = H.defG(A)
                ok("k=1, eps<=1, D_A>=3+eps", k == 1 and eps <= 1 and DA >= 3 + eps, (k, eps, DA))
                S1 = A | C; S2 = (P & ~A) | (Qs & ~C)
                ok("piece1 smaller side C: in-piece deficiency = eps", H.defIn(C, S1) == eps)
                ok("piece2 smaller side P-A: in-piece deficiency <= 1", H.defIn(P & ~A, S2) <= 1)
                ok("sizes |C| + |P-A| = a-1, one positive", popc(C) + popc(P & ~A) == a - 1 and a - 1 >= 1)
        ok("min slack = maxflow - 4a", best == val - 4 * a, (best, val))
        if val < 4 * a: nno4 += 1
res = {"label": label, "graphs": ng, "orientations_without_4factor": nno4, "violations": nviol,
       "checks": cnt, "failures": len(fails), "seconds": round(time.time() - t0, 1)}
print(json.dumps(res)); json.dump(res, open("out_e4_%s.json" % label, "w"))
sys.exit(1 if fails else 0)
