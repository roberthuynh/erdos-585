"""Adversarial check of the proof chain of C1-PAPER.md Theorem 4.3 (lane M3).

The proof uses sparsity (g >= 10) only on named sets. For an instance in which EVERY port is bad
(G - y has no 4-factor for every W-vertex y of degree <= 5), the chain is run with one min-cut
violation S_y per port and petal Q_y = V - S_y:
  step P (Lemma 3.2):  g(Q_y) >= 10 for every port y
  step U (Lemma 4.1):  g(Q - u1) >= 10 for every petal and every partial union used
  step L (Lemma 4.2):  for R_i = Q_1 u ... u Q_i and Q_{i+1}: g(R_i n Q_{i+1}) >= 10, g(R_{i+1}) >= 10
If every named set had g >= 10, the arithmetic of the proof would force the union of all petals to
hold W-deficiency <= 2 while it holds all of D_W: impossible. So the theorem predicts that in every
all-ports-bad instance some named set has g <= 8 (and the checker reports which step). Any instance
where all named sets have g >= 10 is a FAIL (it would refute the proof).
Also verified on the way: the identities used (g(Q) formula, kappa, union != V).
"""
import json
import random
import sys
import time

from c1common import random_c1, has_4factor, min_cut_violation, popcount

SEED = 4417
rng = random.Random(SEED)
t0 = time.time()
fails = []
st = {"generated": 0, "all_ports_bad": 0, "step_counts": {}, "by_s": {}}


def check(c, m):
    if not c:
        fails.append(m)


budget = float(sys.argv[1]) if len(sys.argv) > 1 else 200.0
cfgs = [(s, DU, wmin) for s in (6, 7, 8, 9, 10) for DU in (1, 0) for wmin in (1, 2, 3)]
i = 0
while time.time() - t0 < budget:
    s, DU, wmin = cfgs[i % len(cfgs)]
    i += 1
    G = random_c1(s, rng, DU=DU, wmin=wmin)
    if G is None:
        continue
    st["generated"] += 1
    u1 = s - 1 if DU == 1 else None
    full = G.full
    ports = [w for w in G.W if G.deg[w] <= 5]
    if not ports or not all(not has_4factor(G, delete=[y]) for y in ports):
        continue
    st["all_ports_bad"] += 1
    key = f"s={s},DU={DU}"
    st["by_s"][key] = st["by_s"].get(key, 0) + 1
    petals = []
    failed_at = None
    for y in ports:
        Sm, sig = min_cut_violation(G, y)
        Q = full ^ Sm
        k = popcount(Sm & G.Wmask) - popcount(Sm & G.Umask)
        DC = sum(6 - G.deg[u] for u in G.U if (Sm >> u) & 1)
        check(G.g(Q) == 6 + 2 * DU + 2 * k + 2 * sig - 2 * DC, "g(Q) identity")
        check(G.kappa(Q) == k - 1, "kappa identity")
        if G.g(Q) < 10:
            failed_at = failed_at or f"P: g(Q_y) = {G.g(Q)}"
        else:
            check(DU == 1 and k == 2 and sig == -1 and DC == 0 and G.kappa(Q) == 1, "forced data")
        petals.append(Q)
    if failed_at is None:
        # every petal tight with kappa 1, contains u1
        for Q in petals:
            if G.g(Q ^ (1 << u1)) < 10:
                failed_at = failed_at or "U: g(Q - u1) <= 8"
        R = petals[0]
        for Q in petals[1:]:
            if failed_at:
                break
            check((R | Q) != full, "union is V")
            if G.g(R ^ (1 << u1)) < 10:
                failed_at = "U: g(R - u1) <= 8"
                break
            if (R & Q) == (1 << u1):
                # would contradict deg u1 = 5 given the U step; record
                failed_at = "U': petals meet only in u1 (some g(.-u1) <= 8 must hold)"
                check(G.deg_in(u1, R) + G.deg_in(u1, Q) <= 5, "degree count")
                break
            if G.g(R & Q) < 10:
                failed_at = f"L: g(cap) = {G.g(R & Q)}"
                break
            if G.g(R | Q) < 10:
                failed_at = f"L: g(cup) = {G.g(R | Q)}"
                break
            check(G.g(R & Q) == 10 == G.g(R | Q) and G.kappa(R | Q) == 1, "lattice step")
            R = R | Q
        if failed_at is None:
            # all named sets passed: the proof says this is impossible
            dW = G.Din(R, R & G.Wmask)
            fails.append(f"all named sets have g >= 10: s={s} DU={DU} edges={G.edges} dW={dW}")
            failed_at = "NONE (refutes proof)"
    st["step_counts"][failed_at.split(":")[0]] = st["step_counts"].get(failed_at.split(":")[0], 0) + 1

st["seconds"] = round(time.time() - t0, 1)
st["n_failures"] = len(fails)
st["failures"] = fails[:10]
st["RESULT"] = "PASS" if not fails else "FAIL"
with open("out_adversarial.json", "w") as fh:
    json.dump(st, fh, indent=1)
print(json.dumps(st, indent=1))
sys.exit(0 if not fails else 1)
