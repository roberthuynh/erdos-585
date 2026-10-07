"""Adversarial random search (own code).
(R1) Random C1 instances s = 6..10 with low W-degree floors: every one must have a quartic
     subgraph (SAT). A failure refutes Theorem 4.3.
(R2) In every instance where ALL ports are bad (G - y has no 4-factor for every port y), some
     proper set with >= 2 vertices has g <= 8 (the instance is not sparse), as Lemma 4.4 demands;
     also record where the chain breaks. Exact min g by subset DP (n <= 21).
(R3) Lemma 1.5 on E4 instances built to lack a 4-factor (deficiency concentrated): for every
     violation, the two pieces are C1 instances or single vertices with sizes summing to a - 1.
Usage: adversarial.py seed budget_seconds"""
import sys, random, json, time
from ref_common import Bip, random_C1, random_bip_with_degrees, quartic_subgraph, has_4factor_balanced

seed = int(sys.argv[1]) if len(sys.argv) > 1 else 7
budget = float(sys.argv[2]) if len(sys.argv) > 2 else 200
rng = random.Random(seed)
t0 = time.time()
fails = []
c = {"R1": 0, "R1_by_s": {}, "R2_allbad": 0, "R2_allbad_by_s": {}, "R3_instances": 0, "R3_violations": 0}

def popcount(x): return bin(x).count("1")

def min_g_proper(B):
    n = B.n
    adjb = [sum(1 << w for w in B.adj[v]) for v in range(n)]
    e = [0] * (1 << n); best = 10**9
    for S in range(1, (1 << n) - 1):
        low = S & (-S); v = low.bit_length() - 1; rest = S ^ low
        e[S] = e[rest] + popcount(adjb[v] & rest)
        pc = popcount(S)
        if pc >= 2:
            gS = 6 * pc - 2 * e[S]
            if gS < best: best = gS
    return best

# R3 first (cheap)
for a in [4, 5, 6, 7, 8]:
    for _ in range(12):
        DP = rng.randint(3, 4); DQ = DP
        degP = [6] * a; degQ = [6] * a
        # concentrate: one or two vertices carry the deficiency
        for side in (degP, degQ):
            d = DP
            while d > 0:
                i = rng.randrange(min(2, a)) if rng.random() < 0.7 else rng.randrange(a)
                if side[i] > 2:
                    side[i] -= 1; d -= 1
        H = random_bip_with_degrees(a, a, degP, degQ, rng)
        if H is None: continue
        P = list(H.U); Q = list(H.W)
        if has_4factor_balanced(P, Q, H.adj): continue
        c["R3_instances"] += 1
        for code in range(1 << (2 * a)):
            Cb = code & ((1 << a) - 1); Ab = code >> a
            A = [P[i] for i in range(a) if (Ab >> i) & 1]; C = [Q[i] for i in range(a) if (Cb >> i) & 1]
            k = len(A) - len(C)
            if sum(1 for p in A for q in H.adj[p] if q not in C) - 4 * k >= 0: continue
            c["R3_violations"] += 1
            eps = H.D(C) + sum(1 for q in C for p in H.adj[q] if p not in A)
            PA = [p for p in P if p not in A]; QC = [q for q in Q if q not in C]
            ok = (k == 1 and H.D(A) >= 3 + eps and eps <= 1 and len(A) == len(C) + 1
                  and H.D_in(set(A) | set(C), C) == eps and len(QC) == len(PA) + 1
                  and H.D_in(set(PA) | set(QC), PA) <= 1 and len(C) + len(PA) == a - 1)
            if not ok: fails.append(("R3", H.graph6(), code))
        if time.time() - t0 > 40: break

# R1 + R2
while time.time() - t0 < budget:
    s = rng.choice([6, 7, 8, 9, 10])
    wlo = rng.choice([1, 2, 3, 4])
    B = random_C1(s, rng, DU=rng.choice([0, 1]), wlo=wlo, whi=6)
    if B is None: continue
    c["R1"] += 1; c["R1_by_s"][str(s)] = c["R1_by_s"].get(str(s), 0) + 1
    if quartic_subgraph(B.n, B.edges) is None:
        fails.append(("R1-REFUTATION", B.graph6()))
        continue
    ports = [w for w in B.W if B.deg(w) <= 5]
    if ports and all(not has_4factor_balanced([x for x in B.W if x != y], list(B.U), B.adj) for y in ports):
        c["R2_allbad"] += 1; c["R2_allbad_by_s"][str(s)] = c["R2_allbad_by_s"].get(str(s), 0) + 1
        mg = min_g_proper(B)
        if mg >= 10:
            fails.append(("R2-SPARSE-ALLBAD", B.graph6()))

out = dict(seed=seed, counts=c, fails=len(fails), first=[str(f)[:200] for f in fails[:5]], seconds=round(time.time() - t0, 1))
json.dump(out, open(f"out_adversarial_{seed}.json", "w"), indent=1)
print(json.dumps(out, indent=1))
print("RESULT:", "PASS" if not fails else "FAIL")
sys.exit(0 if not fails else 1)
