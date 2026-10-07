"""Identity checks for C1-PAPER.md (lane M3) on random C1 instances.

Checked, for random C1(s) instances (D_U in {0, 1}), s = 5..8, every port y and EVERY cut
S = A u C of G - y (A = S_W subset of W - y, C = S_U subset of U), Q = V - S:
  (I1) slack identity: e(A, U - C) - 4k = 2k - D_A + eps, eps = D_C(G - y) + e(W - y - A, C)
  (I2) g(Q) = 6 + 2 D_U + 2k + 2 sigma - 2 D(C)            [Lemma 3.1 of C1-PAPER.md]
  (I3) kappa(Q) = k - 1
  (I4) min over cuts of the slack = maxflow(G - y) - 4s       [flow criterion]
  (I5) for every violation (sigma < 0) with g(Q) >= 10: D_U = 1, k = 2, sigma = -1, u1 not in C,
       g(Q) = 10, kappa(Q) = 1                                 [forced data, Lemma 3.2]
And on random vertex sets / pairs:
  (J1) g(A u B) + g(A n B) = g(A) + g(B) - 2 e(A - B, B - A)  (so g is submodular)
  (J2) g(S) = 2 Din_S(S_W) + 6 kappa(S) and Din_S(S_U) - Din_S(S_W) = 6 kappa(S)
  (J3) f(S) := e(S_W, U - S_U) - 4k(S) equals g(S)/2 - k(S) - D(S_W); f submodular on pairs
  (J4) g(S - v) = g(S) - 6 + 2 deg_S(v)
  (J5) g(V) = 6 + 2 D_U, g(V - v) = 2 D_U + 2 deg(v)
  (J6) (j, d) classification: g(S) = 2d + 6j; g(S) <= 8 implies (j, d) in {(0, <=4), (1, <=1)}
Exit code nonzero on any mismatch. Writes out_identities.json.
"""
import json
import random
import sys
import time


from c1common import BG, Tables, random_c1, has_4factor, max_flow_value, popcount, members

SEED = 31337
rng = random.Random(SEED)
t0 = time.time()
stats = {k: 0 for k in ["instances", "cuts_I1_I2_I3", "ports_I4", "violations", "violations_g_ge_10",
                        "violations_g_ge_10_forced_ok", "pairs_J1", "sets_J2", "sets_J3",
                        "pairs_J3_submod", "sets_J4", "J5", "sets_J6", "sample_I1_explicit"]}
viol_profile = {}
fail = []


def check(cond, msg):
    if not cond:
        fail.append(msg)


instances = []
for s in [5, 6, 7, 8]:
    for DU in [1, 0]:
        for wmin in [4, 3]:
            cnt = {5: 12, 6: 12, 7: 10, 8: 6}[s]
            for _ in range(cnt):
                G = random_c1(s, rng, DU=DU, wmin=wmin)
                if G is not None:
                    instances.append((s, DU, G))

for (s, DU, G) in instances:
    stats["instances"] += 1
    T = Tables(G)
    full = G.full
    u1 = (s - 1) if DU == 1 else None
    # J5
    check(T.g[full] == 6 + 2 * DU, f"J5 g(V) s={s}")
    for v in range(G.n):
        check(T.g[full ^ (1 << v)] == 2 * DU + 2 * G.deg[v], "J5 g(V-v)")
        stats["J5"] += 1
    ports = [w for w in G.W if G.deg[w] <= 5]
    for y in ports:
        rest = full ^ (1 << y)
        if s <= 7:
            masks = []
            m = rest
            while True:
                masks.append(m)
                if m == 0:
                    break
                m = (m - 1) & rest
        else:
            masks = [rng.getrandbits(G.n) & rest for _ in range(20000)]
        minsl = None
        nby = T.nb[y]
        for m in masks:
            nA = T.nW[m]; nC = T.nU[m]; k = nA - nC
            DA = T.DW[m]; DC = T.DU[m]; eS = T.eS[m]
            direct = T.sdegW[m] - eS - 4 * k
            eyC = (nby & m).bit_count()
            eps = (DC + eyC) + ((6 * nC - DC) - eS - eyC)
            sig = 2 * k - DA + eps
            if direct != sig:
                fail.append(f"I1 s={s}")
            comp = full ^ m
            gQ = T.g[comp]
            if gQ != 6 + 2 * DU + 2 * k + 2 * sig - 2 * DC:
                fail.append(f"I2 s={s}")
            if T.kappa[comp] != k - 1:
                fail.append(f"I3 s={s}")
            stats["cuts_I1_I2_I3"] += 1
            if minsl is None or sig < minsl:
                minsl = sig
            if sig < 0:
                stats["violations"] += 1
                key = (k, sig, gQ, DC)
                viol_profile[str(key)] = viol_profile.get(str(key), 0) + 1
                if gQ >= 10:
                    stats["violations_g_ge_10"] += 1
                    ok = (DU == 1 and k == 2 and sig == -1 and DC == 0 and gQ == 10
                          and T.kappa[comp] == 1 and (comp >> u1) & 1 == 1)
                    check(ok, f"I5 s={s} key={key}")
                    if ok:
                        stats["violations_g_ge_10_forced_ok"] += 1
        # I4 (exact only when all cuts were enumerated)
        mf = max_flow_value(G, delete=[y])
        if s <= 7:
            check(minsl == mf - 4 * s, f"I4 s={s} y={y}: {minsl} vs {mf - 4*s}")
            stats["ports_I4"] += 1
        else:
            check(minsl >= mf - 4 * s, "I4 sampled lower bound")
        check((mf == 4 * s) == has_4factor(G, delete=[y]), "I4b")
        # explicit (loop-based) recomputation of I1 on a sample of cuts
        for _ in range(30):
            S = rng.choice(masks)
            A = [v for v in members(S) if v >= G.nu]
            C = [v for v in members(S) if v < G.nu]
            Cs = set(C)
            eAUC = sum(1 for a in A for x in G.adj[a] if x not in Cs)
            kk = len(A) - len(C)
            DA_ = sum(6 - G.deg[a] for a in A)
            DCy = sum(6 - (G.deg[c] - (1 if y in G.adj[c] else 0)) for c in C)
            As = set(A)
            eWyAC = sum(1 for c in C for x in G.adj[c] if x != y and x not in As)
            check(eAUC - 4 * kk == 2 * kk - DA_ + DCy + eWyAC, "I1 explicit")
            stats["sample_I1_explicit"] += 1

    # random sets and pairs
    for _ in range(300):
        A = rng.getrandbits(G.n)
        B = rng.getrandbits(G.n)
        lhs = T.g[A | B] + T.g[A & B]
        rhs = T.g[A] + T.g[B] - 2 * G.e_between(A & ~B & full, B & ~A & full)
        check(lhs == rhs, "J1")
        stats["pairs_J1"] += 1

        def fval(S):
            SW = S & G.Wmask
            SU = S & G.Umask
            eSWout = sum(1 for w in members(SW) for x in G.adj[w] if not (SU >> x) & 1)
            return eSWout - 4 * (popcount(SW) - popcount(SU))

        for S in (A, B):
            SW, SU = S & G.Wmask, S & G.Umask
            dW, dU = G.Din(S, SW), G.Din(S, SU)
            kap = T.kappa[S]
            check(T.g[S] == 2 * dW + 6 * kap and dU - dW == 6 * kap, "J2")
            stats["sets_J2"] += 1
            kS = popcount(SW) - popcount(SU)
            check(2 * fval(S) == T.g[S] - 2 * kS - 2 * G.D(SW), "J3")
            stats["sets_J3"] += 1
            for v in members(S):
                check(T.g[S ^ (1 << v)] == T.g[S] - 6 + 2 * G.deg_in(v, S), "J4")
                stats["sets_J4"] += 1
            # J6
            a, b = popcount(SU), popcount(SW)
            if a == 0 and b == 0:
                continue
            if a <= b:
                j6, d6, dl = b - a, dU, dW
            else:
                j6, d6, dl = a - b, dW, dU
            check(T.g[S] == 2 * d6 + 6 * j6 and dl == d6 + 6 * j6, "J6 formula")
            if T.g[S] <= 8:
                check((j6 == 0 and d6 <= 4) or (j6 == 1 and d6 <= 1), "J6 class")
            stats["sets_J6"] += 1
        check(fval(A | B) + fval(A & B) <= fval(A) + fval(B), "J3 submodular")
        stats["pairs_J3_submod"] += 1

stats["violation_profile_(k,sigma,gQ,D(C))"] = viol_profile
stats["seconds"] = round(time.time() - t0, 1)
stats["failures"] = fail[:20]
stats["n_failures"] = len(fail)
stats["RESULT"] = "PASS" if not fail else "FAIL"
with open("out_identities.json", "w") as fh:
    json.dump(stats, fh, indent=1)
print(json.dumps(stats, indent=1))
sys.exit(0 if not fail else 1)
