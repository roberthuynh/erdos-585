"""Identity checks for C1-PAPER.md on random C1 instances (own code).
I1 slack formula (Lemma 1.4 / 3.1), I2 g(V-S) formula (Lemma 3.1), I3 kappa(V-S) = k-1,
I4 flow criterion (min slack < 0 iff no 4-factor of G-y; min slack = maxflow - 4s),
I5 Lemma 3.2's conclusion on every violation whose complement has g >= 10,
J1 Identity 1.2, J2 Identity 1.1, J4 Identity 1.3, J5 basic counts, J6 g = 2d + 6j,
L15 Lemma 1.5 piece structure on random E4 instances.
Exits nonzero on any mismatch."""
import sys, random, json, time
from ref_common import Bip, random_C1, random_bip_with_degrees, maxflow_balanced

rng = random.Random(20261005)
t0 = time.time()
counts = {k: 0 for k in ["I1", "I2", "I3", "I4", "I5", "J1", "J2", "J4", "J5", "J6", "L15", "viol"]}
profiles = {}
bad = []

def popcount(x):
    return bin(x).count("1")

def check_instance(B):
    s, n = B.s, B.n
    adjbits = [sum(1 << w for w in B.adj[v]) for v in range(n)]
    Ubits = (1 << s) - 1
    Wbits = ((1 << n) - 1) ^ Ubits
    def e_in_bits(S):
        return sum(popcount(adjbits[u] & S) for u in range(s) if (S >> u) & 1)
    def g_bits(S):
        return 6 * popcount(S) - 2 * e_in_bits(S)
    def kappa_bits(S):
        return popcount(S & Ubits) - popcount(S & Wbits)
    DU = B.D(B.U)
    u1 = [u for u in B.U if B.deg(u) == 5]
    u1 = u1[0] if u1 else None
    # J5
    counts["J5"] += 1
    if B.g(B.V) != 6 + 2 * DU:
        bad.append(("J5", B.graph6()))
    for v in range(n):
        if g_bits(((1 << n) - 1) ^ (1 << v)) != 2 * DU + 2 * B.deg(v):
            bad.append(("J5b", B.graph6(), v))
    # J2, J6, J4 on all subsets (n <= 15) or random subsets
    allS = range(1 << n) if n <= 15 else (rng.randrange(1 << n) for _ in range(20000))
    for S in allS:
        if S == 0:
            continue
        SU, SW = S & Ubits, S & Wbits
        eS = e_in_bits(S)
        DSU = 6 * popcount(SU) - eS
        DSW = 6 * popcount(SW) - eS
        gS = 6 * popcount(S) - 2 * eS
        kap = popcount(SU) - popcount(SW)
        counts["J2"] += 1
        if not (gS == 2 * DSW + 6 * kap == 2 * DSU - 6 * kap and DSU - DSW == 6 * kap):
            bad.append(("J2", B.graph6(), S))
        j = abs(kap)
        d = DSW if kap >= 0 else DSU
        counts["J6"] += 1
        if gS != 2 * d + 6 * j:
            bad.append(("J6", B.graph6(), S))
        if gS <= 8 and not ((j == 0 and d <= 4) or (j == 1 and d <= 1)):
            bad.append(("J6b", B.graph6(), S))
        # J4: one random vertex of S
        vs = [v for v in range(n) if (S >> v) & 1]
        v = rng.choice(vs)
        counts["J4"] += 1
        if g_bits(S ^ (1 << v)) != gS - 6 + 2 * popcount(adjbits[v] & S):
            bad.append(("J4", B.graph6(), S, v))
    # J1 on random pairs
    for _ in range(3000):
        A = rng.randrange(1 << n); C = rng.randrange(1 << n)
        lhs = g_bits(A | C) + g_bits(A & C)
        # e(A-C, C-A)
        X, Y = A & ~C, C & ~A
        exy = sum(popcount(adjbits[u] & Y) for u in range(s) if (X >> u) & 1) + \
              sum(popcount(adjbits[u] & X) for u in range(s) if (Y >> u) & 1)
        counts["J1"] += 1
        if lhs != g_bits(A) + g_bits(C) - 2 * exy:
            bad.append(("J1", B.graph6(), A, C))
    # Cuts at every port
    ports = [w for w in B.W if B.deg(w) <= 5]
    for y in ports:
        Pbits = Wbits ^ (1 << y)
        P = [w for w in B.W if w != y]
        minslack = None
        exhaustive = (2 * s <= 16)
        cutiter = range(1 << (2 * s)) if exhaustive else (rng.randrange(1 << (2 * s)) for _ in range(30000))
        Wlist = P
        for code in cutiter:
            Cbits = code & Ubits
            Acode = code >> s
            Abits = sum(1 << Wlist[i] for i in range(s) if (Acode >> i) & 1)
            k = popcount(Abits) - popcount(Cbits)
            # direct slack: e(A, U-C) - 4k
            UC = Ubits ^ Cbits
            eA_UC = sum(popcount(adjbits[w] & UC) for w in Wlist if (Abits >> w) & 1)
            sigma = eA_UC - 4 * k
            DA = sum(6 - B.deg(w) for w in Wlist if (Abits >> w) & 1)
            DC = sum(6 - B.deg(u) for u in range(s) if (Cbits >> u) & 1)
            WmA = Wbits ^ Abits  # includes y
            eC_WmA = sum(popcount(adjbits[u] & WmA) for u in range(s) if (Cbits >> u) & 1)
            eps = DC + eC_WmA
            counts["I1"] += 1
            if sigma != 2 * k - DA + eps:
                bad.append(("I1", B.graph6(), y, code))
            Q = ((1 << n) - 1) ^ (Abits | Cbits)
            counts["I2"] += 1
            if g_bits(Q) != 6 + 2 * DU + 2 * k + 2 * sigma - 2 * DC:
                bad.append(("I2", B.graph6(), y, code))
            counts["I3"] += 1
            if kappa_bits(Q) != k - 1:
                bad.append(("I3", B.graph6(), y, code))
            if minslack is None or sigma < minslack:
                minslack = sigma
            if sigma < 0:
                counts["viol"] += 1
                gQ = g_bits(Q)
                prof = (k, sigma, gQ, DC)
                profiles[prof] = profiles.get(prof, 0) + 1
                if k < 1 or DA < 2 * k + 1 + eps:
                    bad.append(("viol-k", B.graph6(), y, code))
                if gQ >= 10:
                    counts["I5"] += 1
                    ok = (DU == 1 and k == 2 and sigma == -1 and DC == 0 and gQ == 10
                          and kappa_bits(Q) == 1 and (u1 is not None and not (Cbits >> u1) & 1)
                          and DA == 5 + eps and eps <= 1 and (Q >> y) & 1 and (Q >> u1) & 1)
                    if not ok:
                        bad.append(("I5", B.graph6(), y, code))
        if exhaustive:
            mf = maxflow_balanced(P, list(B.U), B.adj)
            counts["I4"] += 1
            if minslack != mf - 4 * s:
                bad.append(("I4", B.graph6(), y, minslack, mf))

def check_E4(a):
    """Random E4(a) instance; for every violation verify Lemma 1.5's pieces."""
    for _ in range(50):
        d = rng.randint(0, 4)
        degP = [6] * a; degQ = [6] * a
        for _ in range(d):
            degP[rng.randrange(a)] -= 1
            degQ[rng.randrange(a)] -= 1
        if min(degP) < 0 or min(degQ) < 0:
            continue
        H = random_bip_with_degrees(a, a, degP, degQ, rng)
        if H is None:
            continue
        break
    else:
        return
    s = a; n = 2 * a
    P = list(H.U); Q = list(H.W)  # here "U" is P (size a) and "W" is Q (size a)
    DP = H.D(P)
    for code in range(1 << (2 * a)):
        Cb = code & ((1 << a) - 1)
        Ab = code >> a
        A = [P[i] for i in range(a) if (Ab >> i) & 1]
        C = [Q[i] for i in range(a) if (Cb >> i) & 1]
        k = len(A) - len(C)
        eA_QC = sum(1 for p in A for q in H.adj[p] if q not in C)
        if eA_QC - 4 * k >= 0:
            continue
        counts["L15"] += 1
        DA = H.D(A)
        eps = H.D(C) + sum(1 for q in C for p in H.adj[q] if p not in A)
        ok = (k == 1 and DA >= 3 + eps and eps <= 1)
        # piece 1: A u C, smaller side C with in-piece deficiency eps
        piece1 = set(A) | set(C)
        ok &= (H.D_in(piece1, C) == eps) and (len(A) == len(C) + 1)
        # piece 2: (P-A) u (Q-C), smaller side P-A, in-piece deficiency <= 1
        PA = [p for p in P if p not in A]; QC = [q for q in Q if q not in C]
        piece2 = set(PA) | set(QC)
        ok &= (len(QC) == len(PA) + 1) and (H.D_in(piece2, PA) <= 1)
        ok &= (len(C) + len(PA) == a - 1)
        if not ok:
            bad.append(("L15", H.graph6(), code))

ninst = 0
for s in [5, 6, 7, 8]:
    for DU in [0, 1]:
        for (wlo, whi) in [(1, 6), (3, 6), (4, 6)]:
            reps = 6 if s <= 6 else (3 if s == 7 else 2)
            for _ in range(reps):
                B = random_C1(s, rng, DU=DU, wlo=wlo, whi=whi)
                if B is None:
                    continue
                assert B.is_C1()
                check_instance(B)
                ninst += 1
                if time.time() - t0 > 200:
                    break
for a in [4, 5, 6, 7]:
    for _ in range(4):
        check_E4(a)

out = {"instances": ninst, "counts": counts, "violation_profiles": {str(k): v for k, v in sorted(profiles.items())},
       "mismatches": len(bad), "first_bad": [str(b)[:200] for b in bad[:5]], "seconds": round(time.time() - t0, 1)}
print(json.dumps(out, indent=1))
json.dump(out, open("out_identities.json", "w"), indent=1)
print("RESULT:", "PASS" if not bad else "FAIL")
sys.exit(0 if not bad else 1)
