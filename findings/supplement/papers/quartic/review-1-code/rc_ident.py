"""Referee checks of Identities 1.1-1.3, Lemma 1.4 (slack formula and min-cut = maxflow), Lemma 1.5
(piece deficiencies), Lemma 3.1 (g(Q), kappa(Q)), basic counts, the (j, d) arithmetic of Lemma 2.1,
and the localized Lemma 3.2 implication. Usage: rc_ident.py SEED NINST"""
import sys, json, random, time
from rc_common import *

seed = int(sys.argv[1]); NINST = int(sys.argv[2])
rng = random.Random(seed)
cnt = {}
fails = []


def ok(name, cond, info=None):
    cnt[name] = cnt.get(name, 0) + 1
    if not cond:
        fails.append((name, info))
        if len(fails) < 20:
            print("FAIL", name, info)


def check_sets(G, nsets):
    n = G.n
    for _ in range(nsets):
        S = rng.getrandbits(n) & G.Vmask
        SU, SW = S & G.Umask, S & G.Wmask
        eS = G.e_in(S)
        dU, dW = G.defIn(SU, S), G.defIn(SW, S)
        kap = popc(SU) - popc(SW)
        gS = 6 * popc(S) - 2 * eS
        ok("I1.1 D^S(S_U)=6|S_U|-e(S)", dU == 6 * popc(SU) - eS)
        ok("I1.1 D^S(S_W)=6|S_W|-e(S)", dW == 6 * popc(SW) - eS)
        ok("I1.1 g=2D^S(S_W)+6kappa=2D^S(S_U)-6kappa", gS == 2 * dW + 6 * kap == 2 * dU - 6 * kap)
        # (j, d) form, computed from sides directly
        if popc(SU) >= popc(SW):
            j, d, dl = popc(SU) - popc(SW), dW, dU
        else:
            j, d, dl = popc(SW) - popc(SU), dU, dW
        ok("I1.1 g=2d+6j, larger side d+6j", gS == 2 * d + 6 * j and dl == d + 6 * j)
        if gS <= 8 and 2 <= popc(S) <= n - 1:
            ok("L2.1 g<=8 => (j,d) in {(0,<=4),(1,<=1)}", (j == 0 and d <= 4) or (j == 1 and d <= 1), (j, d))
        # Identity 1.3
        for v in bits(S)[:3]:
            Sv = S & ~(1 << v)
            ok("I1.3 g(S-v)=g(S)-6+2deg_S(v)", G.g(Sv) == gS - 6 + 2 * popc(G.adj[v] & S))
        # Identity 1.2
        T = rng.getrandbits(n) & G.Vmask
        lhs = G.g(S | T) + G.g(S & T)
        rhs = G.g(S) + G.g(T) - 2 * G.e_between(S & ~T, T & ~S)
        ok("I1.2 g(AuB)+g(AnB)=g(A)+g(B)-2e(A-B,B-A)", lhs == rhs)


def check_c1(G, DU, exhaustive, ncut):
    s = G.su
    U, W = G.Umask, G.Wmask
    u1 = [u for u in range(s) if G.deg[u] == 5]
    eG = G.e_in(G.Vmask)
    DW = G.defG(W)
    ok("basic e=6s-D_U", eG == 6 * s - DU)
    ok("basic D_W=6+D_U", DW == 6 + DU)
    ok("basic g(V)=6+2D_U", G.g(G.Vmask) == 6 + 2 * DU)
    for w in bits(W):
        ok("basic g(V-w)=2D_U+2deg(w)", G.g(G.Vmask & ~(1 << w)) == 2 * DU + 2 * G.deg[w])
    ports = [w for w in bits(W) if G.deg[w] <= 5]
    prof = {}
    for y in ports:
        P = W & ~(1 << y)
        Pl, Ul = bits(P), bits(U)
        has4, val = has_4factor_minus(G, y)
        best = None
        if exhaustive:
            itr = ((a, c) for a in range(1 << s) for c in range(1 << s))
        else:
            itr = ((rng.getrandbits(s), rng.getrandbits(s)) for _ in range(ncut))
        for (am, cm) in itr:
            A = mask_of(Pl[i] for i in range(s) if (am >> i) & 1)
            C = mask_of(Ul[i] for i in range(s) if (cm >> i) & 1)
            k = popc(A) - popc(C)
            eAUC = G.e_between(A, U & ~C)
            sig = eAUC - 4 * k
            DA = G.defG(A); DC = G.defG(C)
            eps = DC + G.e_between(C, W & ~A)
            # Lemma 1.4 inside G - y: deficiency of C in G - y, plus e(P - A, C)
            DCy = sum(6 - popc(G.adj[c] & P) for c in bits(C))
            epsy = DCy + G.e_between(P & ~A, C)
            ok("L1.4 slack=2k-D_A+eps (eps as in L3.1)", sig == 2 * k - DA + eps)
            ok("L3.1 eps=D(C)+e(C,W-A) equals eps in G-y", eps == epsy)
            Qs = G.Vmask & ~(A | C)
            gQ = G.g(Qs)
            ok("L3.1 g(Q)=6+2D_U+2k+2sig-2D(C)", gQ == 6 + 2 * DU + 2 * k + 2 * sig - 2 * DC)
            ok("L3.1 kappa(Q)=k-1", G.kappa(Qs) == k - 1)
            if best is None or sig < best:
                best = sig
            if sig < 0:
                ok("L3.2 violation has k>=1 and D_A>=2k+1+eps", k >= 1 and DA >= 2 * k + 1 + eps)
                ok("L3.2 D_A<=6 so k<=2", DA <= 6 and k <= 2, (DA, k))
                key = (k, sig, gQ, DC)
                prof[key] = prof.get(key, 0) + 1
                if gQ >= 10:
                    good = (DU == 1 and k == 2 and sig == -1 and DC == 0 and DA == 5 + eps and eps <= 1
                            and gQ == 10 and G.kappa(Qs) == 1 and (Qs >> y) & 1 and u1 and (Qs >> u1[0]) & 1)
                    ok("L3.2 g(Q)>=10 => DU=1,k=2,sig=-1,u1 notin C,D_A=5+eps,g(Q)=10,kappa=1", good, key)
        if exhaustive:
            ok("L1.4 min slack over all cuts = maxflow(G-y) - 4s", best == val - 4 * s, (best, val))
            ok("L1.4 4-factor iff min slack >= 0", has4 == (best >= 0))
    return prof


def random_e4(a, rng):
    """balanced, both sides of size a, Delta <= 6, deficiency exactly dd <= 4 on each side"""
    for _ in range(200):
        dd = rng.randint(0, 4)
        dP, dQ = [6] * a, [6] * a
        for arr in (dP, dQ):
            r = dd
            while r > 0:
                j = rng.randrange(a)
                if arr[j] > 2:
                    arr[j] -= 1; r -= 1
        el = gen_bip_degseq(dP, dQ, rng)
        if el is not None:
            return Bip(a, a, el), dd
    return None, None


def check_e4(H):
    """Lemma 1.5: every violation (A in P = first side, C in Q) has k = 1, eps <= 1, and pieces are C1."""
    a = H.su
    P, Q = H.Umask, H.Wmask
    Pl, Ql = bits(P), bits(Q)
    nviol = 0
    for am in range(1 << a):
        A = mask_of(Pl[i] for i in range(a) if (am >> i) & 1)
        for cm in range(1 << a):
            C = mask_of(Ql[i] for i in range(a) if (cm >> i) & 1)
            k = popc(A) - popc(C)
            sl = H.e_between(A, Q & ~C) - 4 * k
            if sl >= 0:
                continue
            nviol += 1
            eps = H.defG(C) + H.e_between(P & ~A, C)
            DA = H.defG(A)
            ok("L1.5 violation: k=1, eps<=1, D_A>=3+eps", k == 1 and eps <= 1 and DA >= 3 + eps, (k, eps, DA))
            S1 = A | C
            S2 = (P & ~A) | (Q & ~C)
            ok("L1.5 piece1 side C in-piece deficiency = eps", H.defIn(C, S1) == eps)
            ok("L1.5 piece2 side P-A in-piece deficiency <= 1", H.defIn(P & ~A, S2) <= 1)
            ok("L1.5 sizes |C| + |P-A| = a-1", popc(C) + popc(P & ~A) == a - 1)
    return nviol


t0 = time.time()
allprof = {}
ninst = 0
for it in range(NINST):
    s = rng.choice([5, 6, 6, 7, 7, 8])
    DU = rng.choice([0, 1])
    wmin = rng.choice([2, 3, 4])
    G = random_c1(s, DU, wmin, rng)
    if G is None:
        continue
    ninst += 1
    check_sets(G, 300)
    pr = check_c1(G, DU, exhaustive=(s <= 6), ncut=3000)
    for kk, vv in pr.items():
        allprof[str(kk)] = allprof.get(str(kk), 0) + vv
ne4 = 0; nv4 = 0
for it in range(max(1, NINST // 4)):
    a = rng.choice([6, 6, 7])
    H, dd = random_e4(a, rng)
    if H is None:
        continue
    ne4 += 1
    check_sets(H, 200)
    nv4 += check_e4(H)
res = {"seed": seed, "c1_instances": ninst, "e4_instances": ne4, "e4_violations": nv4,
       "checks": cnt, "failures": len(fails), "violation_profile(k,sigma,gQ,DC)": allprof,
       "seconds": round(time.time() - t0, 1)}
print(json.dumps(res, indent=1))
json.dump(res, open(f"out_ident_{seed}.json", "w"), indent=1)
sys.exit(1 if fails else 0)
