"""Referee 2: identity checks and cross-validation of r2sub (own code).

Checks on random C1 instances (D_U in {0,1}):
  I1  Identity 1.1: D^S(S_U) = 6|S_U| - e(S), D^S(S_W) = 6|S_W| - e(S),
      g = 2 D^S(S_W) + 6 kappa = 2 D^S(S_U) - 6 kappa, and g = 2d + 6j.
  I2  Identity 1.2: g(A u B) + g(A n B) = g(A) + g(B) - 2 e(A - B, B - A).
  I3  Identity 1.3: g(S - v) = g(S) - 6 + 2 deg_S(v).
  I4  Lemma 1.4 slack formula in G - y: e(A, U - C) - 4k = 2k - D_A + eps, eps = D(C) + e(C, W - A).
  I5  Lemma 3.1: g(V - S) = 6 + 2 D_U + 2k + 2 sigma - 2 D(C), kappa(V - S) = k - 1.
  I6  Lemma 1.4 criterion: min slack over all cuts of G - y = maxflow - 4s (exhaustive, small s).
  X1  r2sub ming = Python brute force = flow-based min_g (small instances).
  X2  r2sub viol: violation count and min slack equal Python enumeration (small instances).
Exit code 1 on any mismatch. Writes out_identities.json.
"""
import json
import random
import subprocess
import sys
import os
from r2common import BG, random_C1, popcount, bits, mask_of, has_4factor_balanced, min_g_proper_flow

HERE = os.path.dirname(os.path.abspath(__file__))
SUB = os.path.join(HERE, "r2sub")


def to_input(G):
    lines = [f"{G.s} {G.r} {len(G.edges)}"] + [f"{u} {w}" for (u, w) in G.edges]
    return "\n".join(lines) + "\n"


def run_sub(G, *args):
    p = subprocess.run([SUB, *map(str, args)], input=to_input(G), capture_output=True, text=True,
                       timeout=240)
    if p.returncode != 0:
        raise RuntimeError(p.stderr)
    return p.stdout


def brute_min_g(G):
    best = 10 ** 9
    full = G.full()
    for S in range(1, full):
        if popcount(S) >= 2:
            gv = G.g(S)
            if gv < best:
                best = gv
    return best


def main(seed=2718, ninst=60):
    rng = random.Random(seed)
    stats = {k: 0 for k in ["I1", "I2", "I3", "I4", "I5", "I6", "X1", "X2"]}
    bad = []
    for it in range(ninst):
        s = rng.choice([5, 6, 7])
        DU = rng.choice([0, 1])
        maxd = rng.choice([1, 2, 3])
        G = random_C1(s, DU, maxd, rng)
        if G is None:
            continue
        n = G.n
        full = G.full()
        assert G.DU() == DU and G.DW() == 6 + DU
        # I1, I3 on random subsets
        for _ in range(300):
            S = rng.randrange(0, full + 1)
            Su, Sw = S & G.Umask, S & G.Wmask
            e = G.e_in(S)
            dU, dW = G.defic_in(Su, S), G.defic_in(Sw, S)
            kap = G.kappa(S)
            gv = G.g(S)
            ok = (dU == 6 * popcount(Su) - e and dW == 6 * popcount(Sw) - e and
                  gv == 2 * dW + 6 * kap and gv == 2 * dU - 6 * kap)
            j = abs(kap)
            d = dW if kap >= 0 else dU
            larger = dU if kap >= 0 else dW
            ok = ok and gv == 2 * d + 6 * j and larger == d + 6 * j
            stats["I1"] += 1
            if not ok:
                bad.append(("I1", it, S))
            for v in bits(S):
                dS = popcount(G.adj[v] & S)
                stats["I3"] += 1
                if G.g(S & ~(1 << v)) != gv - 6 + 2 * dS:
                    bad.append(("I3", it, S, v))
        # I2
        for _ in range(300):
            A = rng.randrange(0, full + 1)
            B = rng.randrange(0, full + 1)
            lhs = G.g(A | B) + G.g(A & B)
            rhs = G.g(A) + G.g(B) - 2 * G.e_between(A & ~B, B & ~A)
            stats["I2"] += 1
            if lhs != rhs:
                bad.append(("I2", it, A, B))
        # I4, I5, I6 at every port
        Vmask = full
        for y in G.ports():
            rest = Vmask & ~(1 << y)
            restbits = bits(rest)
            exhaustive = len(restbits) <= 13
            if exhaustive:
                cuts = range(1 << len(restbits))
            else:
                cuts = [rng.randrange(1 << len(restbits)) for _ in range(3000)]
            minsl = 10 ** 9
            for code in cuts:
                S = 0
                c = code
                idx = 0
                while c:
                    if c & 1:
                        S |= 1 << restbits[idx]
                    c >>= 1
                    idx += 1
                A = S & G.Wmask
                C = S & G.Umask
                k = popcount(A) - popcount(C)
                eAUC = G.e_between(A, G.Umask & ~C)
                sigma = eAUC - 4 * k
                DA = G.defic(A)
                DC = G.defic(C)
                eps = DC + G.e_between(C, G.Wmask & ~A)
                stats["I4"] += 1
                if sigma != 2 * k - DA + eps:
                    bad.append(("I4", it, y, S))
                Q = Vmask & ~S
                stats["I5"] += 1
                if G.g(Q) != 6 + 2 * DU + 2 * k + 2 * sigma - 2 * DC or G.kappa(Q) != k - 1:
                    bad.append(("I5", it, y, S))
                minsl = min(minsl, sigma)
            if exhaustive:
                val, target = has_4factor_balanced(G, G.W, G.U, removed=(y,))
                stats["I6"] += 1
                if minsl != val - target:
                    bad.append(("I6", it, y, minsl, val, target))
        # X1, X2 on small ones
        if n <= 13:
            out = run_sub(G, "ming").split()
            cm = int(out[1])
            bm = brute_min_g(G)
            fm = min_g_proper_flow(G)
            stats["X1"] += 1
            if not (cm == bm == fm):
                bad.append(("X1", it, cm, bm, fm))
            for y in G.ports()[:2]:
                out = run_sub(G, "viol", y)
                last = [l for l in out.splitlines() if l.startswith("viol ")][0].split()
                nv, ms = int(last[4]), int(last[6])
                # python count
                rest = Vmask & ~(1 << y)
                rb = bits(rest)
                pyn, pym = 0, 10 ** 9
                for code in range(1, 1 << len(rb)):
                    S = mask_of([rb[i] for i in range(len(rb)) if (code >> i) & 1])
                    A = S & G.Wmask
                    C = S & G.Umask
                    k = popcount(A) - popcount(C)
                    sigma = G.e_between(A, G.Umask & ~C) - 4 * k
                    pym = min(pym, sigma)
                    if sigma < 0:
                        pyn += 1
                stats["X2"] += 1
                if nv != pyn or ms != pym:
                    bad.append(("X2", it, y, nv, pyn, ms, pym))
    res = {"seed": seed, "stats": stats, "mismatches": bad[:50], "n_mismatch": len(bad)}
    with open(os.path.join(HERE, "out_identities.json"), "w") as f:
        json.dump(res, f, indent=1)
    print(json.dumps({"stats": stats, "n_mismatch": len(bad)}))
    return 1 if bad else 0


if __name__ == "__main__":
    a = sys.argv[1:]
    sys.exit(main(int(a[0]) if a else 2718, int(a[1]) if len(a) > 1 else 60))
