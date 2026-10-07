"""Minimality-free core (Lemma 4.4) and the petal lattice (Lemmas 4.1, 4.2) on built sub-case
instances, with my own builder and a full enumeration of the family P over all subsets.

Build: U = C' u U2 (|C'| = c, |U2| = t, u1 in U2), W = A u W2 (|A| = c+2, |W2| = t-1, y in W2).
C'-A: every C'-vertex has 6 neighbors in A (eps = 0), or one C'-vertex c* has 5 in A and one in
W2 (eps = 1). Seven T-edges A-U2 with <= 3 per A-vertex, <= 3 per U2-vertex, <= 2 at u1.
A-deficiency 5 + eps. U2-W2 fills U2 to degree 6 (u1 to 5). Then (A, C') is a violation of G - y
with slack -1, so y is a bad port by construction.

For each built instance that is exactly sparse (min g over proper sets with >= 2 vertices is 10,
by subset DP), enumerate P = {Q != V, |Q| >= 2, g(Q) = 10, kappa(Q) = 1, u1 in Q} and check:
 (E) Q in P contains a port y  <=>  V - Q is a violation of G - y (so petals = members of P);
 (L41) |Q| >= 3, D^Q(Q_W) = 2, deg_Q(u1) >= 3;
 (L42) P closed under intersection and union, over all pairs;
 (L44) union of P in P, and the bad ports' total deficiency <= 2; D_U = 0 built variants excluded.
Usage: sparse_core.py seed budget_seconds"""
import sys, random, json, time, itertools
from ref_common import Bip, has_4factor_balanced, random_bip_with_degrees

seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
budget = float(sys.argv[2]) if len(sys.argv) > 2 else 200
rng = random.Random(seed)
t0 = time.time()

def popcount(x):
    return bin(x).count("1")

def build(c, t, eps, rng, nest=False):
    s = c + t
    Cp = list(range(c)); U2 = list(range(c, s)); u1 = U2[0]
    A = list(range(s, s + c + 2)); W2 = list(range(s + c + 2, 2 * s + 1)); y = W2[0]
    edges = set()
    # C'-A
    cstar = Cp[0] if eps == 1 else None
    for x in Cp:
        need = 5 if x == cstar else 6
        for a in rng.sample(A, need):
            edges.add((x, a))
    if eps == 1:
        edges.add((cstar, rng.choice(W2[1:] if len(W2) > 1 else W2)))  # avoid y so y's degree stays free
    # T-edges: 7, caps 3 per A-vertex, 3 per U2-vertex, 2 at u1
    xnest = U2[1] if nest else None
    for _ in range(200):
        T = set(); capA = {a: 3 for a in A}; capU = {u: (2 if u == u1 else 3) for u in U2}
        ok = True
        if nest:
            for a in rng.sample(A, 3):
                T.add((xnest, a)); capA[a] -= 1
            capU[xnest] = 0
        for _ in range(7 - (3 if nest else 0)):
            cands = [(a, u) for a in A for u in U2 if capA[a] > 0 and capU[u] > 0 and (u, a) not in T]
            if not cands:
                ok = False; break
            a, u = rng.choice(cands); T.add((u, a)); capA[a] -= 1; capU[u] -= 1
        if ok:
            break
    else:
        return None
    # A degrees: e(a, C') + e(a, U2) must be <= 6 and total deficiency 5 + eps (automatic by counts)
    degA = {a: 0 for a in A}
    for (x, a) in edges:
        if a in degA: degA[a] += 1
    for (u, a) in T:
        degA[a] += 1
    if max(degA.values()) > 6:
        return None
    edges |= T
    # U2-W2: u needs 6 - [u1] - r(u) neighbors in W2; W2 degree caps: y <= 5, others <= 6, minus eps edge
    r = {u: 0 for u in U2}
    for (u, a) in T: r[u] += 1
    need = {u: 6 - (1 if u == u1 else 0) - r[u] for u in U2}
    capW = {w: 6 for w in W2}; capW[y] = 5
    for (x, w) in edges:
        if w in capW: capW[w] -= 1
    total = sum(need.values())
    forced = set()
    if nest:
        # y gets degree 4 (deficiency 2), with x_nest adjacent to y
        capW[y] = 4
        edges.add((xnest, y)); forced.add((xnest, y)); need[xnest] -= 1; capW[y] -= 1; total -= 1
    # choose W2 degree sequence summing to total within caps (random)
    for _ in range(200):
        degW2 = {w: 0 for w in W2}
        slots = [w for w in W2 for _ in range(capW[w])]
        if len(slots) < total:
            return None
        rng.shuffle(slots)
        for w in slots[:total]:
            degW2[w] += 1
        H = random_bip_with_degrees(len(U2), len(W2), [need[u] for u in U2], [degW2[w] for w in W2], rng, tries=20)
        if H is not None:
            break
    else:
        return None
    for (i, j) in H.edges:
        e_ = (U2[i], W2[j - len(U2)])
        if e_ in forced:
            return None
        edges.add(e_)
    B = Bip(s, s + 1, sorted(edges))
    if not B.is_C1() or B.D(B.U) != 1:
        return None
    return B, dict(c=c, t=t, eps=eps, u1=u1, y=y, A=A, Cp=Cp)

def subset_dp(B):
    n = B.n
    adjb = [sum(1 << w for w in B.adj[v]) for v in range(n)]
    e = bytearray(1 << n) if False else [0] * (1 << n)
    for S in range(1, 1 << n):
        low = S & (-S); v = low.bit_length() - 1; rest = S ^ low
        e[S] = e[rest] + popcount(adjb[v] & rest)
    return e

results = []
nbuilt = 0; nsparse = 0; fails = []
while time.time() - t0 < budget:
    c, t = rng.choice([(4, 6), (4, 7), (5, 6)]); eps = rng.choice([0, 0, 1])
    out = build(c, t, eps, rng, nest=(eps == 0 and rng.random() < 0.6))
    if out is None:
        continue
    B, info = out
    nbuilt += 1
    n, s = B.n, B.s
    u1, y = info["u1"], info["y"]
    # sanity: (A, C') violation of G - y with slack -1
    A, Cp = info["A"], info["Cp"]
    k = len(A) - len(Cp)
    sigma = sum(1 for a in A for u in B.adj[a] if u not in Cp) - 4 * k
    assert sigma == -1, sigma
    e = subset_dp(B)
    full = (1 << n) - 1
    Ub = (1 << s) - 1
    ming = min(6 * popcount(S) - 2 * e[S] for S in range(1, full) if popcount(S) >= 2)
    rec = dict(c=c, t=t, eps=eps, s=s, n=n, g6=B.graph6(), min_g=ming)
    if ming < 10:
        results.append(rec); continue
    nsparse += 1
    P = [S for S in range(1, full) if popcount(S) >= 2 and 6 * popcount(S) - 2 * e[S] == 10
         and (popcount(S & Ub) - popcount(S >> s)) == 1 and (S >> u1) & 1]
    Pset = set(P)
    ports = [w for w in B.W if B.deg(w) <= 5]
    badports = [w for w in ports if not has_4factor_balanced([x for x in B.W if x != w], list(B.U), B.adj)]
    rec.update(bad_ports=len(badports), bad_def=sum(6 - B.deg(w) for w in badports), P_size=len(P), ports=len(ports))
    # (E): members of P containing a W-vertex w correspond to violations of G - w
    for Q in P:
        for w in B.W:
            if (Q >> w) & 1:
                S = full ^ Q
                Ab = [x for x in B.W if (S >> x) & 1]; Cb = [u for u in B.U if (S >> u) & 1]
                kk = len(Ab) - len(Cb)
                sg = sum(1 for a in Ab for u in B.adj[a] if u not in Cb) - 4 * kk
                nof = not has_4factor_balanced([x for x in B.W if x != w], list(B.U), B.adj)
                if not (sg < 0 and nof and (w not in ports or w in badports)):
                    fails.append(("E", rec["g6"], Q, w))
    # (L41)
    for Q in P:
        Qset = {v for v in range(n) if (Q >> v) & 1}
        QW = [v for v in Qset if v >= s]
        if not (len(Qset) >= 3 and B.D_in(Qset, QW) == 2 and B.D(QW) <= 2 and B.deg_in(Qset, u1) >= 3):
            fails.append(("L41", rec["g6"], Q))
    # (L42)
    for Q, Qp in itertools.combinations(P, 2):
        if (Q & Qp) not in Pset or (Q | Qp) not in Pset:
            fails.append(("L42", rec["g6"], Q, Qp))
    # (L44)
    if P:
        Uall = 0
        for Q in P: Uall |= Q
        if Uall not in Pset:
            fails.append(("L44-union", rec["g6"]))
        covered = [w for w in badports if (Uall >> w) & 1]
        if len(covered) != len(badports) or rec["bad_def"] > 2:
            fails.append(("L44-def", rec["g6"], badports))
    else:
        if badports:
            fails.append(("L44-nopetal", rec["g6"]))
    incomparable = sum(1 for Q, Qp in itertools.combinations(P, 2) if (Q & Qp) not in (Q, Qp))
    rec["incomparable_pairs"] = incomparable
    distinct_petals = {}
    for Q in P:
        for w in badports:
            if (Q >> w) & 1:
                distinct_petals[w] = distinct_petals.get(w, 0) + 1
    rec["petals_per_bad_port"] = distinct_petals
    results.append(rec)

summary = dict(seed=seed, built=nbuilt, sparse=nsparse, fails=len(fails), first_fails=[str(f)[:160] for f in fails[:5]],
               seconds=round(time.time() - t0, 1), results=results)
json.dump(summary, open(f"out_sparse_core_{seed}.json", "w"), indent=1)
print(json.dumps({k: v for k, v in summary.items() if k != "results"}, indent=1))
for r in results:
    print({k: r[k] for k in r if k != "g6"})
print("RESULT:", "PASS" if not fails else "FAIL")
sys.exit(0 if not fails else 1)
