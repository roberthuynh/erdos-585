"""Built C1 instances with an actual sub-case violation (lane M3, own builder).

Construction: U = C' (c vertices) + U - C' (t vertices, u1 the last, degree 5); W = A (c + 2) +
W - A (t - 1, containing the port y). P2 = G[A u C'] and P1 = G[(U - C') u (W - A)] are random simple
bipartite graphs with the degrees forced by the sub-case, glued by 7 edges T between A and U - C'
(and, if eps = 1, one edge f from c* in C' to w' in W - A). Variants: eps = 1 (d0 = 5, A has six
degree-5 vertices); eps = 0 with deg y = 4 ('y4'); eps = 0 with y and a second port y2 of degree 5 in
W - A ('y55').

Checked on every instance (the instances contain quartic subgraphs; these are checks of counts and
identities, not of minimality):
 S1  G is C1 with D_U = 1, D_W = 7; slack of (A, C') in G - y is -1 (direct count); maxflow <= 4s - 1
 S2  e(A, U - C') = 7, e(C', W - A) = eps; g(P1) = 10, g(P2) = 12 + 2 eps, kappa(P1) = 1, u1 in P1,
     in-P1 deficiencies 2 (W - A) and 8 (U - C')
 S3  trace identity x - x' = 4(|V(H) n A| - |V(H) n C'|) on SAT witnesses H for every boundary subset
 S4  gluing: G has quartic H with H n boundary = tau  <=>  P1 and P2 both realize tau (every tau),
     and for tau empty: G has one avoiding the boundary <=> P1 or P2 has one
 S5  P2 + beta: unsigned count 3n - 2 - eps; signed list (eps = 1) has 6c + 7 = 3n - 2 elements;
     a zero-sum (mod 4) sublist exists (SAT), and every solution read as a trace realizes it in P2
 S6  P1 + alpha_tau for distinct-endpoint 4-traces: simple, balanced (t, t), deficiencies (4, 4), Delta <= 6
 S7  eps = 1: P1 + uw' for (1,1)-traces {e, f} with u not adjacent to w': simple C1(t - 1), W - A
     deficiency 1, Delta <= 6
 S8  P1 + a (a in A): deficiency 8 - s(a) on both sides; P1 - x (x in U - C'): 8 - def(x) - r(x) on both
 S9  P1 + alpha (all 7 T-ends; eps = 1 also signed f-element): element count vs threshold
 S10 petal data at y and at every other bad port y': for a min-cut violation S of G - y', Q = V - S has
     g(Q) = 8 + 2k + 2 sigma - 2[u1 in C]; and whenever g(Q) >= 10: k = 2, sigma = -1, u1 not in C,
     kappa(Q) = 1 (Lemma 3.2); for pairs of such petals the Lemma 4.1 / 4.2 inequalities
 S11 sparsity (exact, flow-based) on a subset of instances; for sparse ones the core lemma (bad ports
     in one member of P, total deficiency <= 2)
"""
import itertools
import json
import random
import sys
import time

from c1common import (BG, random_bipartite_degrees, quartic_sat, has_4factor, max_flow_value,
                      min_g_proper, min_cut_violation, popcount, members)

SEED = 990011
rng = random.Random(SEED)
t0 = time.time()
fails = []
stats = {}


def bump(k, v=1):
    stats[k] = stats.get(k, 0) + v


def check(cond, msg):
    if not cond:
        fails.append(msg)


def split_sum(total, nparts, cap, rng):
    """random list of nparts nonnegative ints <= cap summing to total"""
    for _ in range(1000):
        parts = [0] * nparts
        for _ in range(total):
            i = rng.randrange(nparts)
            parts[i] += 1
        if max(parts) <= cap:
            return parts
    return None


def build(c, t, eps, variant, rng, capT=3):
    s = c + t
    Cp = list(range(c))                    # C'
    Ur = list(range(c, c + t))             # U - C'
    u1 = c + t - 1
    A = list(range(c + 2))                 # W indices 0..c+1
    Wr = list(range(c + 2, c + 2 + t - 1)) # W - A
    y = Wr[0]
    degU = {u: 6 for u in range(s)}
    degU[u1] = 5
    degW = {w: 6 for w in range(s + 1)}
    if eps == 1:
        for a in rng.sample(A, 6):
            degW[a] = 5
        degW[y] = 5
    elif variant == "y4":
        degW[y] = 4
        if rng.random() < 0.5:
            for a in rng.sample(A, 5):
                degW[a] = 5
        else:
            a4 = rng.choice(A)
            degW[a4] = 4
            for a in rng.sample([x for x in A if x != a4], 3):
                degW[a] = 5
    else:  # y55
        degW[y] = 5
        degW[Wr[1]] = 5
        for a in rng.sample(A, 5):
            degW[a] = 5
    # T-edge distribution
    r = split_sum(7, t, capT, rng)
    if r is None:
        return None
    r = dict(zip(Ur, r))
    if r[u1] > 2 and capT <= 3:
        return None
    sa = split_sum(7, c + 2, capT, rng)
    if sa is None:
        return None
    sa = dict(zip(A, sa))
    cstar, wprime = (None, None)
    if eps == 1:
        cstar = rng.choice(Cp)
        wprime = rng.choice(Wr)
    # P2: U-side C', W-side A
    duP2 = [6 - (1 if (eps == 1 and u == cstar) else 0) for u in Cp]
    dwP2 = [degW[a] - sa[a] for a in A]
    if min(dwP2) < 0 or max(dwP2) > c:
        return None
    P2 = random_bipartite_degrees(duP2, dwP2, rng)
    if P2 is None:
        return None
    # P1: U-side U - C', W-side W - A
    duP1 = [degU[u] - r[u] for u in Ur]
    dwP1 = [degW[w] - (1 if w == wprime else 0) for w in Wr]
    if min(duP1) < 0 or max(duP1) > t - 1 or max(dwP1) > t:
        return None
    P1 = random_bipartite_degrees(duP1, dwP1, rng)
    if P1 is None:
        return None
    edges = []
    for (i, j) in P2.edges:
        edges.append((Cp[i], A[j]))
    for (i, j) in P1.edges:
        edges.append((Ur[i], Wr[j]))
    # T edges: match stubs
    for _ in range(200):
        ast = [a for a in A for _ in range(sa[a])]
        ust = [u for u in Ur for _ in range(r[u])]
        rng.shuffle(ust)
        T = list(zip(ust, ast))
        if len(set(T)) == 7:
            break
    else:
        return None
    edges += T
    f = None
    if eps == 1:
        f = (cstar, wprime)
        edges.append(f)
    G = BG(s, s + 1, edges)
    info = dict(c=c, t=t, eps=eps, variant=variant, s=s, Cp=Cp, Ur=Ur, u1=u1, A=[s + a for a in A],
                Wr=[s + w for w in Wr], y=s + y, T=[(u, s + a) for (u, a) in T],
                f=None if f is None else (f[0], s + f[1]), r=r, sa={s + a: sa[a] for a in A})
    return G, info


def realize_sat(n, edges, forced):
    return quartic_sat(n, edges, forced=forced, require_nonempty=False)


instances = []
plan = []
for eps in (0, 1):
    variants = ["y4", "y55"] if eps == 0 else ["e1"]
    for variant in variants:
        for c in (4, 5, 6):
            for t in (7, 8, 9):
                plan.append((c, t, eps, variant))
for (c, t, eps, variant) in plan:
    got = 0
    for attempt in range(60):
        out = build(c, t, eps, variant, rng)
        if out is None:
            continue
        instances.append(out)
        got += 1
        if got >= 2:
            break

nsparse_target = int(sys.argv[1]) if len(sys.argv) > 1 else 6
CH = int(sys.argv[2]) if len(sys.argv) > 2 else 0
NCH = int(sys.argv[3]) if len(sys.argv) > 3 else 1
for idx, (G, I) in enumerate(instances):
    if idx % NCH != CH:
        continue
    bump("instances")
    s, c, t, eps = I["s"], I["c"], I["t"], I["eps"]
    y, u1 = I["y"], I["u1"]
    full = G.full
    Am = sum(1 << a for a in I["A"])
    Cm = sum(1 << u for u in I["Cp"])
    P2m = Am | Cm
    P1m = full ^ P2m
    # S1
    check(G.max_deg() <= 6, "S1 maxdeg")
    check(sum(6 - G.deg[u] for u in G.U) == 1 and G.deg[u1] == 5, "S1 D_U")
    check(sum(6 - G.deg[w] for w in G.W) == 7, "S1 D_W")
    eAUC = sum(1 for a in I["A"] for x in G.adj[a] if not (Cm >> x) & 1)
    slack = eAUC - 4 * (len(I["A"]) - len(I["Cp"]))
    check(slack == -1, f"S1 slack {slack}")
    mf = max_flow_value(G, delete=[y])
    check(mf <= 4 * s - 1, "S1 maxflow")
    bump("maxflow_4s-1" if mf == 4 * s - 1 else "maxflow_below")
    # S2
    check(eAUC == 7, "S2 e(A,U-C')")
    check(G.e_between(Cm, G.Wmask & ~Am) == eps, "S2 e(C',W-A)")
    check(G.g(P1m) == 10 and G.g(P2m) == 12 + 2 * eps, "S2 g")
    check(G.kappa(P1m) == 1 and (P1m >> u1) & 1, "S2 kappa/u1")
    check(G.Din(P1m, P1m & G.Wmask) == 2 and G.Din(P1m, P1m & G.Umask) == 8, "S2 in-P1 deficiencies")
    # boundary edges
    bd = list(I["T"]) + ([I["f"]] if eps == 1 else [])
    bdset = set(bd)
    inner = [e for e in G.gedges if e not in bdset]
    allE = inner + bd
    nb = len(bd)
    P1E = [e for e in G.gedges if (P1m >> e[0]) & 1 and (P1m >> e[1]) & 1]
    P2E = [e for e in G.gedges if (P2m >> e[0]) & 1 and (P2m >> e[1]) & 1]
    # S3/S4 over every boundary subset
    if idx % 3 == 0:
        for bits in range(1 << nb):
            tau = [bd[i] for i in range(nb) if (bits >> i) & 1]
            forced = {}
            for (a, b) in tau:
                forced[a] = forced.get(a, 0) + 1
                forced[b] = forced.get(b, 0) + 1
            # G with H n boundary = tau: forbid other boundary edges, force tau
            nin = len(inner)
            # encode: edges = inner, forced degrees from tau
            if not tau:
                F = quartic_sat(G.n, inner)
            else:
                F = realize_sat(G.n, inner, forced)
            existsG = F is not None
            if existsG:
                H = [inner[i] for i in F] + tau
                VH = set(v for e in H for v in e)
                x = sum(1 for e in tau if e in set(I["T"]))
                xp = len(tau) - x
                lhs = x - xp
                rhs = 4 * (len(VH & set(I["A"])) - len(VH & set(I["Cp"])))
                check(lhs == rhs, "S3 trace identity")
                bump("S3_witnesses")
                bump(f"S3_trace_type_({x},{xp})")
            if tau:
                f1 = {v: k for v, k in forced.items() if (P1m >> v) & 1}
                f2 = {v: k for v, k in forced.items() if (P2m >> v) & 1}
                r1 = realize_sat(G.n, P1E, f1) is not None
                r2 = realize_sat(G.n, P2E, f2) is not None
                check(existsG == (r1 and r2), "S4 gluing")
            else:
                h1 = quartic_sat(G.n, P1E) is not None
                h2 = quartic_sat(G.n, P2E) is not None
                check(existsG == (h1 or h2), "S4 gluing empty")
            bump("S4_traces")
    # S5: P2 + beta
    n2 = 2 * c + 2 + 1
    unsigned = len(P2E) + 7
    check(unsigned == 3 * n2 - 2 - eps, "S5 unsigned count")
    if eps == 1:
        signed = len(P2E) + 7 + 1
        check(signed == 6 * c + 7 == 3 * n2 - 2, "S5 signed count")
        # SAT: zero-sum mod 4. Vertices: P2 vertices + beta (index G.n). Elements: P2 edges,
        # T-type (a, beta), f-type (cstar, beta). At A, C' vertices: degree in {0,4}. At beta:
        # x' = 0 -> x in {0,4}; x' = 1 -> x in {1,5}.
        from pysat.solvers import Cadical153
        from c1common import _atleast_direct, _atmost_direct
        beta = G.n
        els = list(P2E) + [(a, beta) for (u, a) in I["T"]] + [(I["f"][0], beta)]
        ne = len(els)
        inc = {}
        for i, (p, q) in enumerate(els):
            inc.setdefault(p, []).append(i + 1)
            inc.setdefault(q, []).append(i + 1)
        cls = []
        zv = {}
        nxt = ne + 1
        for v, L in inc.items():
            if v == beta:
                continue
            zv[v] = nxt; nxt += 1
            for l in L:
                cls.append([-l, zv[v]])
            cls += _atleast_direct(L, 4, guard=zv[v])
            cls += _atmost_direct(L, 4)
        Tl = [i + 1 for i in range(len(P2E), len(P2E) + 7)]
        fl = ne
        # beta: x - x' in {0, 4} with x' in {0,1}: allowed x given x'
        for xx in range(8):
            for xp in (0, 1):
                if (xx - xp) % 4 == 0:
                    continue
                # forbid exactly xx of Tl true together with fl == xp: encode via cardinality of Tl
                # forbidding "exactly xx": for every subset R of size xx: not(all R true and others
                # false and f == xp)
                for R in itertools.combinations(Tl, xx):
                    Rs = set(R)
                    cl = [-l for l in R] + [l for l in Tl if l not in Rs]
                    cl.append(-fl if xp == 1 else fl)
                    cls.append(cl)
        cls.append(list(range(1, ne + 1)))
        with Cadical153(bootstrap_with=cls) as S:
            ok = S.solve()
            check(ok, "S5 Olson zero-sum exists")
            bump("S5_signed_solved")
            if ok:
                model = set(l for l in S.get_model() if l > 0)
                chosen = [els[i] for i in range(ne) if (i + 1) in model]
                xx = sum(1 for l in Tl if l in model)
                xp = 1 if fl in model else 0
                bump(f"S5_signed_solution_({xx},{xp})")
                # read as trace: F = chosen P2 edges, tau = chosen T + f
                Fd = {}
                for (p, q) in chosen:
                    if q == beta:
                        continue
                    Fd[p] = Fd.get(p, 0) + 1; Fd[q] = Fd.get(q, 0) + 1
                taud = {}
                for i in range(len(P2E), ne):
                    if (i + 1) in model:
                        p = els[i][0]
                        taud[p] = taud.get(p, 0) + 1
                for v in members(P2m):
                    check(Fd.get(v, 0) + taud.get(v, 0) in (0, 4), "S5 realization")
        # also force beta used (x + x' >= 1): record whether P2 realizes a nonzero trace this way
        cls2 = cls + [Tl + [fl]]
        with Cadical153(bootstrap_with=cls2) as S:
            bump("S5_beta_used_SAT" if S.solve() else "S5_beta_used_UNSAT")
    # S6: P1 + alpha_tau for distinct-endpoint 4-traces
    Tlist = I["T"]
    for tau in itertools.combinations(range(7), 4):
        ends = [Tlist[i][0] for i in tau]
        if len(set(ends)) < 4:
            continue
        # P1 + alpha: alpha on W side joined to the 4 endpoints
        degs = {}
        for (a, b) in P1E:
            degs[a] = degs.get(a, 0) + 1; degs[b] = degs.get(b, 0) + 1
        for u in ends:
            degs[u] = degs.get(u, 0) + 1
        Wside = [w for w in members(P1m & G.Wmask)] + ["alpha"]
        Uside = [u for u in members(P1m & G.Umask)]
        degs["alpha"] = 4
        dW = sum(6 - degs.get(w, 0) for w in Wside)
        dU = sum(6 - degs.get(u, 0) for u in Uside)
        check(len(Wside) == len(Uside) == t and dW == 4 and dU == 4 and max(degs.values()) <= 6,
              "S6 P1 + alpha_tau in E4")
        bump("S6_checked")
    # S7
    if eps == 1:
        wq = I["f"][1]
        for (u, a) in Tlist:
            if wq in G.adj[u]:
                bump("S7_adjacent_skipped")
                continue
            degs = {}
            for (p, q) in P1E + [(u, wq)]:
                degs[p] = degs.get(p, 0) + 1; degs[q] = degs.get(q, 0) + 1
            dW = sum(6 - degs.get(w, 0) for w in members(P1m & G.Wmask))
            check(dW == 1 and max(degs.values()) <= 6, "S7 P1 + uw' C1")
            bump("S7_checked")
    # S8
    for a in I["A"]:
        sa_ = I["sa"][a]
        m2 = P1m | (1 << a)
        dW = G.Din(m2, m2 & G.Wmask); dU = G.Din(m2, m2 & G.Umask)
        check(dW == dU == 8 - sa_, "S8 P1 + a")
        bump("S8_plus_a")
    for xv in I["Ur"]:
        rx = I["r"][xv]
        m2 = P1m ^ (1 << xv)
        dW = G.Din(m2, m2 & G.Wmask); dU = G.Din(m2, m2 & G.Umask)
        check(dW == dU == 8 - (6 - G.deg[xv]) - rx, "S8 P1 - x")
        bump("S8_minus_x")
    # S9
    n1 = 2 * t
    cnt = len(P1E) + 7 + (1 if eps == 1 else 0)
    thr = 3 * (n1 - 1) + 1
    check(cnt - thr == 1 + eps, f"S9 P1 + alpha count {cnt} thr {thr}")
    # S10: petals at every bad port
    ports = [w for w in G.W if G.deg[w] <= 5]
    bad = [w for w in ports if not has_4factor(G, delete=[w])]
    check(y in bad, "S10 y is bad")
    bump("bad_ports_total", len(bad))
    petals = []
    for w in bad:
        Sm, sig = min_cut_violation(G, w)
        Q = full ^ Sm
        k = popcount(Sm & G.Wmask) - popcount(Sm & G.Umask)
        u1C = (Sm >> u1) & 1
        check(G.g(Q) == 8 + 2 * k + 2 * sig - 2 * u1C, "S10 g(Q) identity")
        if G.g(Q) >= 10:
            check(k == 2 and sig == -1 and not u1C and G.kappa(Q) == 1, "S10 forced data")
            petals.append((w, Q))
            bump("S10_tight_petals")
        else:
            bump("S10_petal_g_le_8")
    for i in range(len(petals)):
        Qi = petals[i][1]
        if G.g(Qi ^ (1 << u1)) >= 10:
            check(G.deg_in(u1, Qi) >= 3, "S10 Lemma 4.1")
        for j in range(i + 1, len(petals)):
            Qj = petals[j][1]
            check((Qi | Qj) != full, "S10 union != V")
            if (Qi & Qj) != (1 << u1):
                check(G.g(Qi & Qj) + G.g(Qi | Qj) <= 20, "S10 submod")
                if G.g(Qi & Qj) >= 10 and G.g(Qi | Qj) >= 10:
                    check(G.kappa(Qi & Qj) == 1 == G.kappa(Qi | Qj), "S10 cap/cup kappa")
            bump("S10_pairs")
    # S11: exact sparsity on some instances
    if stats.get("S11_tested", 0) < nsparse_target:
        mg, wit = min_g_proper(G)
        bump("S11_tested")
        bump(f"S11_min_g_{mg}")
        if mg >= 10:
            bump("S11_sparse")
            Ustar = 0
            for (_, Q) in petals:
                Ustar |= Q
            bdef = sum(6 - G.deg[w] for w in bad)
            check(len(petals) == len(bad), "S11 every bad port has a tight petal")
            check(Ustar != full and G.g(Ustar) == 10 and G.kappa(Ustar) == 1, "S11 union in P")
            check(bdef <= 2, "S11 bad deficiency <= 2")
        stats["S11_examples"] = stats.get("S11_examples", []) + [
            {"c": c, "t": t, "eps": eps, "variant": I["variant"], "min_g": mg,
             "witness_size": popcount(wit), "bad_ports": len(bad),
             "bad_def": sum(6 - G.deg[w] for w in bad)}]
    print(f"instance {idx} c={c} t={t} eps={eps} {I['variant']} bad={len(bad)} t={time.time()-t0:.1f}s",
          flush=True)

stats["seconds"] = round(time.time() - t0, 1)
stats["n_failures"] = len(fails)
stats["failures"] = fails[:20]
stats["RESULT"] = "PASS" if not fails else "FAIL"
with open(f"out_subcase_{CH}of{NCH}.json", "w") as fh:
    json.dump(stats, fh, indent=1)
print(json.dumps({k: v for k, v in stats.items() if k != "S11_examples"}, indent=1))
sys.exit(0 if not fails else 1)
