"""Chain instances with two planted nested petals, and exact enumeration of the family P via min cuts.

Blocks: S2 = A2 (c2+2 W) + C2 (c2 U); X = X_W (p) + X_U (p); Q1 = Q1_U (t U, contains u1) + Q1_W (t-1 W,
contains y). T2 = E(A2, X_U u Q1_U) has 7 edges, T1 = E(A2 u X_W, Q1_U) has 7 edges, tau = e(A2, X_U) =
e(X_W, Q1_U). Variant 0: eps1 = eps2 = 0. Variant 1: one edge X_U-Q1_W (eps1 = 1), one X_W vertex of
degree 5. Then V - S2 and Q1 both have g = 10, kappa = 1 and contain u1 (checked, not assumed).

P enumeration (exact in a sparse D_U = 1 instance, see note N2 of C1-REVIEW.md): for every w in W with
maxflow(G - w) = 4s - 1, all min cuts of the 4-factor network of G - w (closures of the residual graph),
complements filtered to g = 10, kappa = 1, u1 in Q. If some maxflow(G - w) <= 4s - 2 in a sparse instance,
that is recorded as a failure (it contradicts the Lemma 3.2 arithmetic).
Usage: rc_chain.py SEED BUDGET BRUTE_NMAX"""
import sys, json, random, time
from rc_common import *
from rc_build import spread
import rc_lattice as L


def build_chain(c2, p, t, variant, rng):
    nA2 = c2 + 2
    s = c2 + p + t
    lam = 1 if variant == 1 else 0
    lo = max(0, 6 * p - p * p - lam)
    if lo > 7:
        return None
    tau = rng.randint(lo, 7)
    defA2 = spread(5, nA2, 2, rng)
    s2 = spread(7, nA2, 3, rng)
    if defA2 is None or s2 is None:
        return None
    # Q1_U receive: rX (from X_W, sum tau), rA (from A2, sum 7 - tau); u1 last, rX+rA <= 3, <= 2 at u1
    rX = spread(tau, t, 3, rng)
    rA = spread(7 - tau, t, 3, rng)
    if rX is None or rA is None:
        return None
    if any(rX[i] + rA[i] > 3 for i in range(t)) or rX[-1] + rA[-1] > 2:
        return None
    defQ1U = [0] * (t - 1) + [1]
    # X_U: e(x, A2) sums to tau, each <= 3; X_W: out to Q1_U sums to tau, each <= 3
    xA = spread(tau, p, 3, rng)
    xout = spread(tau, p, 3, rng)
    if xA is None or xout is None:
        return None
    defXW = [0] * p
    x0 = w0 = None
    if variant == 1:
        defXW[rng.randrange(p)] = 1
        x0 = rng.randrange(p)
    nQ1W = t - 1
    if variant == 1:
        defQ1W = [1] + [0] * (nQ1W - 1)
        w0 = rng.randrange(nQ1W)
    else:
        defQ1W = ([1, 1] if rng.random() < 0.5 else [2, 0]) + [0] * (nQ1W - 2)
    # T2 edges: A2 side s2 (sum 7); other side = X_U (xA) followed by Q1_U (rA)
    eT2 = gen_bip_degseq(s2, xA + rA, rng)
    eT1 = gen_bip_degseq(xout, rX, rng)  # X_W side vs Q1_U side
    dC2 = [6] * c2
    dA2 = [6 - defA2[i] - s2[i] for i in range(nA2)]
    if min(dA2) < 0 or max(dA2) > c2:
        return None
    e22 = gen_bip_degseq(dC2, dA2, rng)
    dXU = [6 - xA[i] - (1 if (variant == 1 and i == x0) else 0) for i in range(p)]
    dXW = [6 - defXW[i] - xout[i] for i in range(p)]
    if max(dXU) > p or max(dXW) > p or min(dXU) < 0 or min(dXW) < 0:
        return None
    eXX = gen_bip_degseq(dXU, dXW, rng)
    dQU = [6 - defQ1U[i] - rX[i] - rA[i] for i in range(t)]
    dQW = [6 - defQ1W[i] - (1 if (variant == 1 and i == w0) else 0) for i in range(nQ1W)]
    if max(dQU) > nQ1W or min(dQU) < 0 or max(dQW) > t:
        return None
    eQQ = gen_bip_degseq(dQU, dQW, rng)
    if None in (eT2, eT1, e22, eXX, eQQ):
        return None
    # labels. U: C2 [0,c2), X_U [c2, c2+p), Q1_U [c2+p, s) (u1 = s-1). W: A2, X_W, Q1_W (y first).
    C2g = list(range(c2)); XUg = list(range(c2, c2 + p)); QUg = list(range(c2 + p, s))
    A2g = list(range(s, s + nA2)); XWg = list(range(s + nA2, s + nA2 + p))
    QWg = list(range(s + nA2 + p, 2 * s + 1))
    assert len(QWg) == nQ1W
    E = []
    for (i, j) in eT2:  # i: A2 side index, j - nA2: index into X_U + Q1_U
        jj = j - nA2
        E.append(((XUg + QUg)[jj], A2g[i]))
    for (i, j) in eT1:  # i: X_W side, j - p: Q1_U side
        E.append((QUg[j - p], XWg[i]))
    for (i, j) in e22:
        E.append((C2g[i], A2g[j - c2]))
    for (i, j) in eXX:
        E.append((XUg[i], XWg[j - p]))
    for (i, j) in eQQ:
        E.append((QUg[i], QWg[j - t]))
    if variant == 1:
        E.append((XUg[x0], QWg[w0]))
    if len(set(E)) != len(E):
        return None
    G = Bip(s, s + 1, E)
    S2 = mask_of(A2g + C2g)
    S1 = S2 | mask_of(XWg + XUg)
    info = {"c2": c2, "p": p, "t": t, "variant": variant, "tau": tau, "S1": S1, "S2": S2,
            "y": QWg[0], "u1": QUg[-1]}
    return G, info


def mincut_sides(G, w, cap=20000):
    """all min-cut source sides (A, C) of the 4-factor network of G - w; returns (value, list, truncated)"""
    P = G.Wmask & ~(1 << w)
    Pl, Ul = bits(P), bits(G.Umask)
    nodes = Pl + Ul
    idx = {v: i + 1 for i, v in enumerate(nodes)}
    N = len(nodes) + 2
    s_, t_ = 0, N - 1
    D = Dinic(N)
    for p_ in Pl:
        D.add(s_, idx[p_], 4)
        for q in bits(G.adj[p_] & G.Umask):
            D.add(idx[p_], idx[q], 1)
    for q in Ul:
        D.add(idx[q], t_, 4)
    val = D.maxflow(s_, t_)
    # residual graph
    succ = [[b for (b, c, _) in D.g[v] if c > 0] for v in range(N)]
    pred = [[] for _ in range(N)]
    for v in range(N):
        for b in succ[v]:
            pred[b].append(v)
    # forced in: reachable from s; forced out: can reach t
    def reach(start, nb):
        seen = {start}; st = [start]
        while st:
            v = st.pop()
            for b in nb[v]:
                if b not in seen:
                    seen.add(b); st.append(b)
        return seen
    fin = reach(s_, succ)
    fout = reach(t_, pred)
    assert not (fin & fout)
    free = [v for v in range(N) if v not in fin and v not in fout]
    # SCCs of free part (Kosaraju)
    fs = set(free)
    order = []; seen = set()
    for v in free:
        if v in seen:
            continue
        stack = [(v, iter(succ[v]))]; seen.add(v)
        while stack:
            x, itr = stack[-1]
            nxt = None
            for b in itr:
                if b in fs and b not in seen:
                    nxt = b; break
            if nxt is None:
                order.append(x); stack.pop()
            else:
                seen.add(nxt); stack.append((nxt, iter(succ[nxt])))
    comp = {}
    ncomp = 0
    for v in reversed(order):
        if v in comp:
            continue
        st = [v]; comp[v] = ncomp
        while st:
            x = st.pop()
            for b in pred[x]:
                if b in fs and b not in comp:
                    comp[b] = ncomp; st.append(b)
        ncomp += 1
    members = [[] for _ in range(ncomp)]
    for v in free:
        members[comp[v]].append(v)
    csucc = [set() for _ in range(ncomp)]
    for v in free:
        for b in succ[v]:
            if b in fs and comp[b] != comp[v]:
                csucc[comp[v]].add(comp[b])
    # reverse topological order: successors first. Kosaraju yields comps in topological order of the
    # condensation (sources first), so reverse it.
    rorder = list(range(ncomp - 1, -1, -1))
    out = []
    truncated = False
    chosen = [False] * ncomp

    def rec(i):
        nonlocal truncated
        if len(out) >= cap:
            truncated = True
            return
        if i == len(rorder):
            X = set(fin)
            for c in range(ncomp):
                if chosen[c]:
                    X.update(members[c])
            out.append(X)
            return
        c = rorder[i]
        chosen[c] = False
        rec(i + 1)
        if all(chosen[d] for d in csucc[c]):
            chosen[c] = True
            rec(i + 1)
            chosen[c] = False
    rec(0)
    sides = []
    for X in out:
        A = mask_of(nodes[i - 1] for i in X if 1 <= i <= len(Pl))
        C = mask_of(nodes[i - 1] for i in X if len(Pl) < i <= len(nodes))
        sides.append((A, C))
    return val, sides, truncated


def family_via_mincuts(G):
    s = G.su
    u1 = [u for u in range(s) if G.deg[u] == 5][0]
    fam = set(); low = []; trunc = False; ncuts = 0
    for w in bits(G.Wmask):
        val, sides, tr = mincut_sides(G, w)
        trunc |= tr
        if val >= 4 * s:
            continue
        if val <= 4 * s - 2:
            low.append((w, val))
            continue
        for (A, C) in sides:
            ncuts += 1
            # sanity: each enumerated side is a min cut: slack -1
            k = popc(A) - popc(C)
            sl = G.e_between(A, G.Umask & ~C) - 4 * k
            L.ok("chain: enumerated cut has slack -1", sl == -1, sl)
            Q = G.Vmask & ~(A | C)
            if G.kappa(Q) == 1 and G.g(Q) == 10 and (Q >> u1) & 1 and popc(Q) >= 2 and Q != G.Vmask:
                fam.add(Q)
    return fam, low, trunc, ncuts


def lattice_checks(G, fam):
    u1 = [u for u in range(G.su) if G.deg[u] == 5][0]
    fl = list(fam)
    for Q in fl:
        QW = Q & G.Wmask
        L.ok("chain L4.1(1) |Q|>=3", popc(Q) >= 3)
        L.ok("chain L4.1(2) D^Q(Q_W)=2, D(Q_W)<=2", G.defIn(QW, Q) == 2 and G.defG(QW) <= 2)
        L.ok("chain L4.1(3) deg_Q(u1)>=3", popc(G.adj[u1] & Q) >= 3)
    npairs = 0; ncomparable = 0
    for i in range(len(fl)):
        for j in range(i + 1, len(fl)):
            Q, Qp = fl[i], fl[j]
            npairs += 1
            if (Q & Qp) in (Q, Qp):
                ncomparable += 1
            L.ok("N4 (referee claim): in a sparse instance P is a chain", (Q & Qp) in (Q, Qp))
            L.ok("chain L4.2(a) |QnQ'|>=2", popc(Q & Qp) >= 2)
            L.ok("chain L4.2(b) QuQ' != V", (Q | Qp) != G.Vmask)
            L.ok("chain L4.2(c) QnQ', QuQ' in P", (Q & Qp) in fam and (Q | Qp) in fam,
                 (G.g(Q & Qp), G.g(Q | Qp)))
    R = 0
    for Q in fl:
        R |= Q
    if fl:
        L.ok("chain: union of P in P", R in fam)
    ports = [w for w in bits(G.Wmask) if G.deg[w] <= 5]
    bad = [y for y in ports if not has_4factor_minus(G, y)[0]]
    L.ok("chain L4.4: bad ports = ports in a member of P", sorted(bad) == sorted(y for y in ports if (R >> y) & 1))
    L.ok("chain L4.4: bad-port deficiency <= 2", sum(6 - G.deg[y] for y in bad) <= 2)
    return npairs, ncomparable, len(bad)


if __name__ == "__main__":
    seed, budget, BN = int(sys.argv[1]), float(sys.argv[2]), int(sys.argv[3])
    rng = random.Random(seed)
    t0 = time.time()
    st = {"built": 0, "planted_ok": 0, "sparse": 0, "P_hist": {}, "pairs": 0, "comparable_pairs": 0,
          "incomparable_pairs": 0, "brute_crosscheck": 0, "truncated": 0, "by_shape": {}}
    while time.time() - t0 < budget:
        c2 = rng.choice([4, 4, 5]); p = rng.choice([4, 5, 5, 6]); t = rng.choice([6, 6, 7])
        variant = rng.choice([0, 1])
        r = build_chain(c2, p, t, variant, rng)
        if r is None:
            continue
        G, info = r
        st["built"] += 1
        Q1 = G.Vmask & ~info["S1"]; Q2 = G.Vmask & ~info["S2"]
        good = all(G.g(Q) == 10 and G.kappa(Q) == 1 and (Q >> info["u1"]) & 1 for Q in (Q1, Q2))
        L.ok("chain: both planted sets have g = 10, kappa = 1, contain u1", good,
             (G.g(Q1), G.g(Q2), G.kappa(Q1), G.kappa(Q2)))
        if not good:
            continue
        st["planted_ok"] += 1
        if min_proper_g(G, cap=10) < 10:
            continue
        st["sparse"] += 1
        fam, low, trunc, ncuts = family_via_mincuts(G)
        L.ok("chain sparse: no W-vertex with maxflow(G - w) <= 4s - 2", not low, low)
        st["truncated"] += int(trunc)
        L.ok("chain sparse: both planted petals found in P", Q1 in fam and Q2 in fam)
        if G.n <= BN:
            best, famb, _ = L.enumerate_all(G)
            L.ok("chain: min-cut enumeration of P equals brute force", set(famb) == fam and best >= 10)
            st["brute_crosscheck"] += 1
        npairs, ncomp, nbad = lattice_checks(G, fam)
        st["pairs"] += npairs; st["comparable_pairs"] += ncomp; st["incomparable_pairs"] += npairs - ncomp
        k = str(len(fam)); st["P_hist"][k] = st["P_hist"].get(k, 0) + 1
        sh = "c%d_p%d_t%d_v%d" % (c2, p, t, variant); st["by_shape"][sh] = st["by_shape"].get(sh, 0) + 1
    res = {"seed": seed, "stats": st, "checks": L.cnt, "failures": len(L.fails), "seconds": round(time.time() - t0, 1)}
    print(json.dumps(res, indent=1))
    json.dump(res, open("out_chain_%d.json" % seed, "w"), indent=1)
    sys.exit(1 if L.fails else 0)
