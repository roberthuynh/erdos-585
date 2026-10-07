"""Direct test of Lemmas 4.1, 4.2 and 4.4 by brute force over ALL vertex subsets (Gray code).
For each C1 instance: exact min of g over proper sets with |S| >= 2 (sparsity); the family
P = {Q proper, |Q| >= 2, g(Q) = 10, kappa(Q) = 1, u1 in Q} enumerated completely; bad ports by max flow.
If sparse (and D_U = 1): Lemma 4.1 on every member, Lemma 4.2 on every pair (or a sample), union of P in P,
bad ports = ports lying in some member, bad-port deficiency <= 2. If D_U = 0 and sparse: no bad port.
If not sparse: record pairs in P whose union or intersection leaves P (shows sparsity is needed).
Usage: rc_lattice.py MODE ARGS
  MODE g6 S       : read graph6 C1 instances (first class = U of size S) from stdin
  MODE rand SEED N SMIN SMAX WMIN DU : random instances"""
import sys, json, random, time
from rc_common import *

cnt = {}
fails = []
examples = {}


def ok(name, cond, info=None):
    cnt[name] = cnt.get(name, 0) + 1
    if not cond:
        fails.append((name, info))
        if len(fails) < 10:
            print("FAIL", name, info, flush=True)


def enumerate_all(G):
    n, su, adj = G.n, G.su, G.adj
    u1 = [u for u in range(su) if G.deg[u] == 5]
    u1b = (1 << u1[0]) if u1 else 0
    S = 0; e = 0; nu = 0; nw = 0
    best = 10 ** 9
    fam = []
    low = []  # proper sets with g <= 8 (a few)
    for i in range(1, 1 << n):
        v = (i & -i).bit_length() - 1
        b = 1 << v
        if S & b:
            S ^= b
            e -= (adj[v] & S).bit_count()
            if v < su: nu -= 1
            else: nw -= 1
        else:
            e += (adj[v] & S).bit_count()
            S ^= b
            if v < su: nu += 1
            else: nw += 1
        sz = nu + nw
        if sz < 2 or sz == n:
            continue
        gv = 6 * sz - 2 * e
        if gv < best:
            best = gv
        if gv <= 8 and len(low) < 5:
            low.append(S)
        if gv == 10 and nu - nw == 1 and (S & u1b):
            fam.append(S)
    return best, fam, low


def test_instance(G, label):
    s = G.su
    DU = G.defG(G.Umask)
    best, fam, low = enumerate_all(G)
    sparse = best >= 10
    ok("brute min proper g agrees with flow-based min_proper_g (capped at 10)",
       min(best, 10) == min_proper_g(G, cap=10), (best,))
    ports = [w for w in bits(G.Wmask) if G.deg[w] <= 5]
    bad = [y for y in ports if not has_4factor_minus(G, y)[0]]
    famset = set(fam)
    rec = {"sparse": sparse, "DU": DU, "P_size": len(fam), "bad": len(bad)}
    if not sparse:
        # Lemma 4.2 can fail without sparsity: look for a pair whose union/intersection leaves P
        if DU == 1 and len(fam) >= 2:
            for i in range(min(len(fam), 60)):
                for j in range(i + 1, min(len(fam), 60)):
                    Q, Qp = fam[i], fam[j]
                    if (Q | Qp) not in famset or (Q & Qp) not in famset:
                        if "lattice_fails_nonsparse" not in examples:
                            examples["lattice_fails_nonsparse"] = {
                                "label": label, "Q": bits(Q), "Qp": bits(Qp),
                                "g_union": G.g(Q | Qp), "g_inter": G.g(Q & Qp),
                                "union_is_V": (Q | Qp) == G.Vmask}
                        cnt["nonsparse pairs leaving P"] = cnt.get("nonsparse pairs leaving P", 0) + 1
                        break
        return rec
    if DU == 0:
        ok("L4.4 sparse C0: no bad port", not bad, bits(G.Wmask))
        ok("sparse C0 => W-degrees >= 5 (a G110 gadget)", all(G.deg[w] >= 5 for w in bits(G.Wmask)))
        return rec
    u1 = [u for u in range(s) if G.deg[u] == 5][0]
    ok("sparse C1 => W-degrees >= 4", all(G.deg[w] >= 4 for w in bits(G.Wmask)))
    for Q in fam:
        QW = Q & G.Wmask
        ok("L4.1(1) |Q|>=3", popc(Q) >= 3)
        ok("L4.1(2) D^Q(Q_W)=2 and D(Q_W)<=2", G.defIn(QW, Q) == 2 and G.defG(QW) <= 2)
        ok("L4.1(3) deg_Q(u1)>=3", popc(G.adj[u1] & Q) >= 3)
    pairs = 0
    L = len(fam)
    if L <= 400:
        prs = ((i, j) for i in range(L) for j in range(i + 1, L))
    else:
        rr = random.Random(L)
        prs = ((rr.randrange(L), rr.randrange(L)) for _ in range(80000))
    for i, j in prs:
        Q, Qp = fam[i], fam[j]
        pairs += 1
        ok("L4.2(a) |Q n Q'|>=2", popc(Q & Qp) >= 2)
        ok("L4.2(b) Q u Q' != V", (Q | Qp) != G.Vmask)
        ok("L4.2(c) Q n Q' in P and Q u Q' in P", (Q & Qp) in famset and (Q | Qp) in famset)
    if fam:
        R = 0
        for Q in fam:
            R |= Q
        ok("union of all of P is in P", R in famset)
        in_union_ports = [y for y in ports if (R >> y) & 1]
    else:
        in_union_ports = []
    ok("L4.4 bad ports = ports lying in a member of P", sorted(bad) == sorted(in_union_ports),
       (bad, in_union_ports))
    ok("L4.4 bad-port deficiency <= 2", sum(6 - G.deg[y] for y in bad) <= 2)
    # every violation at a bad port has its complement in P: check the min cut of each bad port
    for y in bad:
        val = has_4factor_minus(G, y)[1]
        ok("L3.2 in sparse instance: maxflow(G-y) = 4s-1", val == 4 * s - 1, val)
    rec.update({"pairs": pairs, "bad_def": sum(6 - G.deg[y] for y in bad),
                "P_members_with_port": sum(1 for Q in fam if G.defG(Q & G.Wmask) > 0)})
    return rec


def main():
    global summary
    mode = sys.argv[1]
    t0 = time.time()
    summary = {"instances": 0, "sparse": 0, "sparse_DU1": 0, "sparse_DU0": 0,
               "sparse_with_P_ge2": 0, "max_P": 0, "sparse_with_bad": 0, "pairs_tested": 0}


    def account(rec):
        summary["instances"] += 1
        if rec["sparse"]:
            summary["sparse"] += 1
            summary["sparse_DU%d" % rec["DU"]] += 1
            if rec["P_size"] >= 2 and rec["DU"] == 1:
                summary["sparse_with_P_ge2"] += 1
            summary["max_P"] = max(summary["max_P"], rec["P_size"] if rec["DU"] == 1 else 0)
            if rec["bad"]:
                summary["sparse_with_bad"] += 1
            summary["pairs_tested"] += rec.get("pairs", 0)


    if mode == "g6":
        S = int(sys.argv[2])
        budget = float(sys.argv[3]) if len(sys.argv) > 3 else 200
        for k, line in enumerate(sys.stdin):
            if not line.strip() or line.startswith('>'):
                continue
            n, edges = g6decode(line)
            el = [(i, j) if i < S else (j, i) for (i, j) in edges]
            G = Bip(S, n - S, el)
            account(test_instance(G, "g6:%d" % k))
            if time.time() - t0 > budget:
                summary["stopped_early_at_line"] = k
                break
        tag = "g6_s%d" % S
    else:
        seed, N, smin, smax, wmin, DUarg = map(int, sys.argv[2:8])
        rng = random.Random(seed)
        for it in range(N):
            s = rng.randint(smin, smax)
            DU = DUarg if DUarg in (0, 1) else rng.choice([0, 1])
            G = random_c1(s, DU, wmin, rng)
            if G is None:
                continue
            account(test_instance(G, "rand:%d:%d" % (seed, it)))
            if time.time() - t0 > 200:
                summary["stopped_early_at"] = it
                break
        tag = "rand_%d" % seed
    res = {"tag": tag, "summary": summary, "checks": cnt, "failures": len(fails), "examples": examples,
           "seconds": round(time.time() - t0, 1)}
    print(json.dumps(res, indent=1))
    json.dump(res, open("out_lattice_%s.json" % tag, "w"), indent=1)
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
