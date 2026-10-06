"""Referee 2: Lemma 4.4 (minimality-free core) and Lemma 4.2 (lattice) on built instances.

For each instance from r2_build.build (or random C0/C1 instances with --random):
  - exact min g over proper sets with >= 2 vertices (r2sub ming); sparse iff min g >= 10;
  - bad ports (G - y without spanning 4-factor, networkx max flow);
  - if sparse:
      L44a  D_U = 0 implies no bad port;
      L44b  D_U = 1 implies total deficiency of bad ports <= 2;
      L32   every violation (all cuts, r2sub viol) at every bad port has k = 2, sigma = -1,
            D(C) = 0, g(V - S) = 10, kappa(V - S) = 1 and V - S in the family P;
      L42   P (all members, r2sub petals) is closed under intersection and union;
      CHAIN number of incomparable pairs in P (the first review's optional claim: 0);
      UNION union of petals of the bad ports is in P and its W-part has deficiency <= 2;
  - always: SAT finds a quartic subgraph (Theorem 4.3 predicts one).
Usage: r2_sparse_core.py SEED BUDGET_SECONDS MODE   (MODE = build | random)
Writes out_sparse_<MODE>_<SEED>.json; exit 1 on any failed check.
"""
import json
import os
import random
import subprocess
import sys
import time
from r2common import BG, random_C1, bits, mask_of, popcount, bad_ports, quartic_subgraph
from r2_build import build

HERE = os.path.dirname(os.path.abspath(__file__))
SUB = os.path.join(HERE, "r2sub")


def to_input(G):
    return f"{G.s} {G.r} {len(G.edges)}\n" + "".join(f"{u} {w}\n" for (u, w) in G.edges)


def run_sub(G, *args):
    p = subprocess.run([SUB, *map(str, args)], input=to_input(G), capture_output=True, text=True,
                       timeout=240)
    if p.returncode != 0:
        raise RuntimeError(p.stderr)
    return p.stdout


def analyse(G, rec):
    fails = []
    out = run_sub(G, "ming").split()
    ming = int(out[1])
    rec["ming"] = ming
    bp = bad_ports(G)
    rec["bad_ports"] = bp
    rec["bad_def"] = sum(6 - G.deg[y] for y in bp)
    rec["DU"] = G.DU()
    sparse = ming >= 10
    rec["sparse"] = sparse
    if sparse:
        if G.DU() == 0 and bp:
            fails.append("L44a")
        if G.DU() == 1:
            u1 = [u for u in G.U if G.deg[u] == 5][0]
            if rec["bad_def"] > 2:
                fails.append("L44b")
            pout = run_sub(G, "petals", u1).splitlines()
            head = pout[0].split()
            npet, checked = int(head[1]), int(head[5])
            bcap, bcup, inc = int(head[7]), int(head[9]), int(head[11])
            rec["P_size"] = npet
            rec["P_incomparable"] = inc
            if checked and (bcap or bcup):
                fails.append("L42")
            if not checked:
                rec["P_closure_unchecked"] = True
            Pset = set()
            # the listing prints at most 64 members; fetch membership by direct test instead
            def inP(Q):
                return (Q != G.full() and popcount(Q) >= 2 and G.g(Q) == 10 and G.kappa(Q) == 1
                        and (Q >> u1) & 1)
            union = 0
            nviol_total = 0
            for y in bp:
                vout = run_sub(G, "viol", y).splitlines()
                for line in vout:
                    if line.startswith("V "):
                        f = line.split()
                        Q = int(f[1], 16)
                        k, sg, dc, gq, kq = (int(f[3]), int(f[5]), int(f[7]), int(f[9]), int(f[11]))
                        nviol_total += 1
                        if not (k == 2 and sg == -1 and dc == 0 and gq == 10 and kq == 1 and inP(Q)
                                and (Q >> y) & 1):
                            fails.append(("L32", y, line))
                        union |= Q
            rec["n_viol"] = nviol_total
            if bp:
                Wdef_union = sum(6 - G.deg[w] for w in bits(union & G.Wmask))
                rec["union_Wdef"] = Wdef_union
                if not inP(union) or Wdef_union > 2:
                    fails.append("UNION")
    H = quartic_subgraph(G.n, G.edges)
    rec["quartic"] = H is not None
    if H is None:
        fails.append("NO_QUARTIC")
    rec["fails"] = [str(f) for f in fails]
    return fails


def main(seed, budget, mode):
    rng = random.Random(seed)
    t0 = time.time()
    recs = []
    allfails = []
    tally = dict(built=0, sparse=0, sparse_with_bad=0, bad_def_hist={}, P_sizes={},
                 incomparable_pairs=0, quartic_all=True, n_bad_ports=0, n_viol_checked=0,
                 sparse_DU0=0, sparse_DU1=0)
    while time.time() - t0 < budget:
        if mode == "build":
            c = rng.choice([4, 4, 5, 5, 6])
            t = rng.choice([7, 8]) if c <= 5 else 7
            eps = rng.choice([0, 1])
            res = build(c, t, eps, rng)
            if res is None:
                continue
            G, info = res
            rec = dict(info)
        else:
            s = rng.choice([8, 9, 10, 11, 12])
            DU = rng.choice([0, 1])
            G = random_C1(s, DU, rng.choice([1, 2]), rng)
            if G is None:
                continue
            rec = dict(s=s)
        if G.n > 29:
            continue
        rec["edges"] = G.edges
        tally["built"] += 1
        fails = analyse(G, rec)
        if rec["sparse"]:
            tally["sparse"] += 1
            tally["sparse_DU%d" % rec["DU"]] += 1
            tally["n_bad_ports"] += len(rec["bad_ports"])
            tally["n_viol_checked"] += rec.get("n_viol", 0)
            if rec["bad_ports"]:
                tally["sparse_with_bad"] += 1
                key = str(rec["bad_def"])
                tally["bad_def_hist"][key] = tally["bad_def_hist"].get(key, 0) + 1
            if "P_size" in rec:
                key = str(rec["P_size"])
                tally["P_sizes"][key] = tally["P_sizes"].get(key, 0) + 1
                tally["incomparable_pairs"] += rec.get("P_incomparable", 0)
        if not rec["quartic"]:
            tally["quartic_all"] = False
        if fails:
            allfails.append(rec)
        if rec["sparse"] and rec["bad_ports"] and len(recs) < 60:
            recs.append(rec)
    out = dict(seed=seed, mode=mode, budget=budget, tally=tally, failures=allfails[:20],
               n_failures=len(allfails), sample_sparse_with_bad=recs[:30])
    with open(os.path.join(HERE, f"out_sparse_{mode}_{seed}.json"), "w") as f:
        json.dump(out, f)
    print(json.dumps(dict(seed=seed, mode=mode, tally=tally, n_failures=len(allfails))))
    return 1 if allfails else 0


if __name__ == "__main__":
    sys.exit(main(int(sys.argv[1]), float(sys.argv[2]), sys.argv[3]))
