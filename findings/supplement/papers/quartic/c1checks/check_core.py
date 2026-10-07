"""Exhaustive check of the core lemma (C1-PAPER.md Lemma 4.4) on small C1 and C0 instances.

Core lemma (no minimality, no quartic-freeness assumed): let G be a C1(s) instance that is SPARSE,
i.e. g(S) = 6|S| - 2e(G[S]) >= 10 for every S with 2 <= |S| <= |V| - 1. Call a W-vertex y of degree
<= 5 a port, and call it bad if G - y has no spanning 4-regular subgraph. Then
  (a) if D_U = 0 there is no bad port;
  (b) if D_U = 1, for every bad port y every violation S of G - y has Q = V - S in the family
      P = {Q : g(Q) = 10, kappa(Q) = 1, u1 in Q, Q proper};
  (c) P is closed under intersection and union (checked on all pairs of petals found);
  (d) the union of all petals of bad ports lies in P, so the bad ports have total deficiency <= 2.
Also recorded: every instance has a quartic subgraph (SAT; census replication for these sizes), and
for non-sparse instances in which every port is bad, which inequality of the proof fails.

Generator: nauty genbg 2.9.3 (plain), first class U (s vertices), second class W (s + 1).
Usage: python check_core.py [s_max_full] [s8_mod]   (default 7 and 0 = skip s = 8)
"""
import json
import subprocess
import sys
import time
from os.path import expanduser

from c1common import Tables, parse_genbg_line, has_4factor, has_quartic, popcount, members

GENBG = expanduser("~/.cache/erdos585/nauty2_9_3/genbg")
s_max = int(sys.argv[1]) if len(sys.argv) > 1 else 7
s8_mod = int(sys.argv[2]) if len(sys.argv) > 2 else 0
FAST = False          # s <= s_max: full tables for every graph
CHECK_SAT = True

t0 = time.time()
out = {"runs": [], "failures": []}


def fail(msg):
    out["failures"].append(msg)


def run_class(s, DU, wmin, resmod=None):
    e = 6 * s - DU
    dmin_u = 6 - DU if DU == 1 else 6
    cmd = [GENBG, "-q", f"-d{dmin_u}:{wmin}", "-D6:6", str(s), str(s + 1), f"{e}:{e}"]
    if resmod:
        cmd.append(resmod)
    proc = subprocess.run(cmd, capture_output=True, text=True, timeout=200)
    lines = [l for l in proc.stdout.splitlines() if l.strip()]
    st = {"s": s, "DU": DU, "wmin": wmin, "resmod": resmod, "graphs": len(lines), "sparse": 0,
          "sparse_with_bad_port": 0, "bad_ports_in_sparse": 0, "max_bad_def_in_sparse": 0,
          "all_ports_bad": 0, "all_ports_bad_and_sparse": 0, "quartic_found": 0,
          "violations_checked": 0, "petal_pairs_checked": 0, "min_g_hist": {},
          "all_bad_failure_steps": {}}
    for line in lines:
        G = parse_genbg_line(line, s, s + 1)
        assert G.max_deg() <= 6
        # orient: u1 = the U-vertex of degree 5 (if DU = 1)
        Ud = [u for u in G.U if G.deg[u] == 5]
        assert len(Ud) == DU
        u1 = Ud[0] if DU == 1 else None
        ports = [w for w in G.W if G.deg[w] <= 5]
        bad = [y for y in ports if not has_4factor(G, delete=[y])]
        if FAST and not bad:
            st["graphs_no_bad_port_fast_path"] = st.get("graphs_no_bad_port_fast_path", 0) + 1
            if not CHECK_SAT:
                continue
            if has_quartic(G) is None:
                fail(f"no quartic subgraph: s={s} {line}")
            else:
                st["quartic_found"] += 1
            continue
        T = Tables(G)
        full = G.full
        n = G.n
        ming = min(T.g[m] for m in range(1, full) if T.size[m] >= 2)
        st["min_g_hist"][str(ming)] = st["min_g_hist"].get(str(ming), 0) + 1
        sparse = ming >= 10
        if sparse:
            st["sparse"] += 1
        H = has_quartic(G)
        if H is None:
            fail(f"no quartic subgraph: s={s} {line}")
        else:
            st["quartic_found"] += 1
        if len(bad) == len(ports):
            st["all_ports_bad"] += 1
        petals = []
        steps = set()
        for y in bad:
            rest = full ^ (1 << y)
            m = rest
            while True:
                k = T.nW[m] - T.nU[m]
                sig = T.sdegW[m] - T.eS[m] - 4 * k
                if sig < 0:
                    st["violations_checked"] += 1
                    Q = full ^ m
                    gQ = T.g[Q]
                    if gQ >= 10:
                        ok = (DU == 1 and k == 2 and sig == -1 and T.DU[m] == 0 and gQ == 10
                              and T.kappa[Q] == 1 and (Q >> u1) & 1)
                        if not ok:
                            fail(f"Lemma 3.2 forced data: s={s} {line} y={y}")
                        petals.append((y, Q))
                    else:
                        steps.add("g(V - S) <= 8 for a violation S (Lemma 3.2 premise)")
                        if sparse:
                            fail(f"sparse but g(Q) < 10: s={s} {line}")
                if m == 0:
                    break
                m = (m - 1) & rest
        if sparse and bad:
            st["sparse_with_bad_port"] += 1
            st["bad_ports_in_sparse"] += len(bad)
            if DU == 0:
                fail(f"(a) bad port in sparse C0 instance s={s} {line}")
        # petal family checks
        for i in range(len(petals)):
            Qi = petals[i][1]
            gm = T.g[Qi ^ (1 << u1)]
            if gm < 10:
                steps.add("g(Q - u1) <= 8 (Lemma 4.1 premise)")
                if sparse:
                    fail("sparse but g(Q - u1) < 10")
            elif bin(T.nb[u1] & Qi).count("1") < 3:
                fail("deg_Q(u1) < 3 although g(Q - u1) >= 10")
            for j in range(i + 1, len(petals)):
                Qj = petals[j][1]
                st["petal_pairs_checked"] += 1
                I, Un = Qi & Qj, Qi | Qj
                if Un == full:
                    fail("union of two petals is V")
                if I == (1 << u1):
                    steps.add("petals meet only in u1")
                    if sparse:
                        fail("sparse but petals meet only in u1")
                    continue
                if T.g[I] + T.g[Un] > 20:
                    fail("submodularity")
                if T.g[I] >= 10 and T.g[Un] >= 10:
                    if not (T.g[I] == 10 == T.g[Un] and T.kappa[I] == 1 == T.kappa[Un]):
                        fail("cap/cup not in P although both g >= 10")
                else:
                    steps.add("g(cap) or g(cup) <= 8 (Lemma 4.2 premise)")
                    if sparse:
                        fail("sparse but g(cap) or g(cup) < 10")
        if petals:
            Ustar = 0
            for (_, Q) in petals:
                Ustar |= Q
            badset = set(y for (y, _) in petals)
            inP = (Ustar != full and T.g[Ustar] == 10 and T.kappa[Ustar] == 1)
            bdef = sum(6 - G.deg[y] for y in bad)
            if sparse:
                if not inP:
                    fail(f"(d) union of petals not in P in a sparse instance s={s} {line}")
                if bdef > 2:
                    fail(f"(d) bad deficiency {bdef} > 2 in a sparse instance s={s} {line}")
                st["max_bad_def_in_sparse"] = max(st["max_bad_def_in_sparse"], bdef)
            elif not inP:
                steps.add("union of petals not in P")
        if len(bad) == len(ports):
            if sparse:
                st["all_ports_bad_and_sparse"] += 1
                fail(f"all ports bad in a sparse instance s={s} {line}")
            for x in steps:
                st["all_bad_failure_steps"][x] = st["all_bad_failure_steps"].get(x, 0) + 1
    st["seconds"] = round(time.time() - t0, 1)
    out["runs"].append(st)
    print(json.dumps(st), flush=True)


for s in range(5, s_max + 1):
    run_class(s, 1, 4)
    run_class(s, 0, 4)
if s8_mod:
    FAST = True       # s = 8 slice: tables only for graphs with a bad port
    CHECK_SAT = False
    run_class(8, 1, 4, resmod=f"0/{s8_mod}")
    run_class(8, 0, 4, resmod=f"0/{s8_mod}")
out["seconds"] = round(time.time() - t0, 1)
out["RESULT"] = "PASS" if not out["failures"] else "FAIL"
with open("out_core.json", "w") as fh:
    json.dump(out, fh, indent=1)
print("RESULT:", out["RESULT"], "failures:", len(out["failures"]), "seconds:", out["seconds"])
sys.exit(0 if not out["failures"] else 1)
