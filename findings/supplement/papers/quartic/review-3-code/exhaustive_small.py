"""Exhaustive check of Theorem 4.3 at small sizes with plain nauty genbg as generator and my own
SAT decider. Usage: exhaustive_small.py s [res/mod]. Generates every C1(s) instance up to
isomorphism: sides s and s+1, U-degrees in [5,6], W-degrees in [0,6], 6s-1 <= e <= 6s
(so D_U in {0,1}). For each: quartic subgraph (SAT, witness validated), bad ports (flow),
and for graphs with min W-degree >= 4 also exact sparsity by subset DP."""
import sys, subprocess, json, time, os
import networkx as nx
from ref_common import Bip, quartic_subgraph, has_4factor_balanced

GENBG = os.path.expanduser("~/.cache/erdos585/nauty2_9_3/genbg")
s = int(sys.argv[1])
slice_ = sys.argv[2] if len(sys.argv) > 2 else None
t0 = time.time()
cmd = [GENBG, "-q", "-d5:0", "-D6:6", str(s), str(s + 1), f"{6*s-1}:{6*s}"]
if slice_:
    cmd.append(slice_)
proc = subprocess.run(cmd, capture_output=True, text=True, timeout=230)
lines = [l for l in proc.stdout.split("\n") if l.strip()]

def popcount(x):
    return bin(x).count("1")

def min_g_proper(B):
    """min of g(S) over S with 2 <= |S| <= n-1, by DP over all subsets."""
    n = B.n
    adjb = [sum(1 << w for w in B.adj[v]) for v in range(n)]
    e = [0] * (1 << n)
    best = 10 ** 9
    for S in range(1, 1 << n):
        low = S & (-S)
        v = low.bit_length() - 1
        rest = S ^ low
        e[S] = e[rest] + popcount(adjb[v] & rest)
        c = popcount(S)
        if 2 <= c <= n - 1:
            gS = 6 * c - 2 * e[S]
            if gS < best:
                best = gS
    return best

stats = {"s": s, "slice": slice_, "graphs": 0, "DU0": 0, "DU1": 0, "no_quartic": [], "bad_port_graphs": 0,
         "minW4_graphs": 0, "minW4_sparse": 0, "minW4_nonsparse_examples": 0, "min_g_hist": {}}
for line in lines:
    G = nx.from_graph6_bytes(line.encode())
    edges = [(a, b) if a < s else (b, a) for (a, b) in G.edges()]
    B = Bip(s, s + 1, edges)
    assert B.is_C1(), line
    stats["graphs"] += 1
    stats["DU1" if B.D(B.U) == 1 else "DU0"] += 1
    F = quartic_subgraph(B.n, B.edges)
    if F is None:
        stats["no_quartic"].append(line)
    ports = [w for w in B.W if B.deg(w) <= 5]
    badports = [y for y in ports if not has_4factor_balanced([w for w in B.W if w != y], list(B.U), B.adj)]
    if badports:
        stats["bad_port_graphs"] += 1
    if min(B.deg(w) for w in B.W) >= 4 and B.n <= 17:
        stats["minW4_graphs"] += 1
        mg = min_g_proper(B)
        stats["min_g_hist"][str(mg)] = stats["min_g_hist"].get(str(mg), 0) + 1
        if mg >= 10:
            stats["minW4_sparse"] += 1
            # Lemma 4.4: sparse + D_U = 0 => no bad port; sparse => bad ports total deficiency <= 2
            if B.D(B.U) == 0 and badports:
                stats.setdefault("L44_fail", []).append(line)
            if sum(6 - B.deg(y) for y in badports) > 2:
                stats.setdefault("L44_fail", []).append(line)
    if time.time() - t0 > 225:
        stats["TIMEOUT_after_graphs"] = stats["graphs"]
        break
stats["seconds"] = round(time.time() - t0, 1)
json.dump(stats, open(f"out_exhaustive_s{s}_{(slice_ or 'all').replace('/', 'of')}.json", "w"), indent=1)
print(json.dumps(stats, indent=1))
ok = not stats["no_quartic"] and "L44_fail" not in stats and "TIMEOUT_after_graphs" not in stats
print("RESULT:", "PASS" if ok else "FAIL/INCOMPLETE")
sys.exit(0 if ok else 1)
