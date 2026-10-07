"""Checks for Section 5.4 (REPORT.md Theorem 5, c = 2) with my own code.
(T1) Tutte form with f = deg - 4: on random general graphs with min degree >= 4, max degree <= 6,
     n <= 9, exhaustive over all 3^n pairs (S,T): min delta(S,T) >= 0  <=>  a 4-factor exists
     (SAT, all degrees exactly 4). q counts components with e(C,S) odd; delta even.
(T2) Budget identity 3 delta + 2D = 2e(S) + 4e(T) + 4D_T + sum_C w(C), w(C) = 2D_C + e(C,S)
     + 2e(C,T) - 3[e(C,S) odd]; identity (**) delta = 4(|T|-|S|) + 2e(S) + e(S,R) - q;
     single-vertex w = 12 - a - 3[a odd] >= 4.
(T3) P_2 exhaustively for small n with plain geng: every graph with max degree <= 6, n >= 2,
     e >= 3n - 2 has a 4-regular subgraph (SAT); n = 7..9 complete, n = 10 time-boxed.
(T4) For every graph in (T3) with e = 3n - 2 and min degree >= 4 and NO spanning 4-factor:
     every barrier has the c = 2 type (|S| = |T|+1, e(S) = 1, e(T) = 0, D_T = 0, R empty).
"""
import sys, random, json, time, itertools, subprocess, os
import networkx as nx
from pysat.solvers import Solver
from ref_common import quartic_subgraph

GENG = os.path.expanduser("~/.cache/erdos585/nauty2_9_3/geng")
rng = random.Random(585)
t0 = time.time()
fails = []; counts = {"T1": 0, "T2": 0, "T3": 0, "T4_graphs": 0, "T4_barriers": 0}

def factor_exact4(n, edges):
    inc = [[] for _ in range(n)]
    for i, (a, b) in enumerate(edges):
        inc[a].append(i + 1); inc[b].append(i + 1)
    clauses = []
    for v in range(n):
        lits = inc[v]; d = len(lits)
        if d < 4:
            return False
        for r in range(d + 1):
            if r == 4: continue
            for T in itertools.combinations(range(d), r):
                Ts = set(T)
                clauses.append([-lits[i] if i in Ts else lits[i] for i in range(d)])
    with Solver(name="cadical153", bootstrap_with=clauses) as sol:
        return sol.solve()

def tutte_data(G, S, T):
    """delta(S,T) for f = deg - 4, plus the budget-identity terms."""
    n = G.number_of_nodes()
    deg = dict(G.degree())
    R = [v for v in G if v not in S and v not in T]
    H = G.subgraph(R)
    comps = [set(c) for c in nx.connected_components(H)]
    def e_in(X): return G.subgraph(X).number_of_edges()
    def e_bt(X, Y): return sum(1 for a in X for b in G[a] if b in Y)
    q = sum(1 for C in comps if e_bt(C, S) % 2 == 1)
    fS = sum(deg[v] - 4 for v in S); fT = sum(deg[v] - 4 for v in T)
    degGmS_T = sum(deg[v] - sum(1 for b in G[v] if b in S) for v in T)
    delta = fS - fT + degGmS_T - q
    D = 6 * n - 2 * G.number_of_edges()
    DT = sum(6 - deg[v] for v in T)
    wsum = 0
    for C in comps:
        DC = sum(6 - deg[v] for v in C); a = e_bt(C, S); b = e_bt(C, T)
        w = 2 * DC + a + 2 * b - 3 * (a % 2)
        wsum += w
        if len(C) == 1 and w != 12 - a - 3 * (a % 2):
            fails.append(("T2-single", list(G.edges()), S, T))
        if w < 0:
            fails.append(("T2-wneg", list(G.edges()), S, T))
    rhs = 2 * e_in(S) + 4 * e_in(T) + 4 * DT + wsum
    if 3 * delta + 2 * D != rhs:
        fails.append(("T2", list(G.edges()), S, T))
    if delta != 4 * (len(T) - len(S)) + 2 * e_in(S) + e_bt(S, R) - q:
        fails.append(("T2**", list(G.edges()), S, T))
    if delta % 2 != 0:
        fails.append(("T2-parity", list(G.edges()), S, T))
    return delta

def random_graph_deg46(n):
    for _ in range(100):
        degs = [rng.randint(4, 6) for _ in range(n)]
        if sum(degs) % 2: degs[0] += 1 if degs[0] < 6 else -1
        try:
            G = nx.random_degree_sequence_graph(degs, seed=rng.randrange(10**9), tries=20)
            return G
        except Exception:
            continue
    return None

# T1 + T2
for n in [7, 8, 9]:
    for _ in range(6 if n < 9 else 3):
        G = random_graph_deg46(n)
        if G is None: continue
        V = list(G)
        mind = 10**9
        for assign in itertools.product(range(3), repeat=n):
            S = {V[i] for i in range(n) if assign[i] == 1}; T = {V[i] for i in range(n) if assign[i] == 2}
            d = tutte_data(G, S, T); counts["T2"] += 1
            mind = min(mind, d)
        has = factor_exact4(n, list(G.edges()))
        counts["T1"] += 1
        if has != (mind >= 0):
            fails.append(("T1", list(G.edges()), mind, has))
        if time.time() - t0 > 100: break

# T3 + T4 with geng
for n in [7, 8, 9, 10]:
    if time.time() - t0 > 150: break
    cmd = [GENG, "-q", "-D6", str(n), f"{3*n-2}:{n*(n-1)//2}"]
    try:
        proc = subprocess.run(cmd, capture_output=True, text=True, timeout=max(5, 200 - (time.time() - t0)))
    except subprocess.TimeoutExpired:
        counts[f"T3_n{n}"] = "geng timeout"; break
    lines = [l for l in proc.stdout.split("\n") if l.strip()]
    done = 0
    for line in lines:
        G = nx.from_graph6_bytes(line.encode())
        edges = list(G.edges())
        if quartic_subgraph(n, edges) is None:
            fails.append(("T3", line))
        done += 1
        if G.number_of_edges() == 3 * n - 2 and min(d for _, d in G.degree()) >= 4 and not factor_exact4(n, edges):
            counts["T4_graphs"] += 1
            V = list(G)
            for assign in itertools.product(range(3), repeat=n):
                S = {V[i] for i in range(n) if assign[i] == 1}; T = {V[i] for i in range(n) if assign[i] == 2}
                d = tutte_data(G, S, T)
                if d < 0:
                    counts["T4_barriers"] += 1
                    R = [v for v in V if v not in S and v not in T]
                    DT = sum(6 - G.degree(v) for v in T)
                    typ = (len(S) == len(T) + 1 and G.subgraph(S).number_of_edges() == 1
                           and G.subgraph(T).number_of_edges() == 0 and DT == 0 and not R and d == -2)
                    if not typ:
                        fails.append(("T4", line, sorted(S), sorted(T)))
        if time.time() - t0 > 215:
            counts[f"T3_n{n}"] = f"time-boxed after {done} of {len(lines)}"; break
    else:
        counts[f"T3_n{n}"] = f"complete: {len(lines)} graphs"
    counts["T3"] += done

out = dict(counts=counts, fails=len(fails), first=[str(f)[:200] for f in fails[:5]], seconds=round(time.time() - t0, 1))
json.dump(out, open("out_tutte.json", "w"), indent=1)
print(json.dumps(out, indent=1))
print("RESULT:", "PASS" if not fails else "FAIL")
sys.exit(0 if not fails else 1)
