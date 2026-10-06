#!/usr/bin/env python3
"""sat_check.py -- exact SAT decision of S6 tests (wave6/s6n22).

Input: lines "<graph6> o y" (the s6n22 .surv format; extra fields ignored). For each line, Y = B - o - y
is decided by wave4/va6/tools/span_oracle.py (MiniSat, lazy connectivity cuts). A SPAN witness is
re-checked here independently (each colour class is a Hamilton cycle of Y, the classes are
edge-disjoint, every edge lies in Y). A NOSPAN or TIMEOUT answer is re-decided by a second SAT
decider (wave5/s6hunt/code/myspan.py span2hc, Glucose) and a certificate JSON is written next to the
output; a NOSPAN confirmed by both is reported as CANDIDATE_FAILURE (to be certified and frozen).

Usage: sat_check.py in.txt out.jsonl [--seconds S]
Prints one summary line: lines, SPAN, NOSPAN, TIMEOUT, witness check failures, seconds.
"""
import json, os, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.normpath(os.path.join(HERE, "..", "..", ".."))  # reports/585-next
sys.path.insert(0, os.path.join(ROOT, "wave4", "va6", "tools"))
from span_oracle import spanning_pair  # noqa: E402


def parse_g6(line):
    n = ord(line[0]) - 63
    bits = []
    for ch in line[1:]:
        v = ord(ch) - 63
        bits.extend((v >> (5 - k)) & 1 for k in range(6))
    edges, p = [], 0
    for j in range(1, n):
        for i in range(j):
            if bits[p]:
                edges.append((i, j))
            p += 1
    return n, edges


def check_witness(V, E, cycles):
    """each class: connected 2-regular spanning subgraph of (V, E); classes edge-disjoint."""
    Es = set((min(a, b), max(a, b)) for a, b in E)
    seen = set()
    for cyc in cycles:
        ce = [tuple(sorted(e)) for e in cyc]
        if len(ce) != len(V) or len(set(ce)) != len(ce):
            return False
        if any(e not in Es for e in ce) or any(e in seen for e in ce):
            return False
        seen.update(ce)
        deg = {v: 0 for v in V}
        adj = {v: [] for v in V}
        for a, b in ce:
            if a not in deg or b not in deg:
                return False
            deg[a] += 1; deg[b] += 1
            adj[a].append(b); adj[b].append(a)
        if any(d != 2 for d in deg.values()):
            return False
        start = V[0]; st = [start]; vis = {start}
        while st:
            u = st.pop()
            for w in adj[u]:
                if w not in vis:
                    vis.add(w); st.append(w)
        if len(vis) != len(V):
            return False
    return True


def main():
    inp, outp = sys.argv[1], sys.argv[2]
    secs = 300.0
    if "--seconds" in sys.argv:
        secs = float(sys.argv[sys.argv.index("--seconds") + 1])
    cnt = {"SPAN": 0, "NOSPAN": 0, "TIMEOUT": 0, "witness_fail": 0, "candidate_failure": 0}
    t_all = time.time()
    lines = 0
    with open(outp, "a") as fo:
        for line in open(inp):
            parts = line.split()
            if len(parts) < 3:
                continue
            g6s, o, y = parts[0], int(parts[1]), int(parts[2])
            n, E = parse_g6(g6s)
            V = [v for v in range(n) if v not in (o, y)]
            EY = [(a, b) for a, b in E if a not in (o, y) and b not in (o, y)]
            t0 = time.time()
            r = spanning_pair(V, EY, secs)
            dt = time.time() - t0
            lines += 1
            st = r["status"]
            cnt[st] += 1
            rec = {"g6": g6s, "o": o, "y": y, "status": st, "rounds": r.get("rounds"), "t": round(dt, 4)}
            if st == "SPAN":
                ok = check_witness(V, EY, r["cycles"])
                rec["witness_ok"] = ok
                if not ok:
                    cnt["witness_fail"] += 1
            else:
                sys.path.insert(0, os.path.join(ROOT, "wave5", "s6hunt", "code"))
                from myspan import span2hc  # noqa: E402
                r2 = span2hc(n, EY, secs, vertices=V)
                rec["second_decider"] = {"status": r2["status"], "rounds": r2.get("rounds")}
                if st == "NOSPAN" and r2["status"] == "NOSPAN":
                    cnt["candidate_failure"] += 1
                    rec["CANDIDATE_FAILURE"] = True
                cert = os.path.splitext(outp)[0] + ".cert_%s_%d_%d.json" % (
                    "".join(ch if ch.isalnum() else "_" for ch in g6s)[:40], o, y)
                json.dump({"graph6": g6s, "n": n, "edges": E, "o": o, "y": y, "span_oracle": st,
                           "myspan": r2["status"]}, open(cert, "w"))
            fo.write(json.dumps(rec) + "\n")
            fo.flush()
    print("lines=%d SPAN=%d NOSPAN=%d TIMEOUT=%d witness_fail=%d candidate_failure=%d sec=%.2f" % (
        lines, cnt["SPAN"], cnt["NOSPAN"], cnt["TIMEOUT"], cnt["witness_fail"], cnt["candidate_failure"],
        time.time() - t_all))


if __name__ == "__main__":
    main()
