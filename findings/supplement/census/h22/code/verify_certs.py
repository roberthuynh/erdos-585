#!/usr/bin/env python3
"""wave4/h22b: independent re-check of hdq output (own graph6 parser, no code shared with hdq.c).

Line types checked:
  <g6> H <hexmask> <sw>              the graph is 4-regular, connected, bipartite with equal sides,
                                     and the red edges (mask bits over edge ids, graph6 bit order)
                                     and the blue edges (the rest) are both Hamilton cycles
  <g6> C a-b,c-d <sw> <dec>          4-regular, connected, bipartite with equal sides, ab and cd are
                                     edges, and G - ab - cd is disconnected
  <g6> X ... / <g6> E ...            counted and listed (they are exceptions or errors)
Also counts the swap flags and, per type, the number of lines.

usage: verify_certs.py FILE... (plain or .gz); prints one summary line; exit 1 on any failure.
"""
import gzip
import sys


def parse_g6(s):
    n = ord(s[0]) - 63
    if not (1 <= n <= 62):
        raise ValueError("n")
    need = n * (n - 1) // 2
    data = s[1:]
    if len(data) != (need + 5) // 6:
        raise ValueError("length")
    bits = []
    for ch in data:
        v = ord(ch) - 63
        if not (0 <= v <= 63):
            raise ValueError("char")
        for sh in range(5, -1, -1):
            bits.append((v >> sh) & 1)
    edges = []
    k = 0
    for j in range(1, n):
        for i in range(j):
            if bits[k]:
                edges.append((i, j))
            k += 1
    return n, edges


def connected(n, edges):
    adj = [[] for _ in range(n)]
    for a, b in edges:
        adj[a].append(b)
        adj[b].append(a)
    seen = [False] * n
    seen[0] = True
    stack = [0]
    cnt = 1
    while stack:
        v = stack.pop()
        for w in adj[v]:
            if not seen[w]:
                seen[w] = True
                cnt += 1
                stack.append(w)
    return cnt == n


def basic(n, edges):
    deg = [0] * n
    adj = [[] for _ in range(n)]
    for a, b in edges:
        deg[a] += 1
        deg[b] += 1
        adj[a].append(b)
        adj[b].append(a)
    if any(d != 4 for d in deg):
        return "notreg4"
    if not connected(n, edges):
        return "disconnected"
    col = [-1] * n
    col[0] = 0
    stack = [0]
    while stack:
        v = stack.pop()
        for w in adj[v]:
            if col[w] < 0:
                col[w] = 1 - col[v]
                stack.append(w)
            elif col[w] == col[v]:
                return "notbipartite"
    if 2 * col.count(0) != n:
        return "unequal"
    return None


def is_ham_cycle(n, cyc_edges):
    if len(cyc_edges) != n:
        return False
    deg = [0] * n
    for a, b in cyc_edges:
        deg[a] += 1
        deg[b] += 1
    if any(d != 2 for d in deg):
        return False
    return connected(n, cyc_edges)


def main(files):
    counts = {"H": 0, "C": 0, "X": 0, "E": 0}
    sw = {"H": 0, "C": 0}
    fails = []
    total = 0
    for fn in files:
        op = gzip.open if fn.endswith(".gz") else open
        with op(fn, "rt") as fh:
            for line in fh:
                parts = line.split()
                if not parts:
                    continue
                total += 1
                g6, typ = parts[0], parts[1]
                counts[typ] = counts.get(typ, 0) + 1
                if typ in ("X", "E"):
                    if typ == "E":
                        fails.append(f"{fn} {line.strip()}")
                    print("LISTED", fn, line.strip())
                    continue
                n, edges = parse_g6(g6)
                err = basic(n, edges)
                if err:
                    fails.append(f"{fn} {g6} {typ} basic:{err}")
                    continue
                if typ == "H":
                    mask = int(parts[2], 16)
                    if mask >> len(edges):
                        fails.append(f"{fn} {g6} H mask_out_of_range")
                        continue
                    red = [e for k, e in enumerate(edges) if (mask >> k) & 1]
                    blue = [e for k, e in enumerate(edges) if not (mask >> k) & 1]
                    if not (is_ham_cycle(n, red) and is_ham_cycle(n, blue)):
                        fails.append(f"{fn} {g6} H not_a_decomposition")
                        continue
                    sw["H"] += parts[3] == "1"
                elif typ == "C":
                    cut = []
                    for tok in parts[2].split(","):
                        a, b = map(int, tok.split("-"))
                        cut.append((min(a, b), max(a, b)))
                    eset = set(edges)
                    if len(cut) != 2 or cut[0] == cut[1] or any(c not in eset for c in cut):
                        fails.append(f"{fn} {g6} C bad_cut_edges")
                        continue
                    rest = [e for e in edges if e not in cut]
                    if connected(n, rest):
                        fails.append(f"{fn} {g6} C not_a_cut")
                        continue
                    sw["C"] += parts[3] == "1"
                else:
                    fails.append(f"{fn} {g6} unknown_type {typ}")
    for f in fails[:50]:
        print("FAIL", f)
    print(f"verify_certs lines={total} H={counts['H']} C={counts['C']} X={counts['X']} E={counts['E']} "
          f"swapH={sw['H']} swapC={sw['C']} failures={len(fails)}")
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
