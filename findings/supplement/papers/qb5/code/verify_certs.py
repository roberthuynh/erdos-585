"""Independent checks for the qb5 lane (Python + networkx; shares no code with petal.c / clcheck.c).

Usage: verify_certs.py MODE < file.g6
  c2core : every C2 instance has a good W-vertex; for u0 instances a good W-vertex off N(u0), for
           u1u2 instances a good port. Good = G - w has a 4-factor (max flow, capacities 4).
  e5     : E5 instance: e = 3n - 5, Delta <= 6, sparse (brute force), no 4-factor (max flow), the
           violation from a minimum cut has the block structure of Theorem 6.1 (k = 2, 7 cut edges,
           g(X) = g(Y) = 12), and the cut has matching number <= 3 (networkx max matching).
  sparse : brute-force sparsity (every S with 3 <= |S| <= n - 1 spans <= 3|S| - 6 edges).
Exit status 1 on any failed claim.
"""
import sys
import networkx as nx
from g6 import decode


def sides(n, adj):
    col = [-1] * n
    col[0] = 0
    st = [0]
    while st:
        v = st.pop()
        for u in adj[v]:
            if col[u] < 0:
                col[u] = 1 - col[v]
                st.append(u)
            elif col[u] == col[v]:
                raise ValueError("not bipartite")
    if min(col) < 0:
        raise ValueError("disconnected")
    return col


def sparse(n, adj):
    """min over 3 <= |S| <= n-1 of 6|S| - 2e(S) is >= 12 (bytearray DP over all subsets)."""
    A = [sum(1 << u for u in adj[v]) for v in range(n)]
    full = (1 << n) - 1
    e = bytearray(1 << n)
    for S in range(1, full + 1):
        lo = (S & -S).bit_length() - 1
        rest = S & (S - 1)
        e[S] = e[rest] + bin(A[lo] & rest).count("1")
        if S != full:
            k = bin(S).count("1")
            if k >= 3 and e[S] > 3 * k - 6:
                return False
    return True


def has4factor(adj, col, keep):
    P = [v for v in keep if col[v] == 0]
    Q = [v for v in keep if col[v] == 1]
    if len(P) != len(Q) or not P:
        return False
    F = nx.DiGraph()
    for p in P:
        F.add_edge("s", p, capacity=4)
        for q in adj[p]:
            if q in keep:
                F.add_edge(p, q, capacity=1)
    for q in Q:
        F.add_edge(q, "t", capacity=4)
    return nx.maximum_flow_value(F, "s", "t") == 4 * len(P)


def violation_set(adj, col, keep):
    """A minimum s-t cut of the 4-factor flow network; returns (A, C): A = P-vertices on the
    source side, C = Q-vertices on the sink side complement, i.e. the Hall-type violation."""
    P = [v for v in keep if col[v] == 0]
    Q = [v for v in keep if col[v] == 1]
    F = nx.DiGraph()
    for p in P:
        F.add_edge("s", p, capacity=4)
        for q in adj[p]:
            if q in keep:
                F.add_edge(p, q, capacity=1)
    for q in Q:
        F.add_edge(q, "t", capacity=4)
    val, (S, T) = nx.minimum_cut(F, "s", "t")
    A = [p for p in P if p in S]
    C = [q for q in Q if q in S]
    return val, A, C


def main():
    mode = sys.argv[1]
    bad = 0
    count = 0
    for line in sys.stdin:
        line = line.strip()
        if not line:
            continue
        count += 1
        n, adj = decode(line)
        col = sides(n, adj)
        deg = [len(adj[v]) for v in range(n)]
        e = sum(deg) // 2
        V = set(range(n))
        if mode == "sparse":
            if not sparse(n, adj):
                bad += 1
                print("NOT SPARSE", line)
            continue
        if mode == "c2core":
            c0 = [v for v in V if col[v] == 0]
            c1 = [v for v in V if col[v] == 1]
            U, W = (c0, c1) if len(c0) < len(c1) else (c1, c0)
            DU = sum(6 - deg[u] for u in U)
            ok_c2 = len(W) == len(U) + 1 and DU == 2 and max(deg) <= 6
            if not ok_c2:
                bad += 1
                print("NOT C2", line)
                continue
            Z = [u for u in U if deg[u] < 6]
            if len(Z) == 1:
                cand = [w for w in W if w not in adj[Z[0]]]
                kind = "u0"
            else:
                cand = [w for w in W if deg[w] <= 5]
                kind = "u1u2"
            good = [w for w in cand if has4factor(adj, col, V - {w})]
            if not good:
                bad += 1
                print("NO GOOD VERTEX", kind, line)
            continue
        if mode == "e5":
            c0 = [v for v in V if col[v] == 0]
            ok = len(c0) * 2 == n and e == 3 * n - 5 and max(deg) <= 6
            if not ok:
                bad += 1
                print("NOT E5", line)
                continue
            if not sparse(n, adj):
                bad += 1
                print("NOT SPARSE", line)
                continue
            if has4factor(adj, col, V):
                bad += 1
                print("HAS 4-FACTOR", line)
                continue
            val, A, C = violation_set(adj, col, V)
            # deficiency 4s - val; the violation: A on source side among P, C among Q on source side
            X = set(A) | set(C)
            k = len(A) - len(C)
            eX = sum(1 for v in X for u in adj[v] if u in X) // 2
            gX = 6 * len(X) - 2 * eX
            Y = V - X
            eY = sum(1 for v in Y for u in adj[v] if u in Y) // 2
            gY = 6 * len(Y) - 2 * eY
            cut = [(a, d) for a in X for d in adj[a] if d in Y]
            M = nx.Graph()
            M.add_edges_from(cut)
            nu = len(nx.max_weight_matching(M, maxcardinality=True))
            if not (4 * len(c0) - val == 1 and gX == 12 and gY == 12 and len(cut) == 7 and abs(k) == 2 and nu <= 3):
                bad += 1
                print("E5 STRUCTURE FAIL", line, val, k, gX, gY, len(cut), nu)
            continue
        raise SystemExit("unknown mode")
    print("mode %s: %d graphs, %d failures" % (mode, count, bad))
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
