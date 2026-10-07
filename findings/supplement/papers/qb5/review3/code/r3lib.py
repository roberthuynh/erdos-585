"""Referee-3 library, written from scratch: graph6, Dinic, E5 block decompositions, demands, I_X(M).

Nothing here imports or reads the author's code.
"""
import sys
from itertools import combinations


def parse_g6(s):
    s = s.strip()
    if s.startswith('>>graph6<<'):
        s = s[10:]
    data = [ord(ch) - 63 for ch in s]
    if data[0] < 63:
        n = data[0]
        pos = 1
    else:
        n = (data[1] << 12) | (data[2] << 6) | data[3]
        pos = 4
    bits = []
    for x in data[pos:]:
        for k in range(5, -1, -1):
            bits.append((x >> k) & 1)
    adj = [set() for _ in range(n)]
    idx = 0
    for j in range(1, n):
        for i in range(j):
            if bits[idx]:
                adj[i].add(j)
                adj[j].add(i)
            idx += 1
    return n, adj


def to_g6(n, adj):
    bits = []
    for j in range(1, n):
        for i in range(j):
            bits.append(1 if j in adj[i] else 0)
    while len(bits) % 6:
        bits.append(0)
    out = [chr(n + 63)] if n < 63 else None
    for k in range(0, len(bits), 6):
        v = 0
        for b in bits[k:k + 6]:
            v = (v << 1) | b
        out.append(chr(v + 63))
    return ''.join(out)


def two_color(n, adj):
    col = [-1] * n
    for s in range(n):
        if col[s] >= 0:
            continue
        col[s] = 0
        st = [s]
        while st:
            u = st.pop()
            for v in adj[u]:
                if col[v] < 0:
                    col[v] = 1 - col[u]
                    st.append(v)
                elif col[v] == col[u]:
                    raise ValueError('not bipartite')
    return col


class Dinic:
    def __init__(self, n):
        self.n = n
        self.g = [[] for _ in range(n)]

    def add(self, u, v, c):
        self.g[u].append([v, c, len(self.g[v])])
        self.g[v].append([u, 0, len(self.g[u]) - 1])

    def maxflow(self, s, t):
        flow = 0
        n = self.n
        while True:
            level = [-1] * n
            level[s] = 0
            q = [s]
            for u in q:
                for v, c, _ in self.g[u]:
                    if c > 0 and level[v] < 0:
                        level[v] = level[u] + 1
                        q.append(v)
            if level[t] < 0:
                return flow
            it = [0] * n

            def dfs(u, f):
                if u == t:
                    return f
                while it[u] < len(self.g[u]):
                    e = self.g[u][it[u]]
                    v, c, r = e
                    if c > 0 and level[v] == level[u] + 1:
                        d = dfs(v, min(f, c))
                        if d > 0:
                            e[1] -= d
                            self.g[v][r][1] += d
                            return d
                    it[u] += 1
                return 0
            while True:
                f = dfs(s, 10 ** 9)
                if f == 0:
                    break
                flow += f


def has_k_factor(n, adj, side, removed, k=4):
    """side[v] in {0,1}; removed: set of vertices. 4-factor of the rest via flow."""
    L = [v for v in range(n) if v not in removed and side[v] == 0]
    R = [v for v in range(n) if v not in removed and side[v] == 1]
    if len(L) != len(R):
        return False
    S, T = n, n + 1
    D = Dinic(n + 2)
    for u in L:
        D.add(S, u, k)
        for v in adj[u]:
            if v not in removed:
                D.add(u, v, 1)
    for v in R:
        D.add(v, T, k)
    return D.maxflow(S, T) == k * len(L)


def decompositions(n, adj):
    """All (P-orientation) 2-block decompositions as in PAPER.md Thm 6.1:
    A subset P, C = {q in Q: deg 6, N(q) subset A}, |A| = |C| + 2, e(A, Q - C) = 7,
    B = P - A, D = Q - C, every b in B has deg 6 and N(b) subset D.  Returns list of dicts."""
    col = two_color(n, adj)
    res = []
    for pside in (0, 1):
        P = [v for v in range(n) if col[v] == pside]
        Q = [v for v in range(n) if col[v] != pside]
        if len(P) != len(Q):
            continue
        idx = {v: i for i, v in enumerate(P)}
        nbmask = {}
        for q in Q:
            m = 0
            for u in adj[q]:
                m |= 1 << idx[u]
            nbmask[q] = m
        for Am in range(1, 1 << len(P)):
            C = [q for q in Q if len(adj[q]) == 6 and (nbmask[q] & ~Am) == 0]
            A = [P[i] for i in range(len(P)) if Am >> i & 1]
            if len(A) != len(C) + 2:
                continue
            Cs = set(C)
            As = set(A)
            cut = [(a, d) for a in A for d in adj[a] if d not in Cs]
            if len(cut) != 7:
                continue
            B = [v for v in P if v not in As]
            D = [v for v in Q if v not in Cs]
            okB = all(len(adj[b]) == 6 and all(x in D for x in adj[b]) for b in B)
            if not okB:
                continue
            res.append(dict(P=P, Q=Q, A=A, C=C, B=B, D=D, cut=cut, pside=pside))
    return res


def block_demands(big, small, adj):
    """big: list of big-side vertices (A), small: list (C). dem[mask] for all masks over big."""
    nb = len(big)
    idx = {v: i for i, v in enumerate(big)}
    cm = []
    for c in small:
        m = 0
        for u in adj[c]:
            if u in idx:
                m |= 1 << idx[u]
        cm.append(m)
    dem = [0] * (1 << nb)
    for mask in range(1 << nb):
        s = 0
        for m in cm:
            x = bin(m & mask).count('1')
            s += 4 if x > 4 else x
        dem[mask] = 4 * bin(mask).count('1') - s
    return dem


def I_of(dem, mvec, nb):
    """mvec[i] = m(v_i). Returns I = intersection of under-supplied masks (as mask)."""
    full = (1 << nb) - 1
    I = full
    # m(mask) via incremental DP
    msum = [0] * (1 << nb)
    for mask in range(1, 1 << nb):
        low = mask & -mask
        i = low.bit_length() - 1
        msum[mask] = msum[mask ^ low] + mvec[i]
        if msum[mask] < dem[mask]:
            I &= mask
    return I
