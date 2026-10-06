"""Referee's own helpers for PAPER2 checks: graph6 parsing, Dinic max flow, E5 decompositions,
demands, genericity (Definition 3.2), the pair criterion (Theorem 2.2) and the covering rule
(Lemma 4.2 / Corollary 3.4).  No code shared with qb5/code/."""
from itertools import combinations
from collections import deque


def g6_decode(line):
    s = line.strip()
    data = [ord(ch) - 63 for ch in s]
    if data[0] == 63:
        raise ValueError("large graph6 not supported")
    n = data[0]
    bits = []
    for x in data[1:]:
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


def g6_encode(n, adj):
    bits = []
    for j in range(1, n):
        for i in range(j):
            bits.append(1 if j in adj[i] else 0)
    while len(bits) % 6:
        bits.append(0)
    out = [chr(n + 63)]
    for k in range(0, len(bits), 6):
        v = 0
        for b in bits[k:k + 6]:
            v = 2 * v + b
        out.append(chr(v + 63))
    return "".join(out)


def bipartition(n, adj):
    col = [-1] * n
    for s in range(n):
        if col[s] != -1:
            continue
        col[s] = 0
        dq = deque([s])
        while dq:
            u = dq.popleft()
            for w in adj[u]:
                if col[w] == -1:
                    col[w] = 1 - col[u]
                    dq.append(w)
                elif col[w] == col[u]:
                    return None
    return col


class Dinic:
    def __init__(self, n):
        self.n = n
        self.g = [[] for _ in range(n)]

    def add(self, u, v, c):
        self.g[u].append([v, c, len(self.g[v])])
        self.g[v].append([u, 0, len(self.g[u]) - 1])

    def bfs(self, s, t):
        self.lvl = [-1] * self.n
        self.lvl[s] = 0
        dq = deque([s])
        while dq:
            u = dq.popleft()
            for v, c, _ in self.g[u]:
                if c > 0 and self.lvl[v] < 0:
                    self.lvl[v] = self.lvl[u] + 1
                    dq.append(v)
        return self.lvl[t] >= 0

    def dfs(self, u, t, f):
        if u == t:
            return f
        while self.it[u] < len(self.g[u]):
            e = self.g[u][self.it[u]]
            v, c, r = e
            if c > 0 and self.lvl[v] == self.lvl[u] + 1:
                d = self.dfs(v, t, min(f, c))
                if d > 0:
                    e[1] -= d
                    self.g[v][r][1] += d
                    return d
            self.it[u] += 1
        return 0

    def maxflow(self, s, t):
        flow = 0
        while self.bfs(s, t):
            self.it = [0] * self.n
            while True:
                f = self.dfs(s, t, 10 ** 9)
                if f == 0:
                    break
                flow += f
        return flow


def has_4factor(n, adj, col, removed=()):
    """4-factor of G - removed, by max flow (sides by col)."""
    rem = set(removed)
    P = [v for v in range(n) if col[v] == 0 and v not in rem]
    Q = [v for v in range(n) if col[v] == 1 and v not in rem]
    if len(P) != len(Q):
        return False, 0, 0
    S, T = n, n + 1
    D = Dinic(n + 2)
    for u in P:
        D.add(S, u, 4)
        for w in adj[u]:
            if w not in rem:
                D.add(u, w, 1)
    for w in Q:
        D.add(w, T, 4)
    f = D.maxflow(S, T)
    return f == 4 * len(P), f, 4 * len(P)


def is_sparse_small(n, adj):
    """exhaustive subset DP; only for n <= 26 or so (2^n ints)."""
    raise NotImplementedError


def violations(n, adj, col, side=0):
    """All A subset of side `side` with min_C slack < 0 (Lemma 1.5), with the C attaining it.
    Returns list of (A, C, slack) with C = {c : e(A, c) >= 5} (strictly better than 4 when > 4)."""
    P = [v for v in range(n) if col[v] == side]
    Q = [v for v in range(n) if col[v] != side]
    res = []
    idx = {v: i for i, v in enumerate(P)}
    for mask in range(1, 1 << len(P)):
        A = {P[i] for i in range(len(P)) if mask >> i & 1}
        eAQ = sum(len(adj[a]) for a in A)
        slack = eAQ - 4 * len(A)
        C = set()
        for c in Q:
            x = len(adj[c] & A)
            if x > 4:
                slack -= (x - 4)
                C.add(c)
        if slack < 0:
            res.append((frozenset(A), frozenset(C), slack))
    return res


def decompositions(n, adj, col):
    """2-block decompositions from violations with A on side 0 (P).  Each gives
    X = A u C, Y = rest, B = P - A, D = Q - C."""
    out = []
    for A, C, sl in violations(n, adj, col, 0):
        P = {v for v in range(n) if col[v] == 0}
        Q = {v for v in range(n) if col[v] == 1}
        B = P - A
        Dd = Q - C
        out.append((A, C, B, frozenset(Dd), sl))
    return out


class Block:
    """Data of one E5 decomposition: A, C, B, D, cut, in-block degrees, L sets."""

    def __init__(self, n, adj, A, C, B, D):
        self.n, self.adj = n, adj
        self.A, self.C, self.B, self.D = set(A), set(C), set(B), set(D)
        self.cut = [(a, d) for a in self.A for d in adj[a] if d in self.D]
        self.c = {}
        for v in self.A | self.D:
            self.c[v] = sum(1 for (a, d) in self.cut if v in (a, d))
        self.din = {}
        for a in self.A:
            self.din[a] = len(adj[a] & self.C)
        for d in self.D:
            self.din[d] = len(adj[d] & self.B)
        self.LA = {a for a in self.A if self.din[a] == 3}
        self.LD = {d for d in self.D if self.din[d] == 3}

    def check_structure(self):
        adj = self.adj
        ok = True
        ok &= len(self.A) == len(self.C) + 2 and len(self.D) == len(self.B) + 2
        ok &= all(len(adj[c]) == 6 and adj[c] <= self.A for c in self.C)
        ok &= all(len(adj[b]) == 6 and adj[b] <= self.D for b in self.B)
        ok &= len(self.cut) == 7
        ok &= sum(6 - len(adj[a]) for a in self.A) == 5 and sum(6 - len(adj[d]) for d in self.D) == 5
        return ok

    def demX(self, A1):
        A1 = set(A1)
        return 4 * len(A1) - sum(min(4, len(self.adj[c] & A1)) for c in self.C)

    def demY(self, D1):
        D1 = set(D1)
        return 4 * len(D1) - sum(min(4, len(self.adj[b] & D1)) for b in self.B)

    def e_AD(self, A1, D1):
        return sum(1 for (a, d) in self.cut if a in A1 and d in D1)

    def nongeneric_witnesses(self, side, p):
        """Definition 3.2: list of p-relevant A1 (|A1| <= |A| - 2) with dem > |A1 & L|."""
        if side == 'X':
            big, L, dem = self.A, self.LA, self.demX
        else:
            big, L, dem = self.D, self.LD, self.demY
        rest = sorted(big - {p})
        wit = []
        for r in range(0, len(big) - 1):
            for A1 in combinations(rest, r):
                A1s = set(A1)
                k = dem(A1s)
                crest = sum(self.c[v] for v in big - {p} - A1s)
                if k + crest >= 5 and k > len(A1s & L):
                    wit.append((frozenset(A1s), k))
        return wit

    def criterion(self, p, q):
        """Theorem 2.2: all A1 subset A - p, D1 subset D - q: demX + demY <= 4 + e(A1, D1)."""
        Ar = sorted(self.A - {p})
        Dr = sorted(self.D - {q})
        dX = []
        for r in range(len(Ar) + 1):
            for A1 in combinations(Ar, r):
                dX.append((set(A1), self.demX(A1)))
        dY = []
        for r in range(len(Dr) + 1):
            for D1 in combinations(Dr, r):
                dY.append((set(D1), self.demY(D1)))
        for A1, x in dX:
            for D1, y in dY:
                if x + y > 4 + self.e_AD(A1, D1):
                    return False, (A1, D1, x, y)
        return True, None

    def covering(self, p, q):
        """Lemma 4.2 / Cor. 3.4 covering rule: some M subset E - E(p) - E(q), |M| = 4,
        covering (L_A - p) | (L_D - q).  Direct search."""
        F = [(a, d) for (a, d) in self.cut if a != p and d != q]
        need = (self.LA - {p}) | (self.LD - {q})
        for M in combinations(F, 4):
            cov = set()
            for a, d in M:
                cov.add(a)
                cov.add(d)
            if need <= cov:
                return True, M
        return False, None
