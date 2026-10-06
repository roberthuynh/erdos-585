"""graph6 helpers (n <= 62) and small graph utilities for the qb5 lane."""


def decode(s):
    s = s.strip()
    n = ord(s[0]) - 63
    adj = [set() for _ in range(n)]
    bits = []
    for ch in s[1:]:
        v = ord(ch) - 63
        for b in range(5, -1, -1):
            bits.append((v >> b) & 1)
    k = 0
    for j in range(1, n):
        for i in range(j):
            if bits[k]:
                adj[i].add(j)
                adj[j].add(i)
            k += 1
    return n, adj


def encode(n, edges):
    E = set()
    for a, b in edges:
        if a == b:
            raise ValueError("loop")
        E.add((min(a, b), max(a, b)))
    bits = []
    for j in range(1, n):
        for i in range(j):
            bits.append(1 if (i, j) in E else 0)
    while len(bits) % 6:
        bits.append(0)
    out = chr(n + 63)
    for k in range(0, len(bits), 6):
        v = 0
        for b in bits[k:k + 6]:
            v = 2 * v + b
        out += chr(v + 63)
    return out


def edges_of(n, adj):
    return [(i, j) for i in range(n) for j in adj[i] if i < j]
