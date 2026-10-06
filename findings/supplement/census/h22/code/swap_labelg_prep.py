#!/usr/bin/env python3
"""wave4/h22b: cross-check of hdq's colour-swap flag with nauty labelg (sample only).

For each hdq output line (<g6> H|C ... with the swap flag), writes the graph twice, relabelled so
that one side comes first (A-first) and then the other side first (B-first). labelg with the
partition string a^(n/2) b^(n/2) then gives the canonical form of the 2-coloured graph; the two
canonical forms are equal iff some automorphism exchanges the sides.

usage: swap_labelg_prep.py OUTPREFIX FILE...   writes OUTPREFIX.A.g6, OUTPREFIX.B.g6, OUTPREFIX.flags
"""
import gzip
import sys


def parse_g6(s):
    n = ord(s[0]) - 63
    bits = []
    for ch in s[1:]:
        v = ord(ch) - 63
        for sh in range(5, -1, -1):
            bits.append((v >> sh) & 1)
    adj = [set() for _ in range(n)]
    k = 0
    for j in range(1, n):
        for i in range(j):
            if bits[k]:
                adj[i].add(j)
                adj[j].add(i)
            k += 1
    return n, adj


def to_g6(n, adj):
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


def relabel(n, adj, order):
    pos = {v: i for i, v in enumerate(order)}
    nadj = [set() for _ in range(n)]
    for v in range(n):
        for w in adj[v]:
            nadj[pos[v]].add(pos[w])
    return nadj


def main(prefix, files):
    fa = open(prefix + ".A.g6", "w")
    fb = open(prefix + ".B.g6", "w")
    ff = open(prefix + ".flags", "w")
    for fn in files:
        op = gzip.open if fn.endswith(".gz") else open
        with op(fn, "rt") as fh:
            for line in fh:
                p = line.split()
                if len(p) < 4 or p[1] not in ("H", "C"):
                    continue
                n, adj = parse_g6(p[0])
                side = [-1] * n
                side[0] = 0
                stack = [0]
                while stack:
                    v = stack.pop()
                    for w in adj[v]:
                        if side[w] < 0:
                            side[w] = 1 - side[v]
                            stack.append(w)
                A = [v for v in range(n) if side[v] == 0]
                B = [v for v in range(n) if side[v] == 1]
                fa.write(to_g6(n, relabel(n, adj, A + B)) + "\n")
                fb.write(to_g6(n, relabel(n, adj, B + A)) + "\n")
                ff.write(p[3] + "\n")
    fa.close(); fb.close(); ff.close()


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2:])
