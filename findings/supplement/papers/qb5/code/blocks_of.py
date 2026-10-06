"""Extract both 2-blocks of sparse E5 instances in blockkl.c format (lane qb5, round 3).

Line format: "na nc mask_1 ... mask_nc" (mask_j = neighbours in A of the j-th small-side vertex).
For the Y block the roles are D (big side) and B (small side).
Usage: blocks_of.py FILE.g6 > blocks.txt
"""
import sys

from g6 import decode
from e5pairs import bip, structure


def block_line(big, small, adj):
    big = sorted(big)
    idx = {v: i for i, v in enumerate(big)}
    masks = []
    for c in sorted(small):
        m = 0
        for v in adj[c]:
            if v in idx:
                m |= 1 << idx[v]
        masks.append(m)
    return '%d %d %s' % (len(big), len(small), ' '.join(map(str, masks)))


def main():
    for line in open(sys.argv[1]):
        g = line.split()[0] if line.strip() else ''
        if not g:
            continue
        n, adj = decode(g)
        side = bip(n, adj)
        st = structure(n, adj, side)
        if st is None:
            continue
        A, C, B, D, _ = st
        print(block_line(A, C, adj))
        print(block_line(D, B, adj))


if __name__ == '__main__':
    main()
