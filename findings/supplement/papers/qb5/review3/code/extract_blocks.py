"""Write both blocks of each instance in blk3 format: 'nA nC masks... [cut vector]'.
usage: extract_blocks.py OUT_WITH_C OUT_ALL FILE...
"""
import sys
from r3lib import parse_g6, decompositions

out_c = open(sys.argv[1], 'w')
out_all = open(sys.argv[2], 'w')
ninst = 0
for fn in sys.argv[3:]:
    for s in open(fn):
        s = s.strip()
        if not s:
            continue
        n, adj = parse_g6(s)
        decs = decompositions(n, adj)
        assert decs
        dec = decs[0]
        ninst += 1
        cutA = {}
        cutD = {}
        for a, d in dec['cut']:
            cutA[a] = cutA.get(a, 0) + 1
            cutD[d] = cutD.get(d, 0) + 1
        for big, small, cut in ((dec['A'], dec['C'], cutA), (dec['D'], dec['B'], cutD)):
            idx = {v: i for i, v in enumerate(big)}
            masks = []
            for c in small:
                m = 0
                for u in adj[c]:
                    m |= 1 << idx[u]
                masks.append(m)
            base = f"{len(big)} {len(small)} " + ' '.join(map(str, masks))
            cv = ' '.join(str(cut.get(v, 0)) for v in big)
            out_c.write(base + ' ' + cv + '\n')
            out_all.write(base + '\n')
print('instances', ninst)
