"""B2 phase 1: local colourings and signatures of one block of a graph, cached to disk.
Usage: b2_block.py <edges file> <block index> <cache dir> [blocksize]
Blocks are {s*k, ..., s*k + s - 1} with s = blocksize (default 13)."""
import os
import pickle
import sys
import time
from collections import Counter

from common import load_edges, adjacency
from pairdp import Block, local_signatures

path, k, cache = sys.argv[1], int(sys.argv[2]), sys.argv[3]
s = int(sys.argv[4]) if len(sys.argv) > 4 else 13
E = load_edges(path)
n = 1 + max(x for e in E for x in e)
adj = adjacency(n, E)
verts = list(range(s * k, s * k + s))
t0 = time.time()
blk = Block(n, E, adj, verts, None)
d, cnt = local_signatures(blk)
# breakdown by boundary pattern and internal cycles, from the signatures' own enumeration
kinds = Counter()
for bcol, keys in d.items():
    nr = sum(1 for c in bcol if c == 1)
    nb = sum(1 for c in bcol if c == 2)
    for key in keys:
        kinds[(nr, nb, key[1], key[3])] += 1
os.makedirs(cache, exist_ok=True)
with open(os.path.join(cache, "block_%d.pkl" % k), "wb") as f:
    pickle.dump({"verts": verts, "boundary": blk.boundary, "sigs": d, "count": cnt}, f)
with open(os.path.join(cache, "block_%d.txt" % k), "w") as f:
    f.write("block %d vertices %d..%d: %d internal + %d boundary edges, %d local colourings, "
            "%d boundary colourings, %d signatures, %.1fs\n"
            % (k, verts[0], verts[-1], len(blk.internal), len(blk.boundary), cnt, len(d),
               sum(len(x) for x in d.values()), time.time() - t0))
    f.write("signatures by (red boundary, blue boundary, internal red cycles capped at 2, internal blue cycles capped at 2): %s\n"
            % dict(sorted(kinds.items())))
    f.write("boundary colourings (0 unused, 1 red, 2 blue), boundary edge order %s:\n" % [E[ei] for ei in blk.boundary])
    for bcol in sorted(d):
        f.write("  %s: %d signatures\n" % (bcol, len(d[bcol])))
print(open(os.path.join(cache, "block_%d.txt" % k)).read().splitlines()[0], flush=True)
