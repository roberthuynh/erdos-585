"""B2 phase 2: global combination of cached block signatures (exact; see pairdp.py).
Usage: b2_combine.py <edges file> <cache dir> <number of blocks> [blocksize]"""
import os
import pickle
import sys
import time

from common import load_edges, adjacency
from pairdp import Block, find_pair, describe_pair

path, cache, nblocks = sys.argv[1], sys.argv[2], int(sys.argv[3])
s = int(sys.argv[4]) if len(sys.argv) > 4 else 13
E = load_edges(path)
n = 1 + max(x for e in E for x in e)
assert n == s * nblocks
blocks = [list(range(s * k, s * k + s)) for k in range(nblocks)]
pre = []
for k in range(nblocks):
    with open(os.path.join(cache, "block_%d.pkl" % k), "rb") as f:
        dat = pickle.load(f)
    assert dat["verts"] == blocks[k]
    assert dat["boundary"] == Block(n, E, adjacency(n, E), blocks[k], None).boundary
    pre.append((dat["sigs"], dat["count"]))
t0 = time.time()
pair, st = find_pair(n, E, blocks, precomputed=pre, stop_at_first=True, verbose=True)
print("graph %s, %d blocks of %d" % (os.path.basename(path), nblocks, s))
print("local colourings per block:", st["local_colourings"])
print("boundary colourings per block:", st["bcols"])
print("signatures per block before the sound filter:", st["signatures_before_filter"])
print("signatures per block after the sound filter:", st["signatures"])
print("boundary-consistent assignments reached:", st["consistent_boundary_assignments"])
print("signature combinations checked:", st["signature_combinations_checked"])
print("combine time %.1fs" % (time.time() - t0))
if pair is None:
    print("RESULT: NO PAIR (exhaustive)")
else:
    ok, msg, r, b = describe_pair(n, E, pair)
    print("RESULT: PAIR FOUND; independent verify_pair: %s (%s)" % (ok, msg))
    print("red cycle  (%d vertices): %s" % (len(r), r))
    print("blue cycle (%d vertices): %s" % (len(b), b))
