"""Run blocksig (C) for one block and write the same cache format as b2_block.py.
Usage: b2_block_c.py <edges file> <block index> <cache dir> [blocksize] [--compare <python cache dir>]
With --compare, also checks that the signature set and the local colouring count equal those in
an existing Python-made cache (the C port is only trusted where it reproduces Python)."""
import os
import pickle
import subprocess
import sys
from collections import defaultdict

from common import load_edges, adjacency
from pairdp import Block

args = sys.argv[1:]
cmp_dir = None
if "--compare" in args:
    i = args.index("--compare")
    cmp_dir = args[i + 1]
    args = args[:i] + args[i + 2:]
path, k, cache = args[0], int(args[1]), args[2]
s = int(args[3]) if len(args) > 3 else 13
E = load_edges(path)
n = 1 + max(x for e in E for x in e)
verts = list(range(s * k, s * k + s))
blk = Block(n, E, adjacency(n, E), verts, None)
here = os.path.dirname(os.path.abspath(__file__))
out = subprocess.run([os.path.join(here, "blocksig"), path, str(s * k), str(s)],
                     capture_output=True, text=True, check=True).stdout.splitlines()
cnt = int(out[0].split()[1])
local = list(map(int, out[1].split()[1:]))
boundary = list(map(int, out[2].split()[1:]))
assert local == blk.local, "local edge order differs from Python"
assert boundary == blk.boundary, "boundary order differs from Python"
d = defaultdict(dict)
for line in out[3:]:
    body = line[4:]
    bcol_s, rp_s, rc_s, bp_s, bc_s, wit = body.split("|")
    bcol = tuple(int(x) for x in bcol_s.split(",")) if bcol_s else ()

    def pairs(t):
        if not t:
            return ()
        return tuple(tuple(int(y) for y in x.split("-")) for x in t.split(","))
    key = (pairs(rp_s), int(rc_s), pairs(bp_s), int(bc_s))
    d[bcol][key] = {ei: int(c) for ei, c in zip(local, wit)}
d = dict(d)
os.makedirs(cache, exist_ok=True)
with open(os.path.join(cache, "block_%d.pkl" % k), "wb") as f:
    pickle.dump({"verts": verts, "boundary": boundary, "sigs": d, "count": cnt}, f)
msg = "block %d (C port): %d local colourings, %d boundary colourings, %d signatures" % (
    k, cnt, len(d), sum(len(x) for x in d.values()))
if cmp_dir:
    py = pickle.load(open(os.path.join(cmp_dir, "block_%d.pkl" % k), "rb"))
    same_count = py["count"] == cnt
    same_sigs = {b: set(v) for b, v in py["sigs"].items()} == {b: set(v) for b, v in d.items()}
    msg += "; matches Python cache %s: count %s, signatures %s" % (cmp_dir, same_count, same_sigs)
    assert same_count and same_sigs
print(msg, flush=True)
