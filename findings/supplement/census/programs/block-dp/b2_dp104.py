"""B2: exact pair test of data/bip5-avoider-104.edges by the block DP (pairdp.py).

Partition: the 8 blocks {13k, ..., 13k+12}. The DP is exact for any partition (see pairdp.py),
so this choice only affects running time. Also prints, for each block, the breakdown of local
colourings by boundary pattern, as an independent look at how a pair can meet one copy.
"""
import sys
import time
from collections import Counter

from common import EDGES_104, load_edges, adjacency
from pairdp import Block, find_pair, describe_pair

log = open("b2_dp104.log", "w")


def say(s):
    print(s, flush=True)
    log.write(s + "\n")
    log.flush()


E = load_edges(EDGES_104)
n = 104
blocks = [list(range(13 * k, 13 * k + 13)) for k in range(8)]

# breakdown of local colourings for every block
adj = adjacency(n, E)
t0 = time.time()
for k in range(8):
    blk = Block(n, E, adj, blocks[k], None)
    kinds = Counter()
    total = 0
    for col in blk.enumerate_local():
        total += 1
        s = blk.signature(col)
        bcol, rp, rc, bp, bc = s
        nr = sum(1 for c in bcol if c == 1)
        nb = sum(1 for c in bcol if c == 2)
        insideS = any(col[li] != 0 for li in range(len(blk.local)))
        kinds[(nr, nb, rc, bc, insideS)] += 1
    say("block %d: %d local colourings (including the empty one); breakdown by "
        "(red boundary, blue boundary, internal red cycles, internal blue cycles, meets S): %s"
        % (k, total, dict(sorted(kinds.items()))))
say("breakdown time %.1fs" % (time.time() - t0))

t0 = time.time()
pair, st = find_pair(n, E, blocks, verbose=True, log=log, stop_at_first=True)
say("DP stats: %s" % st)
say("DP time %.1fs" % (time.time() - t0))
if pair is None:
    say("RESULT: no pair (exhaustive block DP over all local colourings and all boundary-consistent combinations)")
else:
    ok, msg, r, b = describe_pair(n, E, pair)
    say("RESULT: PAIR FOUND, verify=%s (%s)" % (ok, msg))
    say("red cycle:  %s" % r)
    say("blue cycle: %s" % b)
