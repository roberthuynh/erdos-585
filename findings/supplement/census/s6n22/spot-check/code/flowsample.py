#!/usr/bin/env python3
"""flowsample.py (wave8/s6spot): second method for the E10 check on a random subset.
For every finished full slice, pick K graph indices (random.Random(SEED + r)) and recompute their
minimum essential cut by max-flow (validate.flow); also every graph that e10cut found non-E10 in
any finished slice. Usage: flowsample.py [K]. Output on stdout."""
import sys, os, random, glob, io, contextlib
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import validate
D = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "data")
K = int(sys.argv[1]) if len(sys.argv) > 1 else 2
SEED = 7
jobs = [l.split() for l in open(os.path.join(D, "jobs.txt")) if l.strip()]
tot = agree = 0
for r, mode in jobs:
    P = os.path.join(D, "slices", "s" + r)
    if not os.path.exists(P + ".done"):
        continue
    cuts = [l.split() for l in open(P + ".cut")]
    idx = [int(c[0]) for c in cuts if int(c[1]) < 10]
    if mode == "full":
        idx += random.Random(SEED + int(r)).sample(range(len(cuts)), min(K, len(cuts)))
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf):
        validate.flow(P + ".g6", P + ".cut", idx)
    for line in buf.getvalue().splitlines():
        if line.startswith("graph"):
            tot += 1
            agree += line.endswith(" agree")
            print("slice %s %s" % (r, line))
print("FLOW_SAMPLE %d/%d agree" % (agree, tot))
