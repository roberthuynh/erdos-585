#!/usr/bin/env python3
"""pick_sample.py (wave8/s6spot): fixed random order of the 10,000 slices r/10000.
The spot-check runs slices in this order and stops at its budget, so whatever completes is a
prefix of one recorded uniform random permutation.

The seed is drawn once from os.urandom and recorded in data/sample_seed.txt; with that file
present the order is rebuilt from the recorded seed (reproducible). A first attempt with seed
20261006 reproduced wave6/s6n22/data/order.txt exactly (same seed and method), so a fresh seed
is used to keep the sample independent of the original's processing order.
Writes data/sample_order.txt (one slice id per line)."""
import os, random, pathlib
D = pathlib.Path(__file__).resolve().parent.parent / "data"
sf = D / "sample_seed.txt"
if sf.exists():
    seed = int(sf.read_text().split()[0])
else:
    seed = int.from_bytes(os.urandom(4), "big")
    sf.write_text(f"{seed}\n")
order = list(range(10000))
random.Random(seed).shuffle(order)
(D / "sample_order.txt").write_text("".join(f"{r}\n" for r in order))
print("seed", seed, "first 40:", order[:40])
