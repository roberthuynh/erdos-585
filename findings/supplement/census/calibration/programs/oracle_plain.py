#!/usr/bin/env python3
"""pair_oracle.decide with decompose=False (no 4-core or cut reduction) on every graph of a file.
Usage: oracle_plain.py IN.g6 [--seconds 600] [--jobs 6]. Prints one line per graph and a summary."""
import sys, time
from multiprocessing import Pool
sys.path.insert(0, "[local path]")
sys.path.insert(0, "[local path]")
import pair_oracle as po
from crosscheck_oracle import g6_edges, replay
SEC = float(sys.argv[sys.argv.index("--seconds") + 1]) if "--seconds" in sys.argv else 600.0
JOBS = int(sys.argv[sys.argv.index("--jobs") + 1]) if "--jobs" in sys.argv else 6
def work(line):
    n, edges = g6_edges(line)
    t0 = time.monotonic()
    r = po.decide(n, edges, SEC, decompose=False)
    ok = replay(edges, r) if r["status"] == "PAIR" else True
    return line, r["status"], ok, time.monotonic() - t0, r.get("rounds")
if __name__ == "__main__":
    lines = [l.strip() for l in open(sys.argv[1]) if l.strip()]
    cnt = {}
    with Pool(JOBS) as p:
        for line, st, ok, dt, rounds in p.imap(work, lines):
            cnt[st] = cnt.get(st, 0) + 1
            print("%s %s witness_ok=%s rounds=%s %.2fs" % (line, st, ok, rounds, dt), flush=True)
    print("SUMMARY file=%s graphs=%d %s decompose=False seconds_cap=%.0f" % (sys.argv[1], len(lines), cnt, SEC))
