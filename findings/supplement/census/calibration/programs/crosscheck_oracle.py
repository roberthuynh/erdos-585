#!/usr/bin/env python3
"""B-1 cross-check: decide every graph of a graph6 file with pair_oracle.py (SAT, PySAT) and
compare with pairc's pair-free list.

  python crosscheck_oracle.py IN.g6 PAIRC_FREE.g6 OUT_PREFIX [--jobs 6] [--seconds 120]

Each PAIR answer is replayed here without pair_oracle code: the support S is nonempty, both cycles
visit every vertex of S exactly once and close up, consecutive vertices are adjacent in G, and the
two cycles share no edge. Writes OUT_PREFIX.nopair.g6, OUT_PREFIX.timeout.g6, OUT_PREFIX.summary.txt.
Exit 0 only if no TIMEOUT, every witness replays, and NOPAIR == pairc pair-free (as sets of lines).
"""
import os, sys, time
from multiprocessing import Pool

sys.path.insert(0, "[local path]")
import pair_oracle as po  # noqa: E402

SECONDS = 120.0


def g6_edges(line):
    n = ord(line[0]) - 63
    bits = []
    for ch in line[1:]:
        v = ord(ch) - 63
        bits.extend((v >> (5 - k)) & 1 for k in range(6))
    edges, t = [], 0
    for j in range(1, n):
        for i in range(j):
            if bits[t]:
                edges.append((i, j))
            t += 1
    return n, edges


def replay(edges, r):
    E = set(edges)
    S = set(r["support"])
    if not S:
        return False
    used = set()
    for cyc in r["cycles"]:
        if len(cyc) != len(S) or set(cyc) != S or len(cyc) < 3:
            return False
        for a, b in zip(cyc, cyc[1:] + cyc[:1]):
            e = (min(a, b), max(a, b))
            if e not in E or e in used:
                return False
            used.add(e)
    return True


def work(line):
    n, edges = g6_edges(line)
    t0 = time.monotonic()
    r = po.decide(n, edges, SECONDS, decompose=True)
    dt = time.monotonic() - t0
    ok = True
    if r["status"] == "PAIR":
        ok = replay(edges, r)
    return line, r["status"], ok, dt


def main():
    global SECONDS
    inp, pairc_free, prefix = sys.argv[1:4]
    jobs = 6
    if "--jobs" in sys.argv:
        jobs = int(sys.argv[sys.argv.index("--jobs") + 1])
    if "--seconds" in sys.argv:
        SECONDS = float(sys.argv[sys.argv.index("--seconds") + 1])
    lines = [l.strip() for l in open(inp) if l.strip() and not l.startswith(">")]
    free_c = set(l.strip() for l in open(pairc_free) if l.strip())
    t0 = time.time()
    cnt = {"PAIR": 0, "NOPAIR": 0, "TIMEOUT": 0}
    bad_witness, nopair, timeout, tmax = [], [], [], 0.0
    with Pool(jobs, initializer=_init, initargs=(SECONDS,)) as pool:
        for k, (line, st, ok, dt) in enumerate(pool.imap(work, lines, chunksize=64), 1):
            cnt[st] += 1
            tmax = max(tmax, dt)
            if st == "PAIR" and not ok:
                bad_witness.append(line)
            elif st == "NOPAIR":
                nopair.append(line)
            elif st == "TIMEOUT":
                timeout.append(line)
            if k % 5000 == 0:
                print("progress %d/%d %s elapsed=%.0fs" % (k, len(lines), cnt, time.time() - t0), flush=True)
    open(prefix + ".nopair.g6", "w").write("".join(l + "\n" for l in nopair))
    open(prefix + ".timeout.g6", "w").write("".join(l + "\n" for l in timeout))
    sn = set(nopair)
    agree = (sn == free_c)
    summary = ("input=%s graphs=%d PAIR=%d NOPAIR=%d TIMEOUT=%d bad_witness=%d pairc_free=%d "
               "nopair_not_pairc=%d pairc_not_nopair=%d agree=%s max_s=%.2f wall_s=%.0f seconds_cap=%.0f\n") % (
        os.path.basename(inp), len(lines), cnt["PAIR"], cnt["NOPAIR"], cnt["TIMEOUT"], len(bad_witness),
        len(free_c), len(sn - free_c), len(free_c - sn), agree, tmax, time.time() - t0, SECONDS)
    open(prefix + ".summary.txt", "w").write(summary)
    print(summary, end="")
    sys.exit(0 if (agree and not timeout and not bad_witness) else 1)


def _init(sec):
    global SECONDS
    SECONDS = sec


if __name__ == "__main__":
    main()
