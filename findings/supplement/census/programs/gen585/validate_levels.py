#!/usr/bin/env python3
"""Independent cross-check of gen585 level sets and final sets.

Generator side A: nauty geng (independent generator) with degree/edge bounds, then
  - pair filter: LANE/tools/pair_oracle.decide (SAT) or the C test (gen585 -p) when --fast,
  - sparsity filter in Python: e(S) <= 3|S| - SP for all S with |S| >= SPMIN
    (S = V excluded when --final),
  - --mindeg for the final level.
Side B: gen585 with -d LEVEL (dump), look-ahead disabled (-L) unless --final.
Both lists are canonicalized with nauty labelg and compared as sets.

Example (level 8 of the N = 13 S10 tree, e in [14, 19]):
  timeout 240 python3 validate_levels.py --N 13 --EF 35 --SP 5 --SPMIN 2 --MINDF 4 --level 8 --emin 14 --emax 19
"""
import argparse, os, subprocess, sys
from itertools import combinations

HERE = os.path.dirname(os.path.abspath(__file__))
LANE = os.path.dirname(os.path.dirname(HERE))
NAUTY = os.path.join(HERE, "nauty2_8_9")
sys.path.insert(0, os.path.join(LANE, "tools"))


def parse_g6(line):
    s = line.strip()
    data = [ord(c) - 63 for c in s]
    n = data[0]
    bits = []
    for d in data[1:]:
        for k in range(5, -1, -1):
            bits.append((d >> k) & 1)
    edges = []
    idx = 0
    for j in range(1, n):
        for i in range(j):
            if bits[idx]:
                edges.append((i, j))
            idx += 1
    return n, edges


def to_g6(n, edges):
    E = set(edges)
    bits = []
    for j in range(1, n):
        for i in range(j):
            bits.append(1 if (i, j) in E or (j, i) in E else 0)
    while len(bits) % 6:
        bits.append(0)
    out = chr(n + 63)
    for k in range(0, len(bits), 6):
        v = 0
        for b in bits[k:k + 6]:
            v = (v << 1) | b
        out += chr(v + 63)
    return out


def sparse_ok(n, edges, SP, SPMIN, final):
    adj = [0] * n
    for a, b in edges:
        adj[a] |= 1 << b
        adj[b] |= 1 << a
    full = (1 << n) - 1
    eT = [0] * (1 << n)
    for T in range(1, 1 << n):
        u = (T & -T).bit_length() - 1
        rest = T & (T - 1)
        eT[T] = eT[rest] + bin(adj[u] & rest).count("1")
        sz = bin(T).count("1")
        if sz < SPMIN or (final and T == full):
            continue
        if eT[T] > 3 * sz - SP:
            return False
    return True


def canon(g6_lines):
    if not g6_lines:
        return set()
    r = subprocess.run([os.path.join(NAUTY, "labelg"), "-q"], input="\n".join(g6_lines) + "\n",
                       capture_output=True, text=True, check=True)
    return set(r.stdout.split())


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--N", type=int, required=True)
    ap.add_argument("--EF", type=int, required=True)
    ap.add_argument("--SP", type=int, required=True)
    ap.add_argument("--SPMIN", type=int, required=True)
    ap.add_argument("--MINDF", type=int, default=4)
    ap.add_argument("--level", type=int, required=True)
    ap.add_argument("--emin", type=int, required=True)
    ap.add_argument("--emax", type=int, required=True)
    ap.add_argument("--final", action="store_true", help="level == N: min degree MINDF, S = V exempt")
    ap.add_argument("--fast", action="store_true", help="use the C pair test instead of pair_oracle")
    args = ap.parse_args()
    k = args.level
    geng = [os.path.join(NAUTY, "geng"), "-q", "-D6"]
    if args.final:
        geng.append("-d%d" % args.MINDF)
    geng += [str(k), "%d:%d" % (args.emin, args.emax)]
    raw = subprocess.run(geng, capture_output=True, text=True, check=True).stdout.split()
    graphs = [parse_g6(l) for l in raw]
    # sparsity first (cheap), then pair test; in --fast mode the C pair filter runs first
    if not args.fast:
        graphs = [(n, E) for n, E in graphs if sparse_ok(n, E, args.SP, args.SPMIN, args.final)]
    if args.fast:
        inp = "".join("%d %d %s\n" % (n, len(E), " ".join("%d %d" % e for e in E)) for n, E in graphs)
        out = subprocess.run([os.path.join(HERE, "gen585"), "-p"], input=inp, capture_output=True, text=True,
                             check=True).stdout.split()
        keep = [g for g, c in zip(graphs, out) if c == "0"]
        keep = [(n, E) for n, E in keep if sparse_ok(n, E, args.SP, args.SPMIN, args.final)]
        import pair_oracle
        for n, E in keep:
            assert pair_oracle.decide(n, E, seconds=60)["status"] == "NOPAIR", "C filter kept a pair graph"
    else:
        import pair_oracle
        keep = []
        for n, E in graphs:
            r = pair_oracle.decide(n, E, seconds=60)
            if r["status"] == "TIMEOUT":
                raise SystemExit("oracle timeout")
            if r["status"] == "NOPAIR":
                keep.append((n, E))
    A = canon([to_g6(n, E) for n, E in keep])
    cmd = [os.path.join(HERE, os.environ.get("GEN", "gen585")), str(args.N), str(args.EF), str(args.SP), str(args.SPMIN),
           str(args.MINDF), "-d", str(k), "-S", str(k)]
    if not args.final:
        cmd.append("-L")
    out = subprocess.run(cmd, capture_output=True, text=True, check=True).stdout.splitlines()
    dumped = []
    for line in out:
        if line.startswith("STATUS") or line.startswith("level") or line.startswith("FINAL"):
            continue
        parts = list(map(int, line.split()))
        n, m = parts[0], parts[1]
        E = [(parts[2 + 2 * i], parts[3 + 2 * i]) for i in range(m)]
        if args.emin <= m <= args.emax:
            dumped.append(to_g6(n, E))
    B = canon(dumped)
    print("geng total %d, after sparsity %d, avoiders kept %d (canonical %d)" % (len(raw), len(graphs), len(keep),
                                                                                len(A)))
    print("gen585 dumped %d (canonical %d, duplicates %d)" % (len(dumped), len(B), len(dumped) - len(B)))
    print("A-B %d  B-A %d  -> %s" % (len(A - B), len(B - A), "MATCH" if A == B else "MISMATCH"))


if __name__ == "__main__":
    main()
