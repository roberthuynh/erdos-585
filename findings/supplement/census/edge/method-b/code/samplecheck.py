"""samplecheck.py -- deciders compared on members of the real classes (wave8/exb).

For each level, one shard of the whole class (bipgen -P, no pruning) is
streamed and every K-th graph is kept (about 2,000 per level).  Each sampled
graph is decided by h4filt (C search), by PySAT (own CNF) and, for the first
150, by the flow method.  Then each sampled graph is "peeled": random edges
are deleted until the PySAT decider finds no 4-regular subgraph; the last
graph with one and the first graph without one are decided again by all three
(boundary instances at n = 17..19).  Any disagreement is printed; exit 1.
Writes data/SAMPLECHECK.txt.
"""

import os
import random
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, HERE)
import deciders as D  # noqa: E402

BIPGEN = os.path.join(HERE, "bin", "bipgen")
H4FILT = os.path.join(HERE, "bin", "h4filt")

LEVELS = [
    ("n17 e44 8+9", ["8", "9", "44:44", "4:4", "6:6", "3/50"], 120),
    ("n18 e47 8+10", ["10", "8", "47:47", "4:4", "6:6", "5/50"], 80),
    ("n18 e47 9+9", ["9", "9", "47:47", "4:4", "6:6", "77/200"], 5000),
    ("n19 e50 9+10", ["9", "10", "50:50", "4:4", "6:6", "123/2000"], 3000),
    ("n19 e51 9+10 d5", ["10", "9", "51:51", "5:5", "6:6", "7/50"], 100),
]


def c_verdicts(graphs):
    r = subprocess.run([H4FILT, "-a", "-q"], input="\n".join(graphs) + "\n", capture_output=True,
                       text=True, check=True)
    v = [ln.split()[1] == "H" for ln in r.stdout.splitlines()]
    assert len(v) == len(graphs)
    return v


def main():
    rng = random.Random(20261006)
    out = []
    bad = 0
    for name, args, K in LEVELS:
        t0 = time.time()
        p = subprocess.Popen([BIPGEN, "-P", "-q", *args], stdout=subprocess.PIPE,
                             stderr=subprocess.DEVNULL, text=True)
        sample = []
        for i, line in enumerate(p.stdout):
            if i % K == 0:
                sample.append(line.strip())
                if len(sample) >= 2000:
                    break
        p.kill()
        p.wait()
        cv = c_verdicts(sample)
        sv = [D.sat_has_h4(*D.parse_g6(g))[0] for g in sample]
        fv = [D.flow_has_h4(*D.parse_g6(g)) for g in sample[:150]]
        mis_cs = sum(a != b for a, b in zip(cv, sv))
        mis_fs = sum(a != b for a, b in zip(fv, sv[:150]))
        # peeling
        last_with, first_without = [], []
        for g in sample:
            n, edges = D.parse_g6(g)
            edges = list(edges)
            if not D.sat_has_h4(n, edges)[0]:
                continue
            rng.shuffle(edges)
            while True:
                cand = edges[:-1]
                if D.sat_has_h4(n, cand)[0]:
                    edges = cand
                    continue
                last_with.append(D.to_g6(n, edges))
                first_without.append(D.to_g6(n, cand))
                break
        bnd = last_with + first_without
        expect = [True] * len(last_with) + [False] * len(first_without)
        cb = c_verdicts(bnd)
        mis_cb = sum(a != b for a, b in zip(cb, expect))
        fb = [D.flow_has_h4(*D.parse_g6(g)) for g in bnd[:100]] + \
             [D.flow_has_h4(*D.parse_g6(g)) for g in first_without[:40]]
        fe = expect[:100] + [False] * min(40, len(first_without))
        mis_fb = sum(a != b for a, b in zip(fb, fe))
        bad += mis_cs + mis_fs + mis_cb + mis_fb
        avg_e = sum(len(D.parse_g6(g)[1]) for g in first_without) / max(1, len(first_without))
        line = (f"{name}: shard {args[-1]} every {K}th graph: {len(sample)} sampled, with H {sum(sv)} "
                f"(C vs SAT mismatches {mis_cs}; flow vs SAT on 150: {mis_fs}); peeled boundary pairs "
                f"{len(last_with)} (first graph without H has {avg_e:.1f} edges on average; "
                f"C vs expected mismatches {mis_cb}; flow vs expected on {len(fb)}: {mis_fb}) "
                f"[{time.time() - t0:.0f} s]")
        print(line, flush=True)
        out.append(line)
        with open(os.path.join(ROOT, "data", "samplecheck_boundary_" + name.replace(" ", "_") + ".g6"),
                  "w") as f:
            f.write("\n".join(f"{g} {'H' if e else '0'}" for g, e in zip(bnd, expect)) + "\n")
    out.append("SAMPLECHECK " + ("PASS" if bad == 0 else f"FAIL ({bad})"))
    print(out[-1])
    with open(os.path.join(ROOT, "data", "SAMPLECHECK.txt"), "w") as f:
        f.write("\n".join(out) + "\n")
    return 0 if bad == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
