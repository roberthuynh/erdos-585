"""gencheck.py -- validate bipgen (own generator) against nauty genbg 2.9.3.

For many small classes, compares the number of bicoloured graphs:
  bipgen -P -u n1 n2 e1:e2 dA:dB DA:DB      (whole class, own generator)
  genbg  -u -d dA:dB -D DA:DB n1 n2 e1:e2    (nauty, reference count)
and, for classes where both prune modes are cheap, the pruned output
  bipgen n1 n2 ...   (graphs with no 4-regular subgraph)
against the whole class filtered by h4filt, compared as sets of canonical
forms (labelg) after forgetting colours where the class sizes differ.
Also checks that every res/mod split sums to the unsplit count.
Usage: python gencheck.py [quick|full]
"""

import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
BIN = os.path.join(HERE, "bin")
NAUTY = os.path.expanduser("~/.cache/erdos585/nauty2_9_3")
GENBG = os.path.join(NAUTY, "genbg")
LABELG = os.path.join(NAUTY, "labelg")


def zcount(stderr):
    m = re.search(r">Z\s+(\d+) graphs", stderr)
    if not m:
        raise RuntimeError("no >Z line: " + stderr[-300:])
    return int(m.group(1))


def bipgen(args, extra=()):
    r = subprocess.run([os.path.join(BIN, "bipgen"), *extra, *args], capture_output=True,
                       text=True, timeout=600)
    if r.returncode:
        raise RuntimeError(r.stderr)
    return r.stdout, zcount(r.stderr)


def genbg_count(n1, n2, e, d, D):
    r = subprocess.run([GENBG, "-u", "-d" + d, "-D" + D, str(n1), str(n2), e],
                       capture_output=True, text=True, timeout=600)
    if "impossible mine,maxe,mindeg,maxdeg" in r.stderr:
        return 0  # genbg refuses classes it can see are empty
    return zcount(r.stderr)


def canon(g6text):
    r = subprocess.run([LABELG, "-q"], input=g6text, capture_output=True, text=True)
    return sorted(r.stdout.split())


def main():
    mode = sys.argv[1] if len(sys.argv) > 1 else "quick"
    cases = []
    for n1 in range(2, 8):
        for n2 in range(1, 8):
            for d, D in (("0:1", "3:3"), ("1:1", "4:4"), ("2:2", "4:3"), ("1:2", "3:5"),
                         ("2:3", "5:5"), ("3:3", "5:6"), ("0:0", "6:6")):
                cases.append((n1, n2, "0:%d" % (n1 * n2), d, D))
    for n1, n2, e in ((7, 7, "28:42"), (7, 8, "28:42"), (8, 7, "28:42"), (6, 9, "36:36"),
                      (8, 8, "32:35"), (7, 9, "32:36")):
        cases.append((n1, n2, e, "4:4", "6:6"))
    cases += [(8, 8, "40:42", "5:5", "6:6"), (7, 8, "36:40", "5:4", "6:6"),
              (8, 7, "36:40", "4:5", "6:6"), (6, 6, "0:36", "0:0", "6:6")]
    if mode == "full":
        cases += [(8, 8, "36:40", "4:4", "6:6"), (8, 9, "40:41", "4:4", "6:6"),
                  (9, 8, "40:41", "4:4", "6:6")]
    bad = 0
    total = 0
    for n1, n2, e, d, D in cases:
        try:
            _, b = bipgen([str(n1), str(n2), e, d, D], ("-P", "-u", "-q"))
        except RuntimeError as ex:
            print("bipgen error", n1, n2, e, d, D, ex)
            bad += 1
            continue
        g = genbg_count(n1, n2, e, d, D)
        total += 1
        if b != g:
            bad += 1
            print(f"MISMATCH n1={n1} n2={n2} e={e} d={d} D={D}: bipgen {b}, genbg {g}")
    print(f"class counts: {total} classes compared, {bad} mismatches")

    # res/mod splits
    for n1, n2, e, d, D, L in ((7, 8, "28:42", "4:4", "6:6", 3), (7, 7, "28:42", "4:4", "6:6", 4),
                               (6, 7, "0:42", "1:1", "4:4", 2)):
        _, whole = bipgen([str(n1), str(n2), e, d, D], ("-P", "-u", "-q"))
        parts = [bipgen([str(n1), str(n2), e, d, D, f"{r}/7"], ("-P", "-u", "-q", "-l", str(L)))[1]
                 for r in range(7)]
        ok = sum(parts) == whole
        bad += not ok
        print(f"split {n1}+{n2} {e} {d} {D} level {L}: parts {parts} sum {sum(parts)} whole {whole} "
              f"{'OK' if ok else 'MISMATCH'}")

    # pruned output vs whole class filtered by h4filt (canonical forms with colours kept:
    # relabel is identical since both list A first; compare uncoloured canonical forms,
    # valid because each class here has n1 != n2 or is compared as multisets)
    for n1, n2, e, d, D in ((7, 7, "28:42", "4:4", "6:6"), (7, 8, "28:42", "4:4", "6:6"),
                            (6, 9, "36:36", "4:4", "6:6"), (8, 8, "32:35", "4:4", "6:6"),
                            (7, 9, "32:36", "4:4", "6:6")):
        pr_out, pr_n = bipgen([str(n1), str(n2), e, d, D], ("-q",))
        whole_out, whole_n = bipgen([str(n1), str(n2), e, d, D], ("-P", "-q"))
        f = subprocess.run([os.path.join(BIN, "h4filt"), "-q"], input=whole_out,
                           capture_output=True, text=True)
        filt = f.stdout
        nf = len(filt.split())
        same = canon(pr_out) == canon(filt)
        bad += (nf != pr_n) or not same
        print(f"prune check {n1}+{n2} e={e} d={d} D={D}: whole {whole_n}, whole filtered {nf}, "
              f"pruned {pr_n}, same multiset of uncoloured canonical forms: {same}")
    print("GENCHECK", "PASS" if bad == 0 else f"FAIL ({bad})")
    return 0 if bad == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
