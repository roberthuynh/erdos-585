#!/usr/bin/env python3
"""Validate every FINAL graph reported by gen585 (a claimed avoider) with the lane's tools.

For each FINAL line: check n, edge count, degree bounds; then run LANE/tools/brute.decide and
LANE/tools/pair_oracle.decide. A true counterexample must get NOPAIR from both. If either finds a
pair, the certificate is checked with LANE/tools/validate.check and the graph is reported as a
false positive of gen585's pair test (which would be a bug to fix, not a counterexample).

Run: timeout 240 [temporary path] validate_finals.py runs/finals_<tag>.txt [EF] [MINDEG]
"""
import json, os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
LANE = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, os.path.join(LANE, "tools"))
import brute, pair_oracle, validate  # noqa: E402


def main():
    path = sys.argv[1]
    EF = int(sys.argv[2]) if len(sys.argv) > 2 and sys.argv[2] else None
    mindeg = int(sys.argv[3]) if len(sys.argv) > 3 else 4
    lines = [l for l in open(path) if l.startswith("FINAL")]
    print("FINAL lines:", len(lines))
    for l in lines:
        head, es = l.split("edges:")
        n = int(head.split("n=")[1])
        E = [tuple(map(int, t.split("-"))) for t in es.split()]
        deg = [0] * n
        for a, b in E:
            deg[a] += 1
            deg[b] += 1
        info = {"n": n, "m": len(E), "mindeg": min(deg), "maxdeg": max(deg)}
        ok_shape = max(deg) <= 6 and min(deg) >= mindeg and (EF is None or len(E) == EF)
        rb = brute.decide(n, E)
        ro = pair_oracle.decide(n, E, seconds=200)
        for r, name in ((rb, "brute"), (ro, "oracle")):
            if r["status"] == "PAIR":
                ok, msg = validate.check(E, r["cycles"][0], r["cycles"][1])
                info[name] = "PAIR (certificate %s: %s)" % ("valid" if ok else "INVALID", msg)
            else:
                info[name] = r["status"]
        info["shape_ok"] = ok_shape
        info["counterexample"] = ok_shape and rb["status"] == "NOPAIR" and ro["status"] == "NOPAIR"
        print(json.dumps(info), "edges:", E)


if __name__ == "__main__":
    main()
