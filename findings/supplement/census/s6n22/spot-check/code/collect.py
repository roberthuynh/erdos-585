#!/usr/bin/env python3
"""collect.py (wave8/s6spot): compare every finished slice with wave6/s6n22's per-slice records.

For each job in data/jobs.txt with a done marker:
  mine:     genbg's own count (>Z line), lines in s<r>.g6, e10cut's min-cut histogram,
            spantest's counts (E10, tests, SPAN, NO, witness failures, decoder hash mismatches)
  original: wave6/s6n22/data/shards/<r/100>/s<r>.sum (graphs, e10, non_e10, tests, mincut_hist)
            and s<r>.genbg.err (>Z line)
  content:  every graph6 string in the original's s<r>.stall file must occur in my s<r>.g6
Writes data/collect.json and data/compare.md (markdown tables), prints a one-line verdict.
"""
import json, os, re, pathlib

D = pathlib.Path(__file__).resolve().parent.parent
ORIG = D.parent.parent / "wave6" / "s6n22" / "data" / "shards"


def kv(path):
    out = {}
    for line in open(path):
        if "=" in line:
            k, v = line.rstrip("\n").split("=", 1)
            out[k] = v
    return out


def zcount(path):
    m = re.search(r">Z (\d+) graphs", open(path).read())
    return int(m.group(1)) if m else None


def hist_str(h):
    return ",".join("%s:%s" % (k, h[k]) for k in sorted(h, key=lambda x: int(x)))


def main():
    jobs = [l.split() for l in open(D / "data" / "jobs.txt") if l.strip()]
    rows, tot = [], dict(slices_full=0, graphs=0, e10=0, tests=0, span=0, no=0, witness_fail=0,
                         mismatches=0, sec_genbg=0, sec_e10=0, sec_span=0)
    special = []
    for r, mode in jobs:
        r = int(r)
        P = D / "data" / "slices" / ("s%d" % r)
        if not os.path.exists(str(P) + ".done"):
            continue
        done = dict(x.split("=") for x in open(str(P) + ".done").read().split())
        my_z = zcount(str(P) + ".genbg.err")
        my_lines = sum(1 for _ in open(str(P) + ".g6"))
        sj = json.load(open(str(P) + ".span.json"))
        o = kv(ORIG / str(r // 100) / ("s%d.sum" % r))
        o_z = zcount(ORIG / str(r // 100) / ("s%d.genbg.err" % r))
        o_hist = {k: v for k, v in (x.split(":") for x in o["mincut_hist"].strip(",").split(",") if x)}
        my_hist = {str(k): str(v) for k, v in sj["mincut_hist"].items()}
        stall = [l.split()[0] for l in open(ORIG / str(r // 100) / ("s%d.stall" % r)) if l.strip()]
        mine_set = set(l.strip() for l in open(str(P) + ".g6"))
        stall_found = sum(1 for g in stall if g in mine_set)
        row = dict(r=r, mode=mode, my_genbg=my_z, my_lines=my_lines, orig_genbg=o_z,
                   orig_graphs=int(o["graphs"]), my_graphs=sj["graphs"],
                   my_e10=sj["e10"], orig_e10=int(o["e10"]), my_non_e10=sj["non_e10"],
                   orig_non_e10=int(o["non_e10"]), my_hist=hist_str(my_hist),
                   orig_hist=hist_str(o_hist), orig_tests=int(o["tests"]),
                   my_tests=sj.get("tests", 0), my_span=sj.get("span", 0), my_no=sj.get("no", 0),
                   witness_fail=sj["witness_fail"], hash_mismatch=sj["hash_mismatch"],
                   stall_lines=len(stall), stall_found=stall_found,
                   sec_genbg=int(done["genbg_s"]), sec_e10=int(done["e10_s"]),
                   sec_span=int(done["span_s"]), non_e10_graphs=sj["non_e10_graphs"])
        ok = (my_z == my_lines == o_z == row["orig_graphs"] == row["my_graphs"]
              and row["my_e10"] == row["orig_e10"] and row["my_non_e10"] == row["orig_non_e10"]
              and my_hist == o_hist and stall_found == len(stall) and row["hash_mismatch"] == 0)
        if mode == "full":
            ok = ok and (row["my_tests"] == 66 * row["my_e10"] == row["orig_tests"]
                         and row["my_span"] == row["my_tests"] and row["my_no"] == 0
                         and row["witness_fail"] == 0)
        row["match"] = ok
        tot["mismatches"] += (not ok)
        if mode == "full":
            tot["slices_full"] += 1
            for k in ("graphs", "e10", "tests", "span", "no", "witness_fail"):
                tot[k] += row["my_" + k] if ("my_" + k) in row else row[k]
            for k in ("sec_genbg", "sec_e10", "sec_span"):
                tot[k] += row[k]
        else:
            special.append(row)
        rows.append(row)
    tot["census_graphs"] = 156473848
    tot["fraction_graphs"] = tot["graphs"] / 156473848
    tot["fraction_slices"] = tot["slices_full"] / 10000
    json.dump(dict(rows=rows, totals=tot), open(D / "data" / "collect.json", "w"), indent=1)
    with open(D / "data" / "compare.md", "w") as f:
        f.write("| slice | graphs: genbg now / lines / s6n22 sum / s6n22 genbg | E10 now / s6n22 | "
                "min-cut hist now = s6n22 | stall g6 found | tests now / s6n22 | SPAN | NO | "
                "witness fail | match |\n|---|---|---|---|---|---|---|---|---|---|\n")
        for w in rows:
            f.write("| %d%s | %s / %s / %s / %s | %s / %s | %s %s | %d/%d | %s / %s | %s | %s | %s | %s |\n" % (
                w["r"], "" if w["mode"] == "full" else " (E10 only)", w["my_genbg"], w["my_lines"],
                w["orig_graphs"], w["orig_genbg"], w["my_e10"], w["orig_e10"], w["my_hist"],
                "=" if w["my_hist"] == w["orig_hist"] else "!= " + w["orig_hist"],
                w["stall_found"], w["stall_lines"], w["my_tests"] if w["mode"] == "full" else "-",
                w["orig_tests"], w["my_span"] if w["mode"] == "full" else "-",
                w["my_no"] if w["mode"] == "full" else "-", w["witness_fail"],
                "yes" if w["match"] else "NO"))
    print("collect: slices_full=%d graphs=%d e10=%d tests=%d span=%d no=%d witness_fail=%d "
          "special=%d mismatched_rows=%d fraction=%.6f" % (
              tot["slices_full"], tot["graphs"], tot["e10"], tot["tests"], tot["span"], tot["no"],
              tot["witness_fail"], len(special), tot["mismatches"], tot["fraction_graphs"]))


if __name__ == "__main__":
    main()
