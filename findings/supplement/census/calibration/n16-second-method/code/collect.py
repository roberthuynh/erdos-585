#!/usr/bin/env python3
"""Sum the per-shard results of one tag (logs/<tag>/) and cross-check the counts.

A shard counts as covered only if: its .done marker exists, geng's >Z count equals the number of
graph6 lines in the shard file, equals the number of graphs the decider read, and pair + nopair
equals that number with no verify failure, no decode mismatch and no degree mismatch.
Usage: collect.py <tag> [<n>]
"""
import glob
import json
import os
import re
import sys

LANE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
tag = sys.argv[1]
want_n = sys.argv[2] if len(sys.argv) > 2 else None
rows = []
tot = {"shards": 0, "covered": 0, "graphs": 0, "pair": 0, "nopair": 0, "verify_fail": 0,
       "decode_mismatch": 0, "degree_mismatch": 0, "cpu_seconds": 0.0, "geng_s": 0,
       "decide_s": 0}
hist = {}
bad = []
nopair_files = []
for meta in sorted(glob.glob(os.path.join(LANE, "logs", tag, "*.meta"))):
    base = meta[:-5]
    m = dict(kv.split("=", 1) for kv in open(meta).read().split())
    if want_n and m["n"] != want_n:
        continue
    tot["shards"] += 1
    z = None
    for line in open(base + ".geng.err"):
        mm = re.match(r">Z (\d+) graphs generated", line)
        if mm:
            z = int(mm.group(1))
    s = json.load(open(base + ".summary.json"))
    ok = (os.path.exists(base + ".done") and z is not None and z == int(m["g6_lines"])
          == s["graphs"] and s["pair"] + s["nopair"] == s["graphs"] and s["verify_fail"] == 0
          and s["decode_mismatch"] == 0 and s["degree_mismatch"] == 0)
    if not ok:
        bad.append(os.path.basename(base))
        continue
    tot["covered"] += 1
    for k in ("graphs", "pair", "nopair", "verify_fail", "decode_mismatch", "degree_mismatch"):
        tot[k] += s[k]
    tot["cpu_seconds"] += s["cpu_seconds"]
    tot["geng_s"] += int(m["geng_s"])
    tot["decide_s"] += int(m["decide_s"])
    for k, v in s["S_size_hist"].items():
        hist[k] = hist.get(k, 0) + v
    if s["nopair"]:
        nopair_files.append(base + ".nopair.g6")
    rows.append((m["n"], int(m["res"]), int(m["mod"]), z, s["pair"], s["nopair"]))
tot["cpu_seconds"] = round(tot["cpu_seconds"], 1)
out = {"tag": tag, "n": want_n, "totals": tot, "cycle_length_hist": dict(sorted(hist.items(), key=lambda kv: int(kv[0]))),
       "not_covered": bad, "nopair_files": nopair_files,
       "shards": [{"n": r[0], "res": r[1], "mod": r[2], "graphs": r[3], "pair": r[4], "nopair": r[5]} for r in rows]}
dst = os.path.join(LANE, "logs", "%s%s.collected.json" % (tag, "_n" + want_n if want_n else ""))
with open(dst, "w") as f:
    json.dump(out, f, indent=1)
    f.write("\n")
print(json.dumps({"totals": tot, "cycle_length_hist": out["cycle_length_hist"], "not_covered": bad,
                  "nopair_files": nopair_files}))
