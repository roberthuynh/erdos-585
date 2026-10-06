#!/usr/bin/env python3
"""wave4/h22b: sum the shard summaries in OUTDIR/done/ (one line per shard, written by run_shard.sh).

usage: collect.py OUTDIR MOD
Prints totals of every hdq counter, geng's own count, the colour-preserving count 2U - S,
the colour-preserving count of 2-cut graphs 2C - swapC, and the shard wall-time total.
"""
import os
import re
import sys


def main(outdir, mod):
    done_dir = os.path.join(outdir, "done")
    names = sorted((f for f in os.listdir(done_dir) if f.isdigit()), key=int)
    missing = sorted(set(range(mod)) - {int(f) for f in names})
    tot = {}
    wall = 0
    maxima = {}
    for f in names:
        line = open(os.path.join(done_dir, f)).read().strip()
        kv = dict(re.findall(r"(\w+)=(\d+)", line))
        for k, v in kv.items():
            if k == "res":
                continue
            v = int(v)
            if k.startswith("max"):
                maxima[k] = max(maxima.get(k, 0), v)
            elif k == "wall":
                wall += v
            else:
                tot[k] = tot.get(k, 0) + v
    U, S = tot.get("graphs", 0), tot.get("swap", 0)
    C, SC = tot.get("C", 0), tot.get("swapC", 0)
    print(f"shards_done={len(names)}/{mod} missing={missing[:20]}{'...' if len(missing) > 20 else ''}")
    print("totals " + " ".join(f"{k}={v}" for k, v in tot.items()))
    print("maxima " + " ".join(f"{k}={v}" for k, v in maxima.items()))
    print(f"geng_total={tot.get('geng', 0)} uncolored_U={U} swap_S={S} colour_preserving_2U-S={2 * U - S}")
    print(f"cut_graphs_C={C} swapC={SC} colour_preserving_2C-swapC={2 * C - SC}")
    print(f"HD={tot.get('H', 0)} colour_preserving_HD={2 * tot.get('H', 0) - (S - SC)} X={tot.get('X', 0)} E={tot.get('E', 0)}")
    print(f"shard_wall_sum_s={wall}")
    return 0 if not missing else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1], int(sys.argv[2])))
