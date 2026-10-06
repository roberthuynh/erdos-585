#!/usr/bin/env python3
"""collect.py -- sum the shard outputs of the s6n22 run into RESULT.md (wave6/s6n22).

Reads data/shards/*/s<r>.sum for every slice r with a done marker, plus the SAT logs, and writes
RESULT.md, data/slices_done.txt (sorted slice list) and data/stall_frames.txt (all stall lines of
the done slices, merged). Run any time; it only reads finished slices.
Usage: collect.py [--no-merge]
"""
import glob, json, os, re, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
D = os.path.normpath(os.path.join(HERE, ".."))
MOD = 10000
INT_KEYS = ["graphs", "bad_input", "e10", "non_e10", "tests", "dfs1_solved", "am_fallback_solved", "dfs2_solved",
            "ams_tests", "ams_solved_short", "ams_stalls", "ams_solved_continued", "ams_solved_dfs", "ams_noframe",
            "survivors", "dfs_exhausted_nopair", "noframe", "verify_fail", "stall_lines", "dfs_nodes"]
SEC_KEYS = ["sec_e10", "sec_dfs1", "sec_ams", "sec_fallback", "sec_wall"]
HIST_KEYS = ["mincut_hist", "ams_phi0_hist", "ams_moves_log2_hist", "ams_stall_phi_hist", "ams_cont_moves_log2_hist"]


def parse_sum(path):
    d = {}
    for line in open(path):
        if "=" not in line:
            continue
        k, v = line.rstrip("\n").split("=", 1)
        d[k] = v
    return d


def hist_add(acc, s):
    for part in s.split(","):
        if ":" in part:
            a, b = part.split(":")
            acc[int(a)] = acc.get(int(a), 0) + int(b)


def fmt_hist(h):
    return ", ".join("%d: %d" % (k, h[k]) for k in sorted(h)) or "none"


def main():
    merge = "--no-merge" not in sys.argv
    done = sorted(glob.glob(os.path.join(D, "data", "shards", "*", "s*.done")))
    tot = {k: 0 for k in INT_KEYS}
    sec = {k: 0.0 for k in SEC_KEYS}
    hist = {k: {} for k in HIST_KEYS}
    slices, gen_total, shard_wall = [], 0, 0
    sat = {"lines": 0, "SPAN": 0, "NOSPAN": 0, "TIMEOUT": 0, "witness_fail": 0, "candidate_failure": 0, "sec": 0.0}
    cand = []
    stall_files = []
    params = None
    for dn in done:
        P = dn[:-5]
        r = int(re.search(r"s(\d+)\.done$", dn).group(1))
        s = parse_sum(P + ".sum")
        dd = dict(x.split("=") for x in open(dn).read().split())
        gen_total += int(dd["gen"])
        shard_wall += int(dd["end"]) - int(dd["start"])
        slices.append(r)
        for k in INT_KEYS:
            tot[k] += int(s.get(k, 0))
        for k in SEC_KEYS:
            sec[k] += float(s.get(k, 0))
        for k in HIST_KEYS:
            hist_add(hist[k], s.get(k, ""))
        if params is None:
            params = {k: s.get(k) for k in ["AMS", "MS", "MX", "MF", "RF", "NA", "NB", "dfs", "testall", "seed"]}
        if os.path.exists(P + ".sat.log"):
            txt = open(P + ".sat.log").read()
            mm = re.search(r"lines=(\d+) SPAN=(\d+) NOSPAN=(\d+) TIMEOUT=(\d+) witness_fail=(\d+) "
                           r"candidate_failure=(\d+) sec=([\d.]+)", txt)
            if mm:
                for i, k in enumerate(["lines", "SPAN", "NOSPAN", "TIMEOUT", "witness_fail", "candidate_failure"]):
                    sat[k] += int(mm.group(i + 1))
                sat["sec"] += float(mm.group(7))
            if os.path.exists(P + ".sat.jsonl"):
                for line in open(P + ".sat.jsonl"):
                    rec = json.loads(line)
                    if rec.get("status") != "SPAN":
                        cand.append((r, rec))
        if os.path.getsize(P + ".stall") > 0:
            stall_files.append(P + ".stall")
    slices.sort()
    with open(os.path.join(D, "data", "slices_done.txt"), "w") as f:
        f.write("\n".join(map(str, slices)) + ("\n" if slices else ""))
    nstall_lines = 0
    if merge:
        with open(os.path.join(D, "data", "stall_frames.txt"), "w") as f:
            for sf in stall_files:
                r = re.search(r"s(\d+)\.stall$", sf).group(1)
                for line in open(sf):
                    f.write("slice=%s %s" % (r, line))
                    nstall_lines += 1
    failed = []
    fp = os.path.join(D, "logs", "failed.txt")
    if os.path.exists(fp):
        failed = [l.strip() for l in open(fp) if l.strip()]
    solved_total = (tot["dfs1_solved"] + tot["am_fallback_solved"] + tot["dfs2_solved"] + tot["ams_solved_short"]
                    + tot["ams_solved_continued"] + tot["ams_solved_dfs"])
    cpu = sum(sec[k] for k in ["sec_e10", "sec_dfs1", "sec_ams", "sec_fallback"])
    now = time.strftime("%Y-%m-%d %H:%M:%S %Z")
    out = []
    out.append("# S6 at |B| = 22: run result (collector output)\n")
    out.append("Written by `code/collect.py` at %s from the slices with a done marker. Rung (b) computation;"
               " nothing here is reviewed. Definitions and method: `JOBS.md`.\n" % now)
    out.append("## Coverage\n")
    out.append("- Slices done: **%d of %d** (`genbg -X-3 -d6:6 -D6:6 11 11 r/10000`, r in `data/slices_done.txt`; "
               "the run takes slices in the fixed random order `data/order.txt`)." % (len(slices), MOD))
    out.append("- Coloured graphs generated in those slices (genbg class count, classes A = 0..10, B = 11..21; a"
               " graph and its side swap are separate genbg classes unless isomorphic, so each uncoloured graph"
               " is tested once per orientation): **%d**; read by s6n22: %d; bad input: %d." % (
                   gen_total, tot["graphs"], tot["bad_input"]))
    if len(slices) == MOD:
        out.append("- **All slices done: the test is exhaustive over every simple bipartite 6-regular graph on 11+11 vertices.**")
    else:
        out.append("- Not exhaustive yet: the statement covers exactly the graphs genbg puts in the listed slices.")
    out.append("")
    out.append("## Counts\n")
    out.append("| quantity | value |\n|---|---|")
    rows = [
        ("E10 graphs (min essential cut >= 10)", tot["e10"]),
        ("non-E10 graphs (skipped)", tot["non_e10"]),
        ("tests (E10 graph, edge oy); 66 per graph", tot["tests"]),
        ("solved, all tiers (verified pair)", solved_total),
        ("DFS first pass solves (tests outside the AM sample)", tot["dfs1_solved"]),
        ("AM fallback solves (after a DFS budget-out)", tot["am_fallback_solved"]),
        ("DFS large-budget solves", tot["dfs2_solved"]),
        ("AM sample: tests (graphs with index % AMS == 0, AM walk first)", tot["ams_tests"]),
        ("AM sample: solved within the short budget (recoloring solves)", tot["ams_solved_short"]),
        ("AM sample: stalls at the short budget (frames saved)", tot["ams_stalls"]),
        ("AM sample: stalls then solved by continuing the walk", tot["ams_solved_continued"]),
        ("AM sample: stalls then solved by DFS", tot["ams_solved_dfs"]),
        ("AM sample: no frame built", tot["ams_noframe"]),
        ("survivors sent to SAT (SAT calls)", tot["survivors"]),
        ("SAT answers: SPAN / NOSPAN / TIMEOUT", "%d / %d / %d" % (sat["SPAN"], sat["NOSPAN"], sat["TIMEOUT"])),
        ("SAT witness check failures", sat["witness_fail"]),
        ("DFS exhausted with no pair (exact NO by DFS)", tot["dfs_exhausted_nopair"]),
        ("**failures (S6 counterexample candidates, NOSPAN by two SAT deciders)**", sat["candidate_failure"]),
        ("verify failures (a tool bug, not a result)", tot["verify_fail"]),
        ("stall lines saved", tot["stall_lines"]),
        ("slices with a failed run (logs/failed.txt lines)", len(failed)),
    ]
    for a, b in rows:
        out.append("| %s | %s |" % (a, b))
    out.append("")
    out.append("## Timing (CPU seconds inside s6n22, summed over slices)\n")
    out.append("| part | seconds | per test or graph |\n|---|---|---|")
    nt_dfs = max(1, tot["tests"] - tot["ams_tests"])
    out.append("| E10 test | %.0f | %.1f us per graph |" % (sec["sec_e10"], 1e6 * sec["sec_e10"] / max(1, tot["graphs"])))
    out.append("| DFS first pass | %.0f | %.2f us per test |" % (sec["sec_dfs1"], 1e6 * sec["sec_dfs1"] / nt_dfs))
    out.append("| AM sample (walk + its fallbacks) | %.0f | %.1f us per test |" % (
        sec["sec_ams"], 1e6 * sec["sec_ams"] / max(1, tot["ams_tests"])))
    out.append("| fallbacks after DFS budget-out | %.1f | |" % sec["sec_fallback"])
    out.append("| SAT (python, survivors) | %.1f | |" % sat["sec"])
    out.append("| s6n22 wall, summed | %.0f | |" % sec["sec_wall"])
    out.append("| slice wall incl. genbg, summed | %d (%.1f core-hours) | |" % (shard_wall, shard_wall / 3600.0))
    out.append("")
    out.append("## Histograms\n")
    out.append("- min essential cut over graphs: %s" % fmt_hist(hist["mincut_hist"]))
    out.append("- AM sample, Phi of the initial frame: %s" % fmt_hist(hist["ams_phi0_hist"]))
    out.append("- AM sample, iterations to Phi = 2 (bucket b = [2^(b-1), 2^b), 0 = none needed): %s" % fmt_hist(
        hist["ams_moves_log2_hist"]))
    out.append("- AM sample, Phi at the stall: %s" % fmt_hist(hist["ams_stall_phi_hist"]))
    out.append("- AM sample, extra iterations when a stalled walk was continued and escaped: %s" % fmt_hist(
        hist["ams_cont_moves_log2_hist"]))
    out.append("")
    out.append("## Stalled frames (for the S6 proof lane)\n")
    out.append("`data/stall_frames.txt`: %d lines, one per AM-sample test whose walk did not reach Phi = 2 within the"
               " short budget. Format: `slice=<r> <graph6 of B> o=<o> y=<y> phi_stall=<Phi at the stall>"
               " phi_min=<min Phi seen> moves_short=<budget> cont_moves=<extra iterations to escape, -1 if the"
               " continuation did not escape> solved_by=<am_continued|dfs|survivor> lam=<p-q:c,...> col=<colours"
               " of the 55 Y edges>`. The frame is the stalled one (before the continuation). Y edges are"
               " ordered by (A-vertex, B-vertex) in B's labels with o, y removed; Lambda edges are listed"
               " as (P-end in N(o)-y, Q-end in N(y)-o, colour 4 or 5); colours 0-3 are the two factors under"
               " the pairing that gives Phi (min over the three pairings)." % nstall_lines)
    ss = os.path.join(D, "data", "stall_sat", "SUMMARY.txt")
    if os.path.exists(ss):
        out.append("SAT on the stalled tests (`code/sat_stalls.sh`, run after the slices): %s\n" % open(ss).read().strip())
    else:
        out.append("SAT on the stalled tests: not run yet (`code/sat_stalls.sh` after the run; an early check of the"
                   " first 2,462 stalls gave 2,462 SPAN with re-checked witnesses, `data/val/sat_stalls_early.log`).\n")
    out.append("")
    if cand:
        out.append("## Non-SPAN SAT answers\n")
        for r, rec in cand:
            out.append("- slice %d: %s" % (r, json.dumps(rec)))
        out.append("")
    if failed:
        out.append("## Failed slice runs (redone on resume)\n")
        for l in failed[-20:]:
            out.append("- %s" % l)
        out.append("")
    out.append("Run parameters (from the first slice): %s\n" % json.dumps(params))
    open(os.path.join(D, "RESULT.md"), "w").write("\n".join(out) + "\n")
    print("slices=%d gen=%d tests=%d solved=%d survivors=%d sat=%s candidate_failure=%d verify_fail=%d stall_lines=%d" % (
        len(slices), gen_total, tot["tests"], solved_total, tot["survivors"], sat["lines"], sat["candidate_failure"],
        tot["verify_fail"], nstall_lines))


if __name__ == "__main__":
    main()
