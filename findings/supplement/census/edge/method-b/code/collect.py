"""collect.py -- collector for method B (wave8/exb).

Reads code/jobs.tsv, code/queue.txt and logs/<tag>/shard_<r>.{g6,err,done};
sums shards per job; re-decides every output graph three ways (h4filt, the
PySAT decider, and a bipartite / degree / edge check); writes
data/COLLECT.md and the block between the COLLECT markers in EX-B.md.

Rules (EX-B.md section 3): with ex(16) = 40 (data/chain.txt, own chain),
  ex(17) = 43 iff (17, 44, min degree >= 4, sides 8+9) is empty;
  then ex(18) = 46 iff (18, 47, min degree >= 4, sides 8+10 and 9+9) is empty;
  then ex(19) = 49 iff (19, 50, min degree >= 4, sides 9+10) is empty.
  (19, 51, min degree >= 5) is implied by (19, 50) and run as a cross-check.
Lower bounds: chain witnesses (own) and method 1's witness files (checks.txt).
"""

import datetime
import glob
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
LOGS = os.path.join(ROOT, "logs")
DATA = os.path.join(ROOT, "data")
sys.path.insert(0, HERE)
import deciders as D  # noqa: E402

LEVELS = [  # (n, e, delta, sides, [pruned job tags], [whole-class job tags], method-1 class count)
    (17, 44, 4, "8+9", ["pr_n17_e44_8x9", "pr_n17_e44_9x8"], ["wh_n17_e44_8x9"], 14087019),
    (18, 47, 4, "8+10", ["pr_n18_e47_8x10", "pr_n18_e47_10x8"], ["wh_n18_e47_10x8"], 8584858),
    (18, 47, 4, "9+9", ["pr_n18_e47_9x9"], ["wh_n18_e47_9x9"], None),
    (19, 50, 4, "9+10", ["n19_e50_10x9", "n19_e50_9x10"], [], None),
    (19, 51, 5, "9+10", ["pr_n19_e51_9x10_d5", "pr_n19_e51_10x9_d5"], ["wh_n19_e51_10x9_d5"], 10055368),
]


def read_jobs():
    jobs = {}
    for line in open(os.path.join(HERE, "jobs.tsv")):
        if not line.strip() or line.startswith("#"):
            continue
        tag, mod, cmd = line.rstrip("\n").split("\t")
        jobs[tag] = (int(mod), cmd)
    queue = {}
    for line in open(os.path.join(HERE, "queue.txt")):
        if line.strip():
            tag, r = line.split()
            queue.setdefault(tag, []).append(int(r))
    return jobs, queue


def job_summary(tag, shards):
    d = os.path.join(LOGS, tag)
    s = dict(total=len(shards), ok=0, failed=[], missing=[], outputs=[], gen=0, cpu=0.0,
             user=0.0, wh_total=0, wh_with=0, wh_without=0, tallies={})
    for r in shards:
        if r is None:
            continue
        done = os.path.join(d, f"shard_{r}.done")
        if not os.path.exists(done):
            s["missing"].append(r)
            continue
        st = re.search(r"^status (\d+)", open(done).read(), re.M)
        if not st or st.group(1) != "0":
            s["failed"].append(r)
            continue
        s["ok"] += 1
        err = open(os.path.join(d, f"shard_{r}.err")).read()
        m = re.search(r">Z\s+(\d+) graphs generated in ([0-9.]+) sec", err)
        if m:
            s["gen"] += int(m.group(1))
            s["cpu"] += float(m.group(2))
        u = re.search(r"^user\s+([0-9.]+)", err, re.M)
        if u:
            s["user"] += float(u.group(1))
        t = re.search(r">T total (\d+) with_H (\d+) without_H (\d+)", err)
        if t:
            s["wh_total"] += int(t.group(1))
            s["wh_with"] += int(t.group(2))
            s["wh_without"] += int(t.group(3))
        for mm in re.finditer(r">S e=(\d+) sides=(\S+) mindeg=(\d+) maxdeg=(\d+) conn=(\d+) "
                              r"count=(\d+) without_H=(\d+)", err):
            key = (int(mm.group(1)), mm.group(2), int(mm.group(3)), int(mm.group(4)), int(mm.group(5)))
            c, w = s["tallies"].get(key, (0, 0))
            s["tallies"][key] = (c + int(mm.group(6)), w + int(mm.group(7)))
        g6 = os.path.join(d, f"shard_{r}.g6")
        if os.path.exists(g6):
            s["outputs"] += [l.strip() for l in open(g6) if l.strip()]
    s["complete"] = (s["ok"] == s["total"])
    return s


def redecide(graphs):
    """Return list of (g6, h4filt verdict, SAT verdict, structure ok)."""
    if not graphs:
        return []
    r = subprocess.run([os.path.join(HERE, "bin", "h4filt"), "-a", "-q"], input="\n".join(graphs) + "\n",
                       capture_output=True, text=True)
    cver = dict(line.split() for line in r.stdout.splitlines())
    out = []
    for g in graphs:
        n, edges = D.parse_g6(g)
        has, _ = D.sat_has_h4(n, edges)
        col = D.bicolour(n, edges)
        deg = [0] * n
        for u, w in edges:
            deg[u] += 1
            deg[w] += 1
        struct = col is not None and max(deg) <= 6
        out.append((g, cver.get(g), "H" if has else "0", struct, n, len(edges), min(deg)))
    return out


def main():
    jobs, queue = read_jobs()
    sums = {tag: job_summary(tag, queue.get(tag, [])) for tag in jobs}
    for _, _, _, _, prs, whs, _ in LEVELS:
        for t in prs + whs:
            if t not in sums:  # not in jobs.tsv: counts as not run
                sums[t] = job_summary(t, [None])
                sums[t]["missing"] = [0]
                sums[t]["complete"] = False
    now = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S EDT")
    L = [f"Written {now} by `code/collect.py` from the shard files.", ""]
    L.append("| Job | Command | Shards ok / total | Output graphs (no 4-regular subgraph) | "
             "Whole class (graphs generated) | CPU s (user) | Status |")
    L.append("|---|---|---|---|---|---|---|")
    total_user = 0.0
    found_all = []
    for tag, (mod, cmd) in jobs.items():
        s = sums[tag]
        total_user += s["user"]
        status = "COMPLETE" if s["complete"] else (
            f"partial: missing {len(s['missing'])}, failed {len(s['failed'])}")
        whole = f"{s['wh_total']:,} (with H {s['wh_with']:,})" if s["wh_total"] else "-"
        nout = len(s["outputs"]) if not s["wh_total"] else s["wh_without"]
        cmd_md = cmd.replace("|", "\\|")  # a pipe inside a table cell must be escaped
        L.append(f"| {tag} | `{cmd_md}` | {s['ok']}/{s['total']} | {nout} | {whole} | "
                 f"{s['user']:,.0f} | {status} |")
        found_all += [(tag, g) for g in s["outputs"]]
    L.append("")
    L.append(f"Total user CPU of the detached jobs: {total_user:,.0f} s ({total_user / 3600:.2f} core-h).")
    L.append("")
    # levels
    L.append("| n | e | min degree | sides | pruned runs (own generator + decider) | whole class, no pruning "
             "(own generator, every graph decided by h4filt) | method 1 class count (plain genbg) | verdict |")
    L.append("|---|---|---|---|---|---|---|---|")
    verdicts = []
    for n, e, dl, sides, prs, whs, m1 in LEVELS:
        pr_txt = []
        empty = True
        complete_any = False
        for t in prs:
            s = sums[t]
            pr_txt.append(f"{t}: {len(s['outputs'])} graphs" + ("" if s["complete"] else " (INCOMPLETE)"))
            if s["outputs"]:
                empty = False
            if s["complete"]:
                complete_any = True
        wh_txt = []
        for t in whs:
            s = sums[t]
            wh_txt.append(f"{s['wh_total']:,} generated, {s['wh_without']} without H"
                          + ("" if s["complete"] else " (INCOMPLETE)"))
            if s["wh_without"]:
                empty = False
            if s["complete"] and m1 is not None:
                wh_txt[-1] += f"; = method 1: {'yes' if s['gen'] == m1 else 'NO'}"
        verdict = ("EMPTY" if (empty and complete_any) else
                   ("!!! GRAPH FOUND" if not empty else "pending"))
        verdicts.append(((n, e), verdict))
        L.append(f"| {n} | {e} | >= {dl} | {sides} | {'; '.join(pr_txt)} | {'; '.join(wh_txt) or '-'} | "
                 f"{'-' if m1 is None else format(m1, ',')} | {verdict} |")
    L.append("")

    def level_empty(ne):
        vs = [v for k, v in verdicts if k == ne]
        return bool(vs) and all(v == "EMPTY" for v in vs)

    e17 = level_empty((17, 44))
    e18 = e17 and level_empty((18, 47))
    e19 = e18 and level_empty((19, 50))
    L.append("Chain (rules in EX-B.md section 3; ex(16) = 40 from `data/chain.txt`):")
    L.append(f"- ex(17) = 43: {'yes' if e17 else 'not settled'}")
    L.append(f"- ex(18) = 46: {'yes' if e18 else 'not settled'}")
    L.append(f"- ex(19) = 49: {'yes' if e19 else 'not settled'}")
    if found_all:
        L.append("")
        L.append("Output graphs re-decided (graph6 in data/found_<tag>.g6):")
        for tag in sorted(set(t for t, _ in found_all)):
            gs = [g for t, g in found_all if t == tag]
            with open(os.path.join(DATA, f"found_{tag}.g6"), "w") as f:
                f.write("\n".join(gs) + "\n")
            for g, cv, sv, st, n, m, dmin in redecide(gs):
                L.append(f"- {tag}: n={n} e={m} mindeg={dmin} bipartite+maxdeg6={st} h4filt={cv} SAT={sv}")
    text = "\n".join(L) + "\n"
    with open(os.path.join(DATA, "COLLECT.md"), "w") as f:
        f.write("# Method B collector output\n\n" + text)
    exb = os.path.join(ROOT, "EX-B.md")
    if os.path.exists(exb):
        s = open(exb).read()
        a, b = "<!-- COLLECT:BEGIN -->", "<!-- COLLECT:END -->"
        if a in s and b in s:
            s = s[:s.index(a) + len(a)] + "\n" + text + s[s.index(b):]
            open(exb, "w").write(s)
    print(text)


if __name__ == "__main__":
    main()
