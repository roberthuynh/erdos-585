"""collect.py: sum the excensus shards and write the results.

Usage: python collect.py [--no-write]

For every job in code/jobs.tsv it counts finished shards (logs/TAG/shard_r.done), sums the
output counts and user CPU, lists missing shards, and concatenates any output graphs into
data/found_TAG.g6. Output graphs are graphs with no 4-regular subgraph (kind q4: the pruned
generator's output; kind sat: the pysat decider's UNSAT graphs). Each one is re-decided by two
deciders: validate_sat.has_q4 (pysat) and q4filter (q4core.h); both must say "none".

Writes data/COLLECT.md and replaces the block between the COLLECT markers in EX.md.
With --no-write it only prints the table.
"""
import os
import subprocess
import sys
import time

E = "[local path]"
QDIR = "[local path]"
sys.path.insert(0, QDIR)
BEGIN, END = "<!-- COLLECT:BEGIN -->", "<!-- COLLECT:END -->"


def jobs():
    out = []
    for line in open(os.environ.get("EXC_JOBS", os.path.join(E, "code", "jobs.tsv"))):
        if not line.strip() or line.startswith("#"):
            continue
        f = line.rstrip("\n").split("\t")
        out.append(dict(tag=f[0], kind=f[1], mod=int(f[2]), binary=f[3], args=f[4],
                        note=f[5] if len(f) > 5 else ""))
    return out


def parse_done(path):
    d = {}
    toks = open(path).read().split()
    for i, t in enumerate(toks):
        if "=" in t:
            k, v = t.split("=", 1)
            d[k] = v
        elif t in ("SAT", "UNSAT") and i + 1 < len(toks):
            d[t] = toks[i + 1]
    return d


def recheck(g6path):
    """Re-decide every graph in g6path with pysat and with q4filter. Returns a text summary."""
    lines = [l.strip() for l in open(g6path) if l.strip()]
    if not lines:
        return "no graphs"
    import networkx as nx
    from validate_sat import has_q4
    sat_none = sum(1 for l in lines if has_q4(nx.from_graph6_bytes(l.encode())) is None)
    p = subprocess.run([os.path.join(QDIR, "q4filter")], input="\n".join(lines) + "\n",
                       capture_output=True, text=True)
    q4_none = len([l for l in p.stdout.splitlines() if l.strip()])
    sys.path.insert(0, os.path.join(E, "code"))
    from certify import certify_file
    tag = os.path.basename(g6path)[len("found_"):-len(".g6")]
    good, rep = certify_file(g6path, os.path.join(E, "data", f"cert_{tag}"))
    open(os.path.join(E, "data", f"cert_{tag}.txt"), "w").write(rep + "\n")
    return (f"{len(lines)} graphs: pysat says no 4-regular subgraph for {sat_none}; "
            f"q4filter says none for {q4_none}; glucose4 DRAT + RUP check: {rep.splitlines()[-1]} "
            f"(data/cert_{tag}.txt)")


def main():
    write = "--no-write" not in sys.argv
    rows, status = [], {}
    for j in jobs():
        L = os.path.join(E, "logs", j["tag"])
        done, missing, cpu, out, gen, sat = 0, [], 0.0, 0, 0, 0
        for r in range(j["mod"]):
            p = os.path.join(L, f"shard_{r}.done")
            if not os.path.exists(p):
                missing.append(r)
                continue
            d = parse_done(p)
            done += 1
            try:
                cpu += float(d.get("user", "0"))
            except ValueError:
                pass
            if j["kind"] == "sat":
                gen += int(d.get("generated", "0"))
                sat += int(d.get("SAT", "0"))
                out += int(d.get("UNSAT", "0"))
            else:
                out += int(d.get("graphs", "0"))
        running = 0
        if os.path.isdir(L):
            running = sum(1 for x in os.listdir(L) if x.endswith(".claim"))
        found = os.path.join(E, "data", f"found_{j['tag']}.g6")
        nfound = 0
        if write:
            with open(found, "w") as fo:
                for r in range(j["mod"]):
                    g = os.path.join(L, f"shard_{r}.g6")
                    if os.path.exists(os.path.join(L, f"shard_{r}.done")) and os.path.exists(g):
                        for l in open(g):
                            if l.strip():
                                fo.write(l.strip() + "\n")
                                nfound += 1
        complete = done == j["mod"]
        st = dict(complete=complete, out=out, done=done, mod=j["mod"])
        status[j["tag"]] = st
        check = ""
        if write and nfound:
            check = recheck(found)
        extra = f"; generated {gen}, SAT {sat}" if j["kind"] == "sat" else ""
        rows.append((j["tag"], j["note"], f"{done}/{j['mod']}" + (f" ({running} running)" if running else ""),
                     str(out) + extra, f"{cpu:,.0f}", "COMPLETE" if complete else
                     f"INCOMPLETE, missing {len(missing)}: {missing[:12]}{' ...' if len(missing) > 12 else ''}",
                     check))
    stamp = time.strftime("%Y-%m-%d %H:%M:%S %Z")
    out = [f"Written {stamp} by `code/collect.py` from the shard files; rules in section 3.", ""]
    out += verdicts(status)
    out += ["", "Detached jobs (`code/jobs.tsv`):", "",
            "| Job | Class | Shards done | Output graphs (no 4-regular subgraph) | user CPU s | Status | Re-check of output |",
            "|---|---|---|---|---|---|---|"]
    for t in rows:
        out.append("| " + " | ".join(x if x else "-" for x in t) + " |")
    text = "\n".join(out) + "\n"
    print(text)
    if not write:
        return
    open(os.path.join(E, "data", "COLLECT.md"), "w").write("# excensus collector output\n\n" + text)
    ex = os.path.join(E, "EX.md")
    if os.path.exists(ex):
        s = open(ex).read()
        if BEGIN in s and END in s:
            a, rest = s.split(BEGIN, 1)
            _, b = rest.split(END, 1)
            open(ex, "w").write(a + BEGIN + "\n" + text + END + b)


def verdicts(st):
    """The answer table. Facts that are not jobs here (complete foreground runs, census F1, QB(5),
    witnesses) are fixed text; see EX.md sections 2 to 4."""
    A, B, C = st.get("n18_99_e47"), st.get("n19_910_e50"), st.get("n20_1010_e54_d5")

    def zero(s):
        return s is not None and s["complete"] and s["out"] == 0

    def found(s):
        return s is not None and s["out"] > 0

    def prog(s):
        return f"{s['done']}/{s['mod']} shards done, 0 graphs so far" if s else "not started"

    rows = [("17", "**43**", "complete. e = 44 (sides 8 + 9): 0 graphs in both class orders; e ≥ 45: census F1(17); "
             "lower bound `data/witness_n17.g6`")]
    ex18 = ex19 = None
    if zero(A):
        ex18 = 46
        rows.append(("18", "**46**", "complete. e = 47: sides 8 + 10, 0 graphs in both orders; sides 9 + 9 (job A), 0 graphs; "
                     "e ≥ 48: census F1(18); lower bound `data/witness_n18.g6`"))
    elif found(A):
        ex18 = 47
        rows.append(("18", "**47 (!!!)**", "job A found graphs with e = 47 and no 4-regular subgraph: "
                     "`data/found_n18_99_e47.g6`. Tell the lead; the n = 19, 20 rows assumed ex(18) = 46."))
    else:
        rows.append(("18", "46 or 47", f"job A (9 + 9, e = 47): {prog(A)}"))
    if ex18 == 46:
        if zero(B):
            ex19 = 49
            rows.append(("19", "**49**", "complete. e = 50 (job B, sides 9 + 10): 0 graphs; e = 51 forces δ ≥ 5 (Lemma B): "
                         "0 graphs in both orders; e ≥ 52: impossible (Lemma B; also QB(5)); lower bound `data/witness_n19.g6`"))
        elif found(B):
            ex19 = 50
            rows.append(("19", "**50 (!!!)**", "job B found graphs with e = 50: `data/found_n19_910_e50.g6`; e = 51 (δ ≥ 5) gave 0, "
                         "e ≥ 52 impossible. Tell the lead; the n = 20 row assumed ex(19) = 49."))
        else:
            rows.append(("19", "49 or 50", f"job B (9 + 10, e = 50): {prog(B)}; e = 51 (δ ≥ 5) gave 0; e ≥ 52 impossible"))
    else:
        rows.append(("19", "49 to 51", "needs ex(18) = 46 first (Lemma B); QB(5) gives ex(19) ≤ 51"))
    if ex19 == 49:
        if zero(C):
            rows.append(("20", "**52 or 53**", "e ≥ 55 impossible (Lemma B); e = 54 forces δ ≥ 5 and job C (10 + 10) gave 0; "
                         "e = 53 not run (over budget, section 5); lower bound `data/witness_n20.g6`"))
        elif found(C):
            rows.append(("20", "**54 (!!!)**", "job C found δ ≥ 5 graphs with e = 54 = 3n − 6 and no 4-regular subgraph: "
                         "`data/found_n20_1010_e54_d5.g6`, so QB(6) fails at n = 20. Tell the lead."))
        else:
            rows.append(("20", "52 to 54", f"job C (10 + 10, e = 54, δ ≥ 5): {prog(C)}; QB(5) gives ex(20) ≤ 54"))
    else:
        rows.append(("20", "52 to 54", "needs ex(19) = 49 first (Lemma B); QB(5) gives ex(20) ≤ 54"))
    v = ["| n | ex(n) | Basis |", "|---|---|---|"]
    v += [f"| {a} | {b} | {c} |" for a, b, c in rows]
    v.append("")
    if ex18 == 46:
        q7 = 19 if ex19 == 49 else 18
        v.append(f"So QB(7) (e ≥ 3n − 7 forces a nonempty 4-regular subgraph) holds for 4 ≤ n ≤ {q7}"
                 + (", and QB(6) holds for 4 ≤ n ≤ 20." if (ex19 == 49 and zero(C)) else "."))
    for tag, s in st.items():
        if tag not in ("n18_99_e47", "n19_910_e50", "n20_1010_e54_d5"):
            v.append(f"- extra job {tag}: {s['done']}/{s['mod']} shards, {s['out']} output graphs"
                     + (" (complete)." if s["complete"] else " (incomplete)."))
    return v


if __name__ == "__main__":
    main()
