#!/usr/bin/env python3
"""report.py (wave8/s6spot): writes SPOTCHECK.md from data/collect.json, data/nonE10.txt,
data/val/flow_sample.log and the validation logs. Run after collect.py, nonE10.py, flowsample.py."""
import json, os, pathlib, re, hashlib

D = pathlib.Path(__file__).resolve().parent.parent
C = json.load(open(D / "data" / "collect.json"))
rows, tot = C["rows"], C["totals"]
full = [r for r in rows if r["mode"] == "full"]
special = [r for r in rows if r["mode"] != "full"]
jobs = [l.split() for l in open(D / "data" / "jobs.txt") if l.strip()]
planned_full = [int(r) for r, m in jobs if m == "full"]
done_full = [r["r"] for r in full]
seed = open(D / "data" / "sample_seed.txt").read().split()[0]
flow = open(D / "data" / "val" / "flow_sample.log").read()
flow_line = [l for l in flow.splitlines() if l.startswith("FLOW_SAMPLE")][-1]
flow_dis = [l for l in flow.splitlines() if "DISAGREE" in l]
nonE10 = open(D / "data" / "nonE10.txt").read()
genbg = os.path.expanduser("~/.cache/erdos585/nauty2_9_3/genbg")
gsha = hashlib.sha256(open(genbg, "rb").read()).hexdigest()

# aggregate SAT rounds and CPU from the span.json files
rounds, cpu_span = {}, 0.0
for r in full:
    sj = json.load(open(D / "data" / "slices" / ("s%d.span.json" % r["r"])))
    for k, v in sj["rounds_hist"].items():
        rounds[int(k)] = rounds.get(int(k), 0) + v
    cpu_span += sj["sec_cpu"]
nt = sum(rounds.values())
cum, med = 0, None
for k in sorted(rounds):
    cum += rounds[k]
    if med is None and 2 * cum >= nt:
        med = k
wall = sum(r["sec_genbg"] + r["sec_e10"] + r["sec_span"] for r in rows)
wall_e10 = sum(r["sec_e10"] for r in rows)
all_match = all(r["match"] for r in rows)
missing = [r for r in planned_full if r not in done_full]

def fmt(x):
    return "{:,}".format(x)

verdict = (
    "**Verdict: s6n22 checks out on the sample.** On %d random slices (%s coloured graphs, %.4f%% "
    "of the 156,473,848 classes; %s (graph, edge) tests, %.4f%% of s6n22's 10,327,273,770) every "
    "compared count matches s6n22's per-slice record (genbg count, E10 count, min-cut histogram, "
    "tests), and every test has two edge-disjoint Hamilton cycles in Y = B - o - y, found by a SAT "
    "encoding written here and checked edge by edge against the graph: %s SPAN, %d NO, %d witness "
    "failures. The three non-E10 graphs are confirmed not E10 by two methods (min essential cuts 8, "
    "6, 8, as recorded). S6's conclusion fails on each of them, exactly on the edges of the "
    "minimum cut (8 + 6 + 8 of 198 tests), so S6 needs its E10 hypothesis already at |B| = 22."
    % (len(full), fmt(tot["graphs"]), 100 * tot["fraction_graphs"], fmt(tot["tests"]),
       100 * tot["tests"] / 10327273770, fmt(tot["span"]), tot["no"], tot["witness_fail"]))
if not all_match or tot["no"] or tot["witness_fail"] or flow_dis or missing:
    verdict = ("**Verdict: see the mismatches below (rows marked NO, missing slices %s, flow "
               "disagreements %d).**" % (missing, len(flow_dis)))

table = open(D / "data" / "compare.md").read()

md = f"""# S6 at |B| = 22: independent spot-check of wave6/s6n22

Lane wave8/s6spot, 2026-10-06. Rung (b) computation. Nothing here is reviewed. No `check.sh`, no
Lean, nothing sent off this machine. Run record: `JOBS.md`; code in `code/`; data in `data/`.

{verdict}

## What was checked, and what is shared with s6n22

S6 (wave4/va6/SCOUT.md §7): if Γ = B - o is sparse, every port y of o has two edge-disjoint Hamilton
cycles in B - o - y. For a 6-regular B, g(S) = |δ_B(S)| for S avoiding o, so "B - o sparse" for
one o, or for all o, is the same as "B is E10" (every edge cut with at least 2 vertices on each side
has at least 10 edges). The test for an edge oy does not depend on which end is called o, so a
coloured graph has 66 tests, as in s6n22; a graph and its side swap are separate genbg classes and
each is tested in its own slice, as in s6n22 (JOBS.md there).

- **Shared with s6n22:** the genbg binary `~/.cache/erdos585/nauty2_9_3/genbg` (SHA-256
  `{gsha[:16]}…`) and its command line `genbg -X-3 -d6:6 -D6:6 11 11 r/10000` (read from
  s6n22's `run_shard.sh`); the PySAT library (s6n22 used it, through wave4/va6's
  `span_oracle.py`, only for its 0 survivors and its post-run SAT check of the 333,908 stalled AM
  tests; its decisions came from its own C tool, a DFS and the AM walk).
- **Written here, sharing no code with `wave6/s6n22/code`:** `code/e10cut.c` (graph6 decoder and
  exact minimum essential cut), `code/spantest.py` (graph6 decoder, SAT encoding, witness checker),
  `code/validate.py`, `code/nonE10.py`, `code/collect.py`, the driver scripts. Nothing in s6n22's
  `code/` was imported or run.

## Sample

- Slice order: a uniform random permutation of 0..9999 from Python's `random.Random(seed)` with
  seed **{seed}**, drawn from `os.urandom` and recorded in `data/sample_seed.txt` before any
  slice ran; order in `data/sample_order.txt` (`code/pick_sample.py`). (The date seed 20261006 was
  tried first and reproduced s6n22's own `order.txt` exactly, so it was dropped.)
- **The sample is the first 50 slices of that order** (the number was fixed from the pilot timing,
  before any results): {", ".join(str(r) for r in planned_full)}. Done: {len(full)} of 50{"" if not missing else "; missing " + str(missing)}.
  Slice 1881, second in the order, was the pilot (same pipeline, run in the foreground just
  before the launch; the driver skipped it).
- Not random, checked separately: slices 5491, 7913, 8360, the three where s6n22 recorded one
  non-E10 graph each (E10 check on every graph, SAT only on the non-E10 graph).

## Counts compared, per slice

"now" = this lane's regeneration; "s6n22 sum" and "s6n22 genbg" = s6n22's `s<r>.sum` and
`s<r>.genbg.err`. "stall g6 found": every graph6 string in s6n22's `s<r>.stall` for that slice also
occurs in the regenerated slice (a content check beyond the counts).

{table}
Totals over the {len(full)} random slices: **{fmt(tot["graphs"])} graphs, {fmt(tot["e10"])} E10,
{fmt(tot["tests"])} tests, {fmt(tot["span"])} SPAN, {tot["no"]} NO, {tot["witness_fail"]} witness
failures**; every row matches: **{"yes" if all_match else "NO"}**.

## Method

**E10 (`code/e10cut.c`).** For each graph, the exact minimum of |δ(S)| over all S with
2 <= |S| <= 20, by enumerating all 2^21 sets S that contain vertex 0 in reflected Gray-code order
(each bipartition once), updating |δ(S)| by deg(v) - 2|N(v) ∩ S| per step. Per graph it also checks
6-regularity, that every edge joins {{0..10}} to {{11..21}}, and recomputes |δ(S)| directly for the
final set and the argmin. Second method on a random subset (`code/flowsample.py`,
`data/val/flow_sample.log`): min over vertex-disjoint edge pairs (e, f) of the max-flow between e
and f (networkx), which equals the minimum essential cut for these graphs (an essential S with
|δ(S)| <= 10 < 12 <= 6|S| has an edge on each side). Result: {flow_line.replace("FLOW_SAMPLE ", "")}
(2 random graphs per random slice plus the 3 non-E10 graphs){"" if not flow_dis else "; DISAGREEMENTS: " + str(flow_dis)}.

**Two edge-disjoint Hamilton cycles (`code/spantest.py`, PySAT MiniSat 2.2).** One incremental
solver per graph B: variables a_v (vertex active) and x(e, c) (edge e of B in cycle c = 0, 1);
clauses: x(e, c) implies both ends active; no edge in both cycles; at most 2 colour-c edges at a
vertex (every 3-subset); an active vertex has at least 2 (every 5-subset of its 6 edges). Test
(o, y) solves under the assumptions "o, y inactive, all others active". A model gives two 2-factors
of Y; if either has several cycles, the cut "some vertex of S inactive, or some edge of δ_B(S) has
colour c" is added for every such cycle S and both colours, and the solver runs again. Every cut
is valid for every test (if S avoids o and y it is a proper subset of V(Y), so a Hamilton cycle
leaves it; otherwise its guard holds), so UNSAT means no pair. Every SPAN answer is accepted only
after `verify_pair` checks the two cyclic vertex sequences against B: both are permutations of
V(B) - o - y, consecutive vertices are adjacent in B, and the 40 edges are distinct. A NO answer is
re-decided by a second encoding (Y alone, no activation literals, CaDiCaL 1.5.3). Each graph is
decoded twice (C and Python) and the two edge-list hashes are compared on every graph. SAT rounds
per test over the sample: median {med}, max {max(rounds)}; CPU in spantest {cpu_span / nt * 1e6:.0f} us per
test.

## Tool validation (`data/val/`)

- Controls built here: K_(6,6) (36 tests: all SPAN, witnesses verified; min cut 10) and NEG24, two
  copies of K_(6,6) minus an edge joined by two edges (min cut 2 by both E10 methods; all 72 tests NO
  by both encodings).
- Witness checker: seven corrupted witnesses (same cycle twice, reversed copy, o included, vertex
  dropped or repeated, non-edge, swapped entries) rejected; 20,000 shuffled sequences agree with a
  direct recount (`witness.log`).
- Pilot: 100 graphs of slice 7797, 6,600 tests, the same answers with MiniSat, Glucose 4 and
  CaDiCaL (`pilot100_*.span.json`).

## The three non-E10 graphs

Found by regenerating slices 5491, 7913 and 8360 and running e10cut on all of their graphs
({", ".join("%d: %s graphs, E10 %s (s6n22: %s, %s)" % (r["r"], fmt(r["my_graphs"]), fmt(r["my_e10"]), fmt(r["orig_graphs"]), fmt(r["orig_e10"])) for r in special)}). graph6 in `data/nonE10.g6`,
details in `data/nonE10.txt`. Each is confirmed not E10 by both methods (e10cut and max-flow). On
each, the S6 conclusion fails exactly on the edges of its minimum cut, and every NO is certified
three ways: the incremental SAT, the second SAT encoding, and a counting argument that needs no
solver (`code/nonE10.py`). Take T = S - o - y (S the minimum cut set), let a and b count the edges
of δ_Y(T) whose end in T is on side A, resp. B, and d = |T_A| - |T_B|. A Hamilton cycle of Y meets T
in paths (possibly single vertices), each entered and left along crossing edges; a path with both
ends on A has one more A- than B-vertex, so d = p_AA - p_BB. Hence one Hamilton cycle uses at least
(mA, mB) crossing edges with A-, resp. B-ends, where (mA, mB) = (1, 1) if d = 0, (2d, 0) if d > 0,
(0, -2d) if d < 0. If a < mA or b < mB, Y has no Hamilton cycle; if a < 2mA or b < 2mB, Y has no two
edge-disjoint ones. Example: graph 13715 of slice 8360, edge (0, 11): d = 0 and only b = 1 crossing
edge ends on side B, but each of the two cycles needs one.

```
{nonE10.strip()}
```

So S6's conclusion does not hold there anyway: 22 of the 198 tests on non-E10 graphs fail.

## Coverage

- Random slices: {len(full)} of 10,000 ({100 * len(full) / 10000:.2f}% of the slices), {fmt(tot["graphs"])} of
  156,473,848 coloured graphs ({100 * tot["fraction_graphs"]:.4f}%), {fmt(tot["tests"])} of 10,327,273,770 tests
  ({100 * tot["tests"] / 10327273770:.4f}%).
- Plus the three non-random slices for counts and E10 ({fmt(sum(r["my_graphs"] for r in special))} graphs).

## Cost

At most {wall / 3600:.2f} core-hours: {fmt(wall)} worker wall-seconds summed from the done markers
(genbg, e10cut, spantest per slice; nice 10 on a machine at load 40-60, so this bounds the CPU used
from above). Of it, {fmt(wall_e10)} s in e10cut; spantest's own CPU time was {fmt(round(cpu_span))} s.
Validation and the max-flow sample added a few CPU-minutes. 4 workers, 09:53:28 to 10:52:26 EDT.

## Files

- `code/`: `e10cut.c`, `spantest.py`, `validate.py`, `flowsample.py`, `nonE10.py`,
  `pick_sample.py`, `run_slice.sh`, `driver.sh`, `launch.py`, `collect.py`, `report.py`.
- `data/sample_seed.txt`, `data/sample_order.txt`, `data/jobs.txt`, `data/collect.json`,
  `data/compare.md`, `data/nonE10.g6`, `data/nonE10.txt`, `data/val/`.
- `data/slices/s<r>.*`: regenerated graph6 (`.g6.gz`), genbg stderr, e10cut output (`.cut.gz`,
  one line per graph: index, min cut, |argmin|, argmin mask, edge hash), spantest summary
  (`.span.json`), NO lines (`.no`), done markers. The `.g6` and `.cut` files were gzipped after
  the report was built (gunzip before rerunning `collect.py`, `flowsample.py` or `nonE10.py`);
  `data/slices/SHA256SUMS` lists the uncompressed files.
"""
open(D / "SPOTCHECK.md", "w").write(md)
print("SPOTCHECK.md written; all_match=%s missing=%s flow=%s" % (all_match, missing, flow_line))
