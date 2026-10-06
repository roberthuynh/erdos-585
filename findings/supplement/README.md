# Supplement to "Erdős Problem 585: kernel-checked finite results, three pair-free 5-regular graphs, and a reduction at degree six"

This folder holds the files that the findings document cites and that are not elsewhere in the public
repository [roberthuynh/erdos-585](https://github.com/roberthuynh/erdos-585) at tag `v0.3`, plus,
for convenience, copies of the three edge lists and the census logs that are also there. The programs in
`small-values/programs/` are the originals of the public `computations/` programs; the public copies
differ only in relocated paths, a few docstring lines, one timing string and, at `v0.3`, American
spelling. `MANIFEST.md` lists every file with its size
and SHA-256.

## Lean (`lean/`)

Lean files under `lean/Openmath/Proofs/`: the twin-core and R1-plus results, the declarations listed
in `lean/DECLARATIONS.md` (appendix E of the findings document), and everything they import beyond
`v0.3`. The Lean files written for this project are Copyright 2026 Robert Huynh, under the Apache
License 2.0. Copy them into the public repository's `Openmath/Proofs/`, then from the repository root:

```bash
lake exe cache get
./check.sh Openmath/Proofs/TwinNoSingleton.lean Erdos585.TwinNoSingleton.hasPair_of_no_singleton_twins
```

`check.sh` builds the named file and its imports. The 39 declarations of these files that the
findings document cites, and the 56 declarations of `lean/DECLARATIONS.md` (36 of the 39 among them,
and 20 in the public repository's own files), passed this check on October 4, 2026, and again on
October 6 in a clean clone of the `v0.3` release files with these files copied into its `Openmath/`
(none of them replaces a release file). `checks/supplement-checks-in-v0.3.log` is the run's
log, with its times, each declaration's result and each run's length (its toolchain and build inputs
are those at the top of `checks/v0.3-release-files.txt`; the copied files are this folder's, with
their SHA-256 in `MANIFEST.md`);
`checks/supplement-lean-in-v0.3.tsv` and `checks/appendix-e-in-v0.3.tsv` list the same results by
declaration. `checks/` also holds the transcript of each October 4 check (these record neither date nor time;
`lean/DECLARATIONS.md` gives each declaration's time from that run), the October 4 `leanchecker`
replay of every compiled module (`checks/leanchecker-main-oct4.tsv`), the October 6 checks of the
`v0.3` release files (the build, the axiom check, `check.sh` on every headline result and `leanchecker` on
every module, in `checks/v0.3-release-files.txt` with its own timestamps), and `leanchecker` on every
module in these files (`checks/leanchecker-supplement-in-v0.3.tsv`). `lean/DECLARATIONS.md` lists the
declarations beyond those in the findings document.

## Graphs (`graphs/`)

One edge per line as `u v`; lines starting with `#` are comments.

- `regular-five-18.edges`: the 18-vertex graph, 45 edges, printed from the Lean definition.
- `regular-five-32.edges`: the 32-vertex graph, 80 edges, printed from the Lean definition.
- `bipartite-five-104.edges`: the 104-vertex graph, 260 edges, with the labels of the Lean file.
- `bipartite-five-104-sides.txt`: its two-coloring, printed from the Lean definition.
- `bipartite-five-104-alt.edges`: a second 104-vertex graph from the same block and skeleton. It is
  not isomorphic to the Lean graph (542 four-cycles against 538), and the Lean result does not cover it.
- `verify_graphs.py`: checks all four graphs from the edge lists alone in a few seconds, with no
  packages: counts, 5-regularity, the two-coloring, four-cycles, and no pair (every pair lies in a
  4-edge-connected subgraph; the script finds those subgraphs and searches each one exhaustively).

## Census (`census/`)

`programs/COMMANDS.md` gives the commands. `programs/` holds the pair test `pairc.c` and its
helpers, `gen585/` (the minimal-counterexample search for n = 13 and 14), `replication/` (the
independent replication of n = 13) and `block-dp/` (the exact block decomposition used for both
104-vertex graphs). `logs/` holds the summary lines of every census run
(`graphs=… with_pair=… pair_free=…`) and the logs cited in the findings document.

`quartic/` holds the census of bipartite graphs with no 4-regular subgraph behind the sharpness
paragraph of section 4.1: `CENSUS.md` (Jobs 2 and 3 are the F1 runs), `BUILD.md`, the graph files
`f1/`, the F1 logs, and the programs in `programs/`: the pruning hooks `q4core.h`, `q4prune.c` and
`q4prune_bg.c`, which `build.sh` compiles into nauty 2.8.9 `geng` and `genbg` as `geng_q4` and
`genbg_q4`, the SAT decider `validate_sat.py`, `sat_all.py`, and the run scripts. The F1 run at
n = 18, which `CENSUS.md` lists as projected, finished: the last line of
`logs/driver_f1_n18.log` reads `finished=24/24 graphs=0`. `CENSUS.md` also describes other runs (F2,
C0, pieces) whose logs are not included.

`calibration/` holds the degree-5 calibration of section 4.4: `CALIBRATION.md`, the programs (the
5-regular runs, the second decider `pair_oracle.py` with `crosscheck_oracle.py`, the level ladder, and
`glue18.py`, which builds the 18-vertex constructions), their logs, and the 120 glued 18-vertex graphs.
The n = 14 second-decider run finished after `CALIBRATION.md` was written: its result is the last line
of `logs/driver_xc_reg5_n14.log` (3,459,386 graphs, all with a pair, 100 of 100 shards agreeing).
`LOG.md`, `data/ladder/` and the n = 9 and 11 cross-check logs are not included, and
`data/glue18/glue18-classes.g6` is shipped as `data/glue18-classes.g6`.

`calibration/n16/` holds the census of all 5-regular graphs on 16 vertices behind row 8 of the
findings document: `REG5N16.md` (written by the run's collector), `JOBS.md` and the lane log
`LOG.md`. nauty 2.9.3 `geng` was compiled with a pair-pruning hook (`code/pairprune.c`, built by
`code/build.sh`; `code/validate_prune.sh` and `logs/validate_prune.txt` test it) and run in 20,000
shards in the shuffled order `data/shard_order.txt`; `data/done_shards.txt` lists the 20,000
completed shards, and no shard printed a graph. `code/pairprune_experiments.c` is a speed-up attempt
that the run did not adopt (`LOG.md`; `code/geng_fast.c`, which `LOG.md` names, is a modified copy of
nauty's `geng.c` and is not included). `LOG.md` and `JOBS.md` cover the first night (its driver is
`code/driver.sh.night1`); the census was resumed at 07:15 EDT on October 6 with `code/driver.sh` and
finished at 11:16 (`logs/driver.log`). The per-shard logs and the empty per-shard outputs (60,000
files, 19 MB) are not included; `REG5N16.md` sums them. `calibration/n16-second-method/` holds the
second method (`REG5N16-B.md`): a SAT pair decider on PySAT (`code/pairsat.py`) whose every pair is
checked against the graph, on the output of stock nauty 2.9.3 generators (the first method runs a
hooked build of the same `geng`); the decider shares no code with the first method. Its checks are the 388 triangle-free and the 41 bipartite 5-regular graphs on 16 vertices
(`logs/check1/`), every 5-regular graph on 6 to 14 vertices (`logs/check2/`) and 28 random shards of
the 20,000 (`logs/check3/`, 3,612,814 graphs), with the calibration of the decider on graphs with
and without pairs in `logs/calib/`, `logs/xcheck/` and `logs/glue18/`. Its two gzipped certificate
files are not included. Neither method is reviewed.

`pairs-lane/` holds the pairs lane's census programs and records, laid out as in the original
folder so that the run scripts' relative paths hold: `ptool.c` (sparsity by max flow, the
spanning-pair test `H`, the port test `y` and the witness mode `w`; its Hamilton-cycle search is
taken from `programs/pairc.c`), `cuts.c` (small edge cuts, 2-edge cuts among them, by a Gray-code
enumeration), `verify_sp.py` (checks printed pairs with networkx), the run scripts, the lane log
`LOG.md` and `data/`. They give the first method of H22 (`run_q4a11.sh`, the 24 shard summaries
`data/q4a11/err_*.txt`, the 236 graphs without a decomposition in `data/q4bip_a11_nonhd.g6`, each
with a 2-edge cut, and `data/q4bip_a8_nonhd.txt` to `q4bip_a10_nonhd.txt` for 16 to 20 vertices),
the 8 + 9 part of L5 (`run_l5s8.sh`, `data/l5s8/err_*.txt`), and the second method for census F2,
the spanning-pair runs of `papers/pairs/SCOUT.md` section 2.1 on the classes a smallest
counterexample can lie in (`data/e4_a6_sp.txt` to `e4_a8_sp.txt`, the 100 shard summaries
`data/e4a9/err_*.txt`, `data/c1_s5_ports.txt` to `c1_s7_ports.txt` and the six summaries
`data/c1_s8_part_a?.err`). In `ptool`'s summary line, `hits` counts graphs with two edge-disjoint
Hamilton cycles in mode `H`, and graphs with a port y such that G − y has them in mode `y`. The
census runs used a `ptool` binary built from an earlier revision of `ptool.c`; the lane's notes say
the exact search is unchanged in this file (`papers/pairs/SCOUT.md`, section 5). Not included: the
input graph lists, which genbg regenerates, the per-port records for s = 8 (15 MB), and the empty
outputs of runs that found nothing. `LOG.md` gives the T2 count as 82; the pairs review's fix F5
corrects it to 6.

`h22/` holds a second, independent census of H22: `H22B.md` (method, counts by stage, validation
for n ≤ 20, caveats), its log, the code (`hdq.c`, a search over red and blue edge colorings that
does not enumerate Hamilton cycles, with two tests for 2-edge cuts; `sat_hd.py`, a SAT second
decider; `verify_certs.py`, a separate certificate checker; the shard and driver scripts) and the
logs. `logs/final_checks.log` has every total at 22 vertices: 2,806,490 classes from `geng` (sides
not kept apart), 2,806,335 with a checked decomposition, 155 with a 2-edge cut, which are exactly
the first method's 236 graphs without a decomposition (genbg keeps the sides apart), and none with
neither. The per-graph certificates (61 MB) are not included. `geng` and the first method's
`genbg` share nauty's canonical labeling (`H22B.md`, section 8).

`l5/` holds a second, independent census of L5: `L5B.md` (method, counts by order and side split,
superset checks, validation, caveats), its log, the code (`l5b_sat.py`, a class filter and a SAT
pair decider whose every answer is decoded into two cycles; `verify.py`, a separate certificate
checker; the run, superset and collection scripts), the collector's `data/census/SUMMARY.json` and
`logs/collect.out` (1,357,397 classes from `geng -b` on at most 17 vertices, all with a checked
pair; 1,471,650 after conversion to genbg's count with the sides kept apart, equal to the first
method at every side split), the unsplit `geng -u` counts at 15 to 17 vertices, the superset
checks, and the validation inputs and logs. The certificate archives (one checked pair per graph,
13.7 MB) and the per-shard summaries are not included. At 17 vertices the maximum-degree flag of
`geng` is checked only by the count match (`L5B.md`, caveats). `geng` and the first method's `genbg`
are both nauty 2.9.3 programs (`L5B.md`, caveats).

`s6n22/` holds the computation behind row 18 of the findings document: the collector's `RESULT.md`
(coverage, counts, timing, histograms), `JOBS.md` (method, pilot, validation, commands), the lane
log, the code and the summary logs. `code/s6n22.c` is the decision program: an exact E10 test, a
randomized recoloring search (the "AM walk") and a depth-first search for two edge-disjoint
Hamilton cycles, with every claimed pair checked directly; `s6n22_v1.c` is the first version, used
for the 20-vertex validation; `sat_check.py` imports two SAT deciders written in other lanes,
`span_oracle.py` and `myspan.py`, copied beside it. `logs/collect_final.log`,
`logs/sat_stalls.log` and `logs/check_stall_frames.log` hold the totals. The per-slice outputs,
the 333,908 stalled frames and the validation outputs (`data/`, 258 MB) are not included. Nothing
here is reviewed. `s6n22/spot-check/` holds an independent spot-check of 50 random slices of the
10,000 (`SPOTCHECK.md`, `JOBS.md`, the code, the data and the logs): its own E10 test
(`code/e10cut.c`), SAT encoding and witness checker (`code/spantest.py`); it shares only the
`genbg` binary and command line and the PySAT library with the run it checks. Its per-slice
outputs (`data/slices/`, 425 files, 12 MB) are not included; `data/collect.json` and
`data/compare.md` sum them. It is a check of a sample, not a review.

`edge/` holds the edge census of section 5, question 4 (`EX.md`, `JOBS.md` and the lane log
`LOG.md`): ex(n), the largest number of edges of a bipartite graph on n vertices with maximum degree
at most 6 and no nonempty 4-regular subgraph, for n = 17 to 20, from runs of the pruned generators
of `quartic/` and the two lemmas of `EX.md` section 3. `code/` has the run and collection scripts,
the witness builder `witness.py`, the certifier `certify.py` and the decider self-tests; `data/` has
the graphs `witness_n15.g6` to `witness_n20.g6` (3n − 8 edges and no nonempty 4-regular subgraph),
each with the CNF that says it has one and a DRAT proof that this CNF is unsatisfiable, and
`WITNESSES.txt`, which records how they were built and checked. The per-shard logs of the three
detached jobs (1,320 files) are not included; `data/COLLECT.md` and the table in `EX.md` sum them.
`edge/method-b/` holds the second method (`EX-B.md`, `JOBS.md`): its own generator
(`code/bipgen.c`, which uses nauty's core library for automorphism groups and canonical labels
only), its own exhaustive decider (`code/h4.h`, `code/h4filt.c`), a CNF decider and a flow test
(`code/deciders.py`), and a chain of exact values from n = 8 with no census input (`code/chain.py`,
`data/chain.txt`, `data/chain_witness_*.g6`), with its re-check of the first method's witnesses
(`data/WITNESS-CHECK.txt`). Its per-shard logs (`logs/`, 1,002 files) are not included;
`data/COLLECT.md` sums them. Neither method is reviewed. The reports' paths point into the private
repository, where these folders are `reports/585-next/wave6/excensus/` and
`reports/585-next/wave8/exb/`.

Partial or superseded runs, not claimed anywhere: `reg6-n15-part*.err` and `reg6-n15.stopped` (the
direct 6-regular run at n = 15, stopped), `bip-reg6-n20.err` (stopped), and
`bip-n18-level-4.PARTIAL-timeout.err` (a first attempt, superseded by `bip-n18-part0` to `part11`).

## Small values (`small-values/`)

Programs, logs and notes for n = 9 to 12. `notes/` holds the working notes behind the n = 9 and n = 10
figures. The second exhaustive method for f(12) is the targeted audit `programs/erdos585_twelve_upper.py`,
with output `logs/twelve-upper-independent-result.json`; the "still running" note in
`logs/geng-twelve-result.json` was written before that audit finished. The empty `logs/geng-twelve-36.g6`
and its `.log` belong to an unfinished, unpartitioned first run, superseded by the 32
completed parts. Some programs write
their outputs to folders of the original repository (for example `reports/585-overnight`); change
those paths to rerun them.

## Papers (`papers/`)

One folder per argument of the findings document, each with the written argument, its reviews, and any certificate or replay files: `quartic/`, `qb5/` and
`six-port-gadget/` (section 4.1; G110 is the question that section now settles), `twin-core/` (4.3),
`census-extension/` (4.4), `r1-substitution/` (4.6), `lemma-f/`, `bipartite-hamilton/` (BM-2),
`extraction-attempt/` (E110) and `vertex-deletion/` (V110) for 4.7, `r1plus-recoloring-barrier/`
(4.8), and `pairs/`, `b6-24/`, `s6/` and `p4-attempt/` (section 5). Section 4.5 relies on published
papers only.

`quartic/` holds the written proof of QB(4) and P_2 (`C1-PAPER.md`, a byte-for-byte copy:
`shasum -a 256 -c C1-FROZEN.sha256` succeeds in that folder), its three reviews with each referee's own
code (`C1-REVIEW.md` and `review-1-code/`; `C1-REVIEW-2.md` and `review-2-code/`; `C1-REVIEW-3.md`,
its log `C1-REVIEW-3-LOG.md` and `review-3-code/`), the one correction (`C1-CORRECTIONS.md`), the
checks of its appendix A (`c1checks/`), and the two earlier reports it cites. The second referee
re-derived every step and wrote its own code before reading the first review, but it was given
`C1-CORRECTIONS.md` at the start, which records the first review's verdict, its one fix and its two
optional observations; so it confirmed that fix rather than finding it. It was requested on a
different model, but every call in its transcript ran on Claude Opus 5.5, the first referee's model;
a note the third track's lead agent added at the top of `C1-REVIEW-2.md` corrects its closing
sentence ("Two referees on different models"). The third referee ran on Claude Fable 5.1 and was
told not to open the other reviews or the correction note before writing its verdict; its log shows
when it opened them. The earlier
reports are `PAPER.md` (with
`REVIEW.md` and `CORRECTIONS.md`) for the 4-factor criterion, and `REPORT.md` (with
`QUARTIC-REVIEW.md`) for the E4 reduction and the reductions behind P_2. `PAPER.md` is also a
byte-for-byte copy of the file frozen at the SHA-256 that `C1-PAPER.md` appendix B cites. The proof's
plain-text file paths point into the private repository; the files they name that matter here are in
this folder. `REPORT.md` remarks that the Alon-Friedland-Kalai method needs more than 3n edges at
maximum degree 6; section 4.1 of the findings document supersedes that remark ([AFK84, Remark 3.6]
applies from 3n − 2 edges in bipartite graphs, and [AFK84, Theorem 3.1] from more than 3n − 2 edges
in loopless multigraphs, when the maximum degree is at most 7).

`qb5/` holds the written proof of QB(5) (section 4.1; the Lean proof, `Erdos585.qb5`, is in the public
repository's `Openmath/Proofs/QB5/`): four papers, each frozen with its hash list
(`FROZEN.sha256` to `FROZEN4.sha256`) and each with its referee's report. `PAPER.md` shows that a
smallest counterexample to QB(5) is an E5 instance, two blocks joined by seven edges, and states the E5
pair statement (some G − p − q has a 4-factor), which implies QB(5) (`REVIEW.md`); `PAPER2.md` proves
that statement for generic blocks, hence for n ≤ 26 (`REVIEW2.md`); `PAPER3.md` reduces it to one block
lemma, KL1, using a computed lemma, its Lemma 4.1 (`REVIEW3.md`); and `PAPER4.md` proves KL1, hence
QB(5) (`REVIEW4.md`). Read section 0 of `PAPER4.md` first; its section 1.1 says how the fixes the first
three reports require are carried. All four reports are final and found no mathematical error;
`REVIEW4.md` requires one wording fix (J1) that the frozen `PAPER4.md` does not carry: the paper's
account of its own computer checks overstates which lemmas they test. The code and data that the
hash lists name are in `code/` (two of the files are in `review3/data/`). Each referee's own code and
log are in `review/` to `review4/`, without compiled binaries; the referees' other data are not
included. `shasum -a 256 -c` on the four hash lists succeeds in that folder except for two files
whose local paths are replaced here: `code/generic_check.py` (named in `FROZEN2.sha256` and
`FROZEN3.sha256`) and `code/run_all.sh` (in `FROZEN.sha256`); `PROVENANCE.json` records both edits.
The author and the four referees were Claude Opus 5.5 agents of the third track. The papers' file
paths point into the private repository, where this folder is `reports/585-next/wave4/qb5/`.

`pairs/` holds the third track's pairs paper (`PAPER.md`, byte for byte, with `FROZEN.sha256`), its
final review (`REVIEW.md`: accept with fixes; read its fixes F1 to F6 with the paper), and the
certificates behind section 5, question 3: the 20-vertex example (`data/rigid20.g6`) and the six
11-vertex counterexamples with their marked edges (`data/t1_none.txt`, checked by `verify_t1.py`).
`SCOUT.md`, the pairs lane's notes, states two of the censuses of section 5, question 2 (H22 in
its section 2.3, L5 in its section 2.4) and the spanning-pair runs of its section 2.1, the second
method for census F2; their programs and records are in `census/pairs-lane/`. Its lemmas are
drafts of those in `PAPER.md` (numbering in its section 5); the review's fixes F1 (its Lemma 1.4
needs |S| ≥ 3) and F5 (the T2 count in its sections 0 and 3.2 is 6, not 82) apply to it.

`b6-24/` holds the written proof that every bipartite 6-regular graph on at most 24 vertices has a
pair (section 5, question 2). `theory/` has the rigid-set paper (`PAPER.md`) and its addendum
(`ADDENDUM-B.md`: Theorem B and Corollary B, no smallest E4-type counterexample to W1b on at most
22 vertices), each byte for byte with its hash list (`FROZEN.sha256`, `FROZEN-B.sha256`), one
referee report for both (`REVIEW.md`: the results the chain uses are accepted; its fixes P1 and P2
reword two statements of section 7 (P2 also the results-table row of Lemma 7.3) and P3 corrects
stale counts in the "Evidence" paragraph of section 6.2; P4 and P5 are optional), the referee's
log and code (`review/`), the note `N.md`, whose step 1 is the reduction from B to B − o, and the
records that the paper's appendix A and the addendum's section 5 cite: the 5 + 5 census
(`final_checks.sh`, `census55*`), the side census of Lemma B2 (`census_side.*`, `cs_*`), the SAT
model of Theorem B (`lemmaB_sat*`), the LP and identity checks, and the direct census at 20
vertices (`run_b6_20.sh`, `b6_20_part_*.err`). The repair experiments `exp1` to `exp12` (except the
library `exp11lib.py`, which `check_identities.py` imports), `FLAW.md` and the graph lists are not
included. `c1type/` has the C1-type paper (`PAPER.md`: Theorem C and Corollary C, byte for byte
with `FROZEN.sha256`), its referee report (`REVIEW.md`: Theorem C accepted; Corollary C accepted
with fix F1, which corrects the provenance of census F2; fixes F2 to F4 replace stale status words
in sections 0, 7 and 8; read them with the paper), the referee's log and code (`review/`), and the
author's SAT checks (`code/`). The referee settled by computation the one shape the author's model
left open (`review/code/n23k44_enum.out`, `k44free_*`, `k44split_*`); `review/code/n23_55_free.*`
and `k44free_y1b1_d5.*` are stopped runs, not cited. The chain also uses Lemma 1 and Proposition 5
of `pairs/PAPER.md` and Lemma 4.4 of `quartic/C1-PAPER.md`. Authors and referees were third-track
agents (section 7). The papers' paths point into the private repository, where these folders are
`reports/585-next/wave4/theory/` and `reports/585-next/wave4/c1type/`.

`s6/` holds the first paper of the S6 theory lane (`PAPER.md`, byte for byte with `FROZEN.sha256`)
and its referee's report (`REVIEW.md`: nothing rejected; fixes to wording, citations and framing).
Section 5, question 3 uses only its Lemma 1.1 (B − o is sparse if and only if B is E10, for every
o; accepted) and its section 6 (Corollary 6.6, accepted; read lines 288-289 with the report's fix:
"S6 gives B6 once such cuts are ruled out"). Its Lemma K, the route of its Theorem 4.1, was later
shown false on a 28-vertex graph in a separate paper with its own review, not included; Lemma 1.1,
S6 and section 6 are not affected.
`p4-attempt/` holds the unreviewed P_4 attempt (`PAPER.md`, byte for byte, with `FROZEN.sha256`;
`FLAW.md`): the certificates of section 5, question 4 (`checks/data/out_deep.json`, re-decided by
`checks/check_deep.py`), the 11-vertex graph of section 4.1 (`checks/data/qb8_counterexample.g6`) and
the logs of the n = 13 minimal-counterexample search (`checks/data/spq4_n13_*.err`).

These are the project's working documents, copied verbatim with three kinds of edit: absolute local
paths are shown as `[local path]`, `[temporary path]` or `[local scratch folder]`, or replaced by
the supplement path or archive name they stand for, link targets are remapped into this folder or marked "not
included", and one sentence of `r1-substitution/PROOF-R1.md` about an integer program is corrected
against its own log. Other edits, each marked or recorded: the copyright line of the Lean files
written for this project is matched to the public repository; in `bipartite-hamilton/` and
`extraction-attempt/PAPER.md` a few passages outside these findings are omitted, each omission marked
in the text; in three working documents the name of the author's task tracker is replaced by a
description; one path in a graph file's header is relocated to the public layout; and in the
Markdown working documents that no hash list names and no other file cites by hash, British
spellings are changed to American ones.
One more edit is recorded only in `PROVENANCE.json`: `checks/leanchecker-main-oct4.tsv` omits the row
of one Lean file that is not part of this release (its other rows include a few scratch
modules of the project, which are not shipped either). `PROVENANCE.json` lists each file's source
path in the author's private working repository, its SHA-256 and every edit. Where a report has a correction header, the header
takes precedence over the body. Line numbers that working documents cite in the findings document or
in each other refer to the versions current when they were written. The byte-for-byte frozen copies
(`C1-PAPER.md`, `quartic/PAPER.md`, `pairs/PAPER.md`, `p4-attempt/PAPER.md`, `b6-24/theory/PAPER.md`
and `ADDENDUM-B.md`, `b6-24/c1type/PAPER.md`, `s6/PAPER.md`, and the papers, reports and hash-listed
files of `qb5/` apart from the two noted there) keep their original interpreter and
cache paths, so that their hashes verify; home-relative cache paths (`~/.cache/erdos585/...`) are kept
as written in the other files too. Scripts that name a local interpreter or path, shown
as `[temporary path]` or `[local path]` (for example `papers/quartic/c1checks/run_all.sh` and
`census/calibration/programs/oracle_plain.py`), need that path set before a rerun.

## Glossary of the working documents

- **Codex**, the lead agent (in the numbered passes), root, coordinator: the OpenAI Codex agents
  (GPT-6 Astra) that ran the project's numbered research passes; only the lead ran the result checker.
- **lead**, **lead agent**, **research lead** (in the third track's documents): the Claude Opus 5.5
  agent that ran the third track of section 7, wrote its subagents' briefs, and added the note at the
  top of `papers/quartic/C1-REVIEW-2.md`. Not the author of the findings document.
- **Fable**: the Claude Fable 5.1 track on degree six, with Claude Opus 5.5 subagents. "Fable R1" is
  Theorem R1 of the findings document.
- **Opus**, wildcard: the Claude Opus 5.5 track that extended the census and wrote BM-2 (Theorem BM in its working documents).
- **lane**: a parallel research track. **subagent** or **reviewer**: an AI agent given one task.
  **scout**: a short exploratory attempt.
- **pass N**, **Attempt N**: the project's numbered research rounds.
- **rung (a) to (d)**: result categories: (a) proof, (b) special case, bound or counterexample,
  (c) literature find, (d) formalization.
- **check.sh**, **oracle**, **PASS**: the result checker described in section 3 of the findings
  document, and its success line.
- **S10**: the census statement called W1 in the findings document.
- **E110**, **V110**, **G110**: statements named after research pass 110, where they were stated.
- **R1-plus**: the recoloring barrier of section 4.8, Lean name `ParabolaBarrier104`.
- **B2** names unrelated things in different files: check B2 of `papers/r1-substitution/REVIEW-R1.md`
  (and the programs `census/programs/block-dp/b2_*.py` named after it), "Lemma B2.2" in
  `papers/bipartite-hamilton/` (a lemma of its bipartite part), the fact (B2) of
  `papers/qb5/PAPER2.md`, Lemma B2 of `papers/b6-24/theory/ADDENDUM-B.md`, the facts B2a to B2c of
  `papers/r1-substitution/FACTS.md`, item (B2) of `papers/s6/PAPER.md` section 4.1, and the petal type
  T_B2 in the `qb5` C code.
- **P_c**, **QB(c)**: "maximum degree at most 6, n ≥ 2 (n ≥ 3 when c is 5 or 6, n ≥ 4 when c is 7)
  and at least 3n − c edges give a nonempty 4-regular subgraph", for all graphs (P_c) and for bipartite graphs
  (QB(c)). QB(4), QB(5) and P_2 are section 4.1; P_4 is open (section 5); QB(6) and QB(7) appear in
  `census/edge/`.
- **ex(n)** (in `census/edge/`): the largest number of edges of a bipartite graph on n vertices with
  maximum degree at most 6 and no nonempty 4-regular subgraph. **Lemma A**, **Lemma B** there are
  the two lemmas of `EX.md` section 3; **method 1** and **method B** are the two computations.
- **C0, C1, E3, E4** (C_j, E_d): the instance classes of section 1 of `papers/quartic/C1-PAPER.md`.
  **G110-quartic**: the vertex-deleted form of section 4.1.
- **F1(N)**, **F2(N)** (in `census/quartic/CENSUS.md`): bipartite graphs with minimum degree at least
  4, maximum degree at most 6 and at least 3n − 6 (F1) or 3n − 4 (F2) edges, up to N vertices, have a
  4-regular subgraph. **Census F2** (in `papers/pairs/` and `papers/b6-24/`) is the pair statement
  with the hypotheses of F2(N): W1b through 18 vertices, the bipartite part of row 13 of the findings
  document. Neither is a fact (F1) to (F3) of `papers/b6-24/c1type/PAPER.md` or (F0) to (F3) of
  `papers/s6/PAPER.md` section 6, the set types F1 and F2 of Lemma 3.1 of
  `papers/b6-24/theory/PAPER.md`, or a fix label: F1 to F6 of `papers/pairs/REVIEW.md`, F1 to F7 of
  `papers/qb5/REVIEW.md` and of `papers/b6-24/c1type/REVIEW.md`, or the checks F1 to F5 of
  `papers/qb5/PAPER4.md` section 5.
- In `papers/qb5/`: F1 to F7, G1 to G3, H1, and J1 and J2 are the four referees' fix labels; (H1) to
  (H3) in `PAPER4.md` are hypotheses, and (B1), (B2) in `PAPER2.md` are facts.
  The lane's own ladder has rung 1 (a proof of QB(5)) and rung 2 (a reduction to an exactly stated
  remainder), not the rungs (a) to (d) above.
- **Pass 3**, **wave**, **M1**, **M2**, **M3**, **M3-R**, **author lane**: the third track of section 7
  (not research pass 3 of the numbered Codex rounds), its rounds, and its author and referee
  subagents.
- **W1b**: W1 for bipartite graphs (section 5, questions 2 and 3). **T1**, **T2**: two computations in
  the pairs notes; T1 is the marked-edge statement of section 5, question 3.
- **VA6**: the vertex-deleted form of B6 (section 5, question 2).
- **S6**: for a bipartite 6-regular graph B and a vertex o: if Γ = B − o is sparse (g(S) ≥ 10 for
  every S with 2 ≤ |S| ≤ |Γ| − 1), then Γ − y has two edge-disjoint Hamilton cycles for every port
  y (section 5, question 3).
- **E10** (essentially 10-edge-connected): every edge cut with at least two vertices on each side
  has at least 10 edges. B − o is sparse exactly when B is E10 (`papers/s6/PAPER.md`, Lemma 1.1).
- **port**: a vertex of degree at most 5 on the larger side of a C1 or C0 instance
  (`papers/quartic/C1-PAPER.md`, section 2; the classes are defined in its section 1); it is *bad*
  if removing it leaves no spanning 4-regular subgraph (Lemma 4.4 there). B − o is a C0 instance,
  and its ports are the six neighbors of o.
- **L5**: no pair-free bipartite graph with minimum degree at least 4, maximum degree at most 6 and
  3n − 5 edges (level −5) has at most 17 vertices (`papers/pairs/SCOUT.md` section 2.4,
  `census/l5/`).
- **H22** (**H18**, **H20**, **H_m**): every connected bipartite 4-regular graph on at most 22 (18,
  20, m) vertices with no 2-edge cut has a Hamilton decomposition (**HD**)
  (`papers/pairs/SCOUT.md` section 2.3, `census/h22/`).
- **5 + 5 census**: no pair-free bipartite graph on 5 + 5 vertices has 22 or more edges
  (`papers/b6-24/theory/census55.out`).
- **Theorem B**, **Corollary B**, **Lemmas B1 to B3** (in `papers/b6-24/theory/ADDENDUM-B.md`),
  **Theorem C**, **Corollary C**, **Lemma C1**, **Proposition C2**, **Lemma C3**, **Theorem C3**,
  **Lemma C4** (in `papers/b6-24/c1type/PAPER.md`): steps of section 5, question 2. Not Corollary B
  of `papers/r1-substitution/PROOF-R1.md` (section 4.6).
- **P1** to **P5** (in `papers/b6-24/theory/REVIEW.md`): that referee's fix labels.
- **AM walk** (in `census/s6n22/`), **frame**, **Φ** (there and in `papers/s6/`): the randomized
  recoloring search of the S6 program and its state; a frame with Φ = 2 gives two edge-disjoint
  Hamilton cycles (`papers/s6/PAPER.md`, Lemma 2.3). The program uses it only to find pairs, which
  it checks.
- **shard**, **slice**: one of the parts `r/mod` into which nauty's generators split their output.
- **briefed hints** (section 6 of `C1-PAPER.md`): suggestions given to the author agent at the start
  by the third track's lead agent; that section checks each one. H10, the route of its sections 3
  and 4, is one of them; the lead agent first proposed the uncrossing of ports in a message to an
  earlier author subagent.
- **AGENTS.md**, **CONTINUE.md**, **585-RESEARCH-PLAN.md**, **STATE.md**, **CHECKPOINT** and
  **FINAL-SYNTHESIS** files: the agents' instructions and planning notes in the private repository;
  not included. Paths starting with `reports/` (in `PROVENANCE.json` and in the working documents) are
  folders of the private repository, kept for provenance.
- **harness**, **worktree**, **model override**, **nested-agent request**, **SendMessage**, **main**
  (the lead agent, as a message recipient), **session scratchpad**: terms of the agent
  software. **ref2**, **fresh92** and similar names: individual reviewer agents or their folders.
- **SMS**: SAT Modulo Symmetries, the solver of `papers/census-extension/`.
