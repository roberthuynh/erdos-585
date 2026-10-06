# s6spot jobs: independent spot-check of wave6/s6n22 (S6 at |B| = 22)

Lane wave8/s6spot, 2026-10-06. Rung (b) computation. Nothing leaves this machine. No check.sh.

## What runs

`data/jobs.txt`, 53 jobs, 4 workers (`xargs -P 4`), nice 10, detached (own session):

- 3 jobs `e10only`: slices 5491, 7913, 8360 (the slices where s6n22 recorded one non-E10 graph
  each). genbg, then `code/e10cut` on every graph (count and E10 comparison), then SAT only on the
  non-E10 graphs (informative).
- 50 jobs `full`: the first 50 slices of `data/sample_order.txt`, a uniform random permutation of
  0..9999 from a fresh seed recorded in `data/sample_seed.txt` (1931695848). Slice 1881 (the pilot)
  already has its done marker and is skipped. Per slice: genbg with the original's flags
  (`genbg -X-3 -d6:6 -D6:6 11 11 r/10000`, the same binary as s6n22:
  `~/.cache/erdos585/nauty2_9_3/genbg`), `code/e10cut` (exact minimum essential cut, exhaustive
  Gray-code enumeration, C), `code/spantest.py` (PySAT, all 66 edges of every E10 graph, every
  witness re-verified).

Per-slice outputs: `data/slices/s<r>.{g6,genbg.err,cut,e10.err,span.json,span.log,no,done}`.
Progress lines: `logs/progress.log`. Failures: `logs/failed.txt`. Driver log: `logs/driver.log`.

## Process (launched 2026-10-06 09:53:28 EDT)

- Driver PID **98838**, process group 98838 (`logs/driver.pid`).
- No new slices after 11:25 EDT (STOP_EPOCH 1791300300); the group is killed at 11:40 EDT
  (KILL_EPOCH 1791301200). Projection from the pilot (18.5 ms per graph, 588k graphs): about
  3.0 core-hours, finishing about 10:45 EDT.
- When the workers finish, the driver runs `code/collect.py` (writes `data/collect.json`,
  `data/compare.md`).

## Commands

- Graceful stop (in-flight slices finish):
  `touch [local path]`
- Hard stop: `kill -TERM -- -98838`
- Progress: `ls [local path] | wc -l` (of 53)
- Resume (done slices are skipped):
  `cd [local path] && rm -f STOP && W=4 ~/.cache/erdos585/venv/bin/python code/launch.py`
- Collect any time: `~/.cache/erdos585/venv/bin/python [local path]`

## Final state (2026-10-06 10:52:26 EDT)

The driver finished: 53 of 53 jobs done, no failed slices (`logs/failed.txt` absent), `driver end`
in `logs/driver.log`. collect: 50 random slices, 588,094 graphs, all E10, 38,814,204 tests, all
SPAN with verified witnesses, 0 NO, every per-slice count equal to s6n22's. Max-flow sample 103/103.
Result: `SPOTCHECK.md`. No process of this lane is running. The slice `.g6` and `.cut` files are
gzipped (`data/slices/SHA256SUMS` lists the uncompressed files; all 106 verified after gzip).
