# exb jobs (method B)

**Status: finished.** All 313 shards ended with status 0 by 10:48:31 EDT; 0 output graphs in every
job; 5,151 core-s of user CPU; the driver exited after running the collector (`data/COLLECT.md`,
`EX-B.md` section 1). Worker cap changes are logged in `logs/driver.log` (3 while a foreground
check ran, 3 two-process pipelines in the whole-class phase).

Launched 2026-10-06 10:18:16 EDT. One driver, detached with `nohup`, `nice -n 10`. Workers: 4
before 11:00 EDT, 6 from 11:00 (the machine is shared with a census job until about 11:00);
`data/WORKERS` (a number) overrides. Each shard runs under `timeout 3000`. When the queue is done
(or after STOP), the driver runs `code/collect.py`, which writes `data/COLLECT.md` and the results
block of `EX-B.md`.

## Process

| What | Value |
|---|---|
| Driver PID | 34809 (exited 10:48:31 EDT; `logs/driver.pid` is removed at exit) |
| Driver command | `nohup nice -n 10 /bin/bash code/run_exb.sh drive` (started by `run_exb.sh launch`) |
| Driver log | `logs/driver.log` (one line per finished shard) |
| Job table | `code/jobs.tsv` (13 jobs) |
| Work list | `code/queue.txt` (313 lines, run in order) |
| Shard files | `logs/<tag>/shard_<r>.{g6,err,done}`; a shard counts only if its `.done` says `status 0` |

## Jobs

Binaries: `code/bin/bipgen` (own generator, own decider `code/h4.h` as the prune) and
`code/bin/h4filt` (own decider on every graph); SHA-256 in `code/BUILD.txt`.

| Tag | Command (shard r of mod) | Shards | Projected core-s | What it settles |
|---|---|---|---|---|
| pr_n17_e44_8x9, pr_n17_e44_9x8 | `bipgen 8 9 44:44 4:4 6:6` and order 9 8 | 1 + 1 | 4 | n = 17, e = 44, both class orders |
| pr_n18_e47_8x10, pr_n18_e47_10x8 | `bipgen 8 10 47:47 4:4 6:6` and order 10 8 | 1 + 1 | 13 | n = 18, e = 47, sides 8 + 10 |
| pr_n18_e47_9x9 | `bipgen 9 9 47:47 4:4 6:6 r/4` | 4 | 60 | n = 18, e = 47, sides 9 + 9 |
| pr_n19_e51_9x10_d5, pr_n19_e51_10x9_d5 | `bipgen 9 10 51:51 5:5 6:6` and order 10 9 | 1 + 1 | 24 | n = 19, e = 51, δ ≥ 5 (cross-check; implied by e = 50) |
| n19_e50_9x10 | `bipgen 9 10 50:50 4:4 6:6 r/50` | 50 | 580 | n = 19, e = 50 |
| n19_e50_10x9 | `bipgen 10 9 50:50 4:4 6:6 r/50` | 50 | 900 | n = 19, e = 50, other class order |
| wh_n17_e44_8x9 | `bipgen -P -q 8 9 44:44 4:4 6:6 \| h4filt` | 1 | 55 | whole class, no pruning, every graph decided |
| wh_n18_e47_10x8 | `bipgen -P -q 10 8 47:47 4:4 6:6 \| h4filt` | 1 | 21 | same, sides 8 + 10 |
| wh_n19_e51_10x9_d5 | `bipgen -P -q 10 9 51:51 5:5 6:6 \| h4filt` | 1 | 90 | same, n = 19, e = 51, δ ≥ 5 |
| wh_n18_e47_9x9 | `bipgen -P -q 9 9 47:47 4:4 6:6 r/200 \| h4filt` | 200 | 6,000 | same, sides 9 + 9 (1,316,086,566 bicolored graphs; 3,447 core-s) |

Projected total: about 7,700 core-s (2.1 core-h) at pilot speed, plus about 0.3 core-h of pilots
and checks. The load average was about 46 on 18 cores at launch, so wall time is longer than CPU.

## Commands

Status (prints the table, writes nothing):

```
/bin/bash [local path] status
```

Graceful stop (running shards finish, nothing new starts, then the collector runs):

```
touch [local path]
```

Immediate stop (then run the collector by hand):

```
touch [local path]
pkill -f 'wave8/exb/code/run_exb.sh'
pkill -f 'bin/bipgen'
[local path] [local path]
```

(`pkill -f 'bin/bipgen'` matches only this lane's generator; no other lane uses that name.)

Resume (skips finished shards, clears stale claims; refuses if a driver is alive):

```
rm -f [local path]
/bin/bash [local path] launch
```
