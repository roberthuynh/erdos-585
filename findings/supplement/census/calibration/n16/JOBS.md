# reg5n16 jobs

Lane: `reports/585-next/wave6/reg5n16/`. Question: is there a 5-regular pair-free graph on 16 vertices?

## Running (launched 2026-10-06 03:48:05 EDT)

| What | PID | Nice | Notes |
|---|---|---|---|
| driver `code/driver.sh` | 57159 | 10 | parent of xargs; runs the collector when the shards stop |
| `xargs -P 16 -n 1 /bin/bash code/worker.sh` | 57170 | 10 | 16 workers, one shard each at a time |
| workers: `timeout <s> code/geng_pp -d5 -D5 16 r/20000` | many, short-lived | 10 | one shard is about 13-14 s |

Launch command (run from bash, not zsh, so zsh's background nice is not added):

```
cd [local path]
WORKERS=16 nohup nice -n 10 /bin/bash code/driver.sh >> logs/driver.log 2>&1 < /dev/null &
```

- Binary: `code/geng_pp`, SHA-256 `c8b8ee91...c45b5a789` (full hashes in `logs/driver.log` and
  `logs/build.txt`). Source `code/pairprune.c` SHA-256 `66347bb0...6894d10`.
- Shards: geng res/mod with mod 20000, in the shuffled order `data/shard_order.txt` (seed 585).
- Built-in stops: no new shard at or after 06:10:00 EDT; a running shard is killed by `timeout` at
  06:13:30; then the driver runs `code/collect.sh --quick` (under `timeout 40`) and exits by about
  06:14.
- Resumable: rerunning the launch command skips every shard with `logs/shards/<r>.done`.

## Stop

- Graceful (no new shards, running shards finish within about 15 s): `touch [local path]`
- Hard stop (everything in this lane, now): `pkill -TERM -f 'wave6/reg5n16/code/'`
- After a hard stop, run the collector: `bash [local path]`

## ETA

- Measured 03:48-04:12 EDT: about 1.03 shards per second with 16 workers (13-14 s per shard).
- The full census (20000 shards) needs about 5.4 h at that rate, so it does not finish before the
  06:10 cutoff. Expected coverage at 06:10: about 8,700-9,000 of 20,000 shards (about 44%).
- Coverage is recorded exactly: `data/done_shards.txt` (written by the collector).
- The driver runs `code/collect.sh --quick` at the end. If a graph was found, rerun
  `code/collect.sh` without `--quick` to add the SAT certificate and `FROZEN.sha256`.
