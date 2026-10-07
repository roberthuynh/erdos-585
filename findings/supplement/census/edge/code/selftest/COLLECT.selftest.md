# excensus collector output

Collected 2026-10-05 23:54:15 EDT by `code/collect.py`.

| Job | Class | Shards done | Output graphs (no 4-regular subgraph) | user CPU s | Status | Re-check of output |
|---|---|---|---|---|---|---|
| selftest_q4 | control: expect 24231 graphs in total | 4/4 | 24231 | 0 | COMPLETE | 24231 graphs: pysat says no 4-regular subgraph for 24231; q4filter says none for 24231 |
| selftest_sat | control: expect UNSAT 485 in total | 2/2 | 485; generated 28960, SAT 28475 | 7 | COMPLETE | 485 graphs: pysat says no 4-regular subgraph for 485; q4filter says none for 485 |

Conclusions drawn by the collector (rules in EX.md section 4):

- ex(18) ∈ {46, 47} for now: n = 18, e = 47 (9 + 9) is 0/? shards done, 0 graphs so far.
- ex(19) ∈ {49, 50} for now: n = 19, e = 50 (9 + 10) is 0/? shards done, 0 graphs so far.
- ex(20) ∈ {52, 53, 54} for now (needs ex(19) = 49 and the e = 54 run: 0/? shards done).
- selftest_q4: 4/4 shards, 24231 output graphs (complete).
- selftest_sat: 2/2 shards, 485 output graphs (complete).
