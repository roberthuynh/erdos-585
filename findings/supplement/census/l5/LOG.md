2026-10-05 21:28:20 EDT lane start: L5B second-method census; reading SCOUT.md 2.4
2026-10-05 21:31:43 EDT geng -b -d4 -D6 small n: n=10:1 11:2 12:9 13:29 14:448 (uncolored); n=15 timed
2026-10-05 21:33:37 EDT pilot geng: n=15 2895 (0.2s), n=16 116035 uncolored (2.7s), n=17 1/50 slices ~1.25s each (~62s total). Generation is cheap; decider cost dominates. Original: genbg + pairc (subset S then DFS Ham cycles). Referee: rpair (cycles grouped by vertex set). Mine: geng -b + SAT (PySAT) encoding with reachability-based connectivity, witness checked by separate verifier.
2026-10-05 21:37:21 EDT validate1 PASS: 3000 random (623 pair/2377 free) SAT=brute; 7 named ok; t1_Z 5625 + frontier 17 pair-free all UNSAT. Launched validate2 (bip n=12,13 sets, 378 graphs, brute) and validate3 (bip n=14 e=36 d4, 1144 graphs, brute) in background.
2026-10-05 21:39:58 EDT driver code/run_census.sh tested on n=10,12,14 (counts 1, 9, 448; swap autos 1, 5, 77 -> color-preserving 1, 13, 819 = original). Verifier negative test: 30 corrupted certificates rejected, 10 rotated (valid) accepted (data/validation/corrupt14.txt).
2026-10-05 21:40:07 EDT LAUNCHED full census: JOBS=6 nice 10 bash code/run_census.sh all, driver pid 79156; 64 shards n=17 (mod 64), 8 shards n=16 (mod 8), n=5..15 unsplit, stage-0 counts n=15,16,17.
2026-10-05 21:40:57 EDT poll: 3 shards done; collector code/collect.py written
2026-10-05 21:41:40 EDT heartbeat (monitor): 8 of 83 shards done, driver pid 79156, load 100.59 73.09 51.60
2026-10-05 21:44:40 EDT heartbeat (monitor): 22 of 83 shards done, driver pid 79156, load 97.48 84.05 60.25
2026-10-05 21:44:42 EDT superset plan: geng -b with a degree flag dropped, exact filter in code/superset_filter.py. Timings: -D6 only n=15 0.3s, n=16 3.6s, n=17 ~80s (slice 3/200 0.39s); no degree flags n=14 2.1s; -d4 only n=14 0.41s, n=15/16 timing in progress (slow).
2026-10-05 21:46:15 EDT superset n16 -D6 only: 181,327 read, 116,035 in class (= exact flags), 65,292 rejected mindeg. Launched code/run_superset.sh (nice 15, sequential) pid 13739: n=9..15 no flags, n=16 -D6 only/-d4 only, n=17 -D6 only in 4 shards. (-d4 only at n=16 costs >2 min CPU; at n=17 not attempted.)
2026-10-05 21:46:30 EDT timing: geng -u -b -d4 16 43:43 (no -D6) = 6,083,736 graphs, 139 s CPU; n=17 -d4-only slice timing running. Census: 30/83 shards done.
2026-10-05 21:46:57 EDT timing: geng -u -b -d4 17 46:46 3/200 = 3,072,146 graphs in 27.6 s -> full n=17 superset without -D6 ~614M graphs, ~1.5 core-h generation + ~5 core-h Python filter. Not run (bonus check only; the max-degree flag at n=16 is checked by n16_d4only, and n=17 by the count reconciliation).
2026-10-05 21:47:39 EDT superset no-flag counts n=9..15 (geng -b n 3n-5 only, exact filter): in class 0,1,2,9,29,448,2895 = exact-flag counts; supersets read 0,1,4,37,549,14176,592620. Census 35/83.
2026-10-05 21:47:41 EDT heartbeat (monitor): 35 of 83 shards done, driver pid 79156, load 135.43 106.38 74.03
2026-10-05 21:48:33 EDT poll: census 38/83 done, 0 FAIL; superset n17 -D6-only shard 0/4: 706,976 read, 255,749 in class; L5B.md method section drafted.
2026-10-05 21:50:41 EDT heartbeat (monitor): 50 of 83 shards done, driver pid 41035, load 115.33 110.90 82.08
2026-10-05 21:53:41 EDT heartbeat (monitor): 61 of 83 shards done, driver pid 41035, load 113.79 112.25 88.09
2026-10-05 21:55:16 EDT superset script ended, 0 FAIL
2026-10-05 21:56:41 EDT heartbeat (monitor): 69 of 83 shards done, driver pid 41035, load 143.76 121.98 96.37
2026-10-05 21:59:09 EDT census driver ended: 83/83 shards done, 0 FAIL. Collecting.
2026-10-05 21:59:37 EDT COLLECTED: 1,357,397 uncoloured graphs n=10..17, all in class, all SAT with certificates verified by verify.py, 0 pair-free, 0 exceptions, 0 problems; color-preserving totals match the original at every split (8+8: W=2157 -> 229,913; 8+9: 1,237,978; sum 1,471,650).
2026-10-05 21:59:49 EDT validate2 done (bad=0). Coordinator asked: collect (done), finish both brute-force validations, 8+8 check (W=2157, match), fill L5B.md.
2026-10-05 22:01:27 EDT L5B.md written with verdict (no pair-free graph; counts match original at every split; 1,357,397 certificates verified). Only placeholder left: validate3 row (n=14 brute force, still running).
2026-10-05 22:01:39 EDT validate3 done: 1,144 graphs n=14 e=36 d4, SAT = brute force on all (all with a pair). L5B.md complete; RESUME.md status updated. Lane done.
