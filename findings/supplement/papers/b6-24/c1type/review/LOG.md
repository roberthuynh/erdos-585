# c1type referee LOG
2026-10-05 19:06:37 referee start; FROZEN.sha256 check: PAPER.md OK; created review/ and review/code/
2026-10-05 19:07:47 read c1type PAPER (393 lines), THEORY PAPER, ADD-B, THEORY REVIEW. Next: PAIRS PAPER+REVIEW, C1P Lemma 4.4, SCOUT H22/L5
2026-10-05 19:39:04 read PAIRS PAPER+REVIEW, C1P Lemma 4.4 (bad ports deficiency <= 2, needs only sparse C1 with D_U = 1: OK), SCOUT H22/L5 tables, author NOTES. Hand re-derivation of PAPER §1-§5 in progress (Lemma C1, Prop C2, C3, §4.1-4.3 all checked so far, no gap found)
2026-10-05 19:58 RESUMED after stall (coordinator message). State: hand re-derivation of PAPER done line by line:
  - §1 setting, (F1) density consequences, (F2), (F3)/(1.2) via PAIRS Prop 5 (|S|>=3) + L5 for |S+w| <= 17: OK.
  - (K): no bad set => connected, no <=2-edge cut (cuts <=2 are balanced) => H_m: OK.
  - Lemma C1 (a),(b),(c): OK (t=2,3 killed by e >= 4t-1 > t^2; nested pairs need |M| >= 8).
  - Prop C2 (THEORY 6.6 transfer): re-derived in Y incl. |M| <= m-16 <= 6, xy in F' cases: OK.
  - Lemma C3, 5+5 side (alpha/beta), (D3): OK.
  - §4.1 n=19, 21, 23 (K44-e): OK. n=23 endgame: good sets have r=6, t in {4,5}, s=1; z=q'; Z_P vertices
    have both H-edges to q1 -> even 2 parallel edges per x; contradiction holds.
  - §4.2 (n=21, 10|10): counts, covering, (3), (4) all OK.
  - §4.3 Lemma C4 (all t,r cases), Steps 1-5: OK.
  - Corollary C: OK.
  FINDING (provenance, not math): PAPER §8 row "Census F2 ... two methods" is wrong for the pair version:
  census/CENSUS.md Job 1 replication (geng_q4/genbg_q4) decides 4-regular subgraphs, not pairs. F2 (pairs,
  n <= 18) is one method (geng -b + pairc, 585-fable CHECKPOINT-02/05). PAIRS referee said the same.
  NEXT: own SAT model (code/), all shapes + controls; K44-e|7+7 at n=23 by enumeration of F[B] (genbg) + SAT
  per F[B], and/or WLOG split.
2026-10-05 21:07:00 census records: census55 files give pair-free 125,62,24,8,0,0,0,0 (e=18..25) = THEORY App A; THEORY referee made it two methods (PAPER §8 says one: understated, optional fix). genbg -d3:3 -D4:4: F[B] classes 7+7: 208, 6+6: 14, 5+5: 2 (= alpha/beta, confirms D2). Plan: own SAT (code/c1ref.py) with F[B] enumerated per class, plus fB-variable model. Writing code now.
2026-10-05 21:08:42 code/c1ref.py + run_shape.py written; fb5/fb6/fb7.g6 = 2/14/208 classes. n19k44 enum: 4/4 UNSAT, controls nostar 4/4 SAT with one-crossing (independent BFS checker).
2026-10-05 21:11:11 timing n23k44 enum (fixed F[B], lean k44w+r12): idx0 1-2 s, idx50 16 s, UNSAT with 0 lazy cuts so far; adding A-side lex symmetry breaking (S3 x S3) to cut cost
2026-10-05 21:12:14 symA (lex on A_P-p1, A_Q-q1) speeds idx50 deg5 from 123 s to 4 s (CaDiCaL 1.9.5; kissat 9.7 s). DETACHED: run_shape.py n23k44 enum levels=k44w,r12,symA workers=6 -> code/n23k44_enum.out (416 jobs)
2026-10-05 21:13:37 n21k44 enum (k44w,c55): 28/28 UNSAT. n21_55 enum (eHB2): 176/176 UNSAT, qfree 176/176 UNSAT, controls nostar 176/176 SAT with one-crossing (BFS checker). Encoding tests: enc_test.py relax2 (star SAT models: 160, none with one-crossing); enc_test2.py random direct configs 3000 (1500 dense + 1500 sparse, 157+13 without one-crossing): star model with main vars fixed SAT iff no one-crossing, 0 disagreements.
2026-10-05 21:15:33 n23_55 enum (k44w, r12 lean): 1232/1232 UNSAT (44 A sides incl. 12 with a pair x 14 F[B] x 2 deg w); controls nostar 1232/1232 SAT w/ one-crossing; n21k44 nostar 28/28 SAT. Free-F[B] formulation: n19k44 2/2 UNSAT, n21k44 (k44w,c55,symA) 2/2 UNSAT (3 s, 23 s). n23k44 enum at 259/416, all UNSAT so far.
2026-10-05 21:15:39 n21_55 free: 88/88 UNSAT. DETACHED: n23_55 free (limit 120 s/instance, 4 workers) -> code/n23_55_free.out
2026-10-05 21:16:53 n23_55 free stopped after 3 UNSAT (17-51 s each; redundant second formulation, budget). n23k44 enum 392/416 UNSAT, cpu 1556 s. Compute so far ~0.6 core-h.
2026-10-05 21:18:43 RESULT n23k44 enum (lean k44w + r12, symA): UNSAT 416/416 (208 F[B] classes x deg w 4,5), wall 291 s on 6 workers (~1700 core-s). aside_pairs.py (own networkx pair test): 44 5+5 sides: 12 pair, 32 pair-free, PAPER rule agrees 44/44; controls K44 pair, K44-e none. Next: second formulation for K44|7+7 = free F[B] + generic lex-leader symmetry breaking (symG).
2026-10-05 21:19:42 coordinator (from Robert via lead): settle K44-e|7+7 at n=23 by computation too; up to ~4 core-h for that case; detached nohup jobs, symmetry split as ADD-B referee; own line in REVIEW.md. Status: method 1 (genbg F[B] enumeration + own SAT, symA) already UNSAT 416/416. Now method 2: free F[B] + WLOG symmetry split (generic y1 carries an E0H edge, to p' or to b1) + lex-leader for the residual group (symG), detached.
2026-10-05 21:20:51 symG implemented (generic lex-leader for adjacent transpositions under one global order; WLOG cases y1pp/y1b1 for free F[B]). test_symG.py: lex clauses with main vars fixed SAT iff x >=lex tau(x) for all generators, 1500 tests (750 local lex-max positives), 0 disagreements.
2026-10-05 21:21:05 n21k44 free + WLOG split + symG: UNSAT 4/4 (0.1-1 s); nostar controls SAT (n21k44, n23k44, both cases). DETACHED method 2: run_k44free.sh 3000 -> code/k44free_{y1pp,y1b1}_d{4,5}.out (4 jobs, 3000 s cap each)
2026-10-05 21:21:23 RESUME rewritten; method-2 jobs running since 21:20 (4 cores). Drafting REVIEW.md.
2026-10-05 21:22:20 author's SAT records match PAPER §7 (n19 UNSAT+ctrl SAT; sat21_y 66 UNSAT, ctrl 66 SAT; sat21_proof 88 UNSAT 5+5|5+5; sat23_y 64 UNSAT + K44 timeouts; allA 88 UNSAT; k44/k44p TIMEOUT; check_aside 12/32). Polling method-2 jobs.
2026-10-05 21:22:54 method 2: case y1pp deg4 UNSAT (90 s). Others running.
2026-10-05 21:24:15 REVIEW.md DRAFT written (verdicts, fixes F1-F6, K44 line pending method 2).
2026-10-05 21:24:41 method-1 controls: n23k44 enum nostar (k44w,r12,symA) 416/416 SAT with one-crossing; decoded models K44-free in X[B+w] (checker) for n23k44, n23_55, n21k44 controls.
2026-10-05 21:25:17 compute so far ~0.9 core-h (method 1 solver time 1720 s). Machine load avg ~47 (other lanes). Method 2: 3 jobs at ~3.5 min CPU each; note: limit only checked between lazy iterations, will kill manually at cap.
2026-10-05 21:26:07 Monitor armed on method-2 jobs (y1pp d5, y1b1 d4, y1b1 d5). Waiting.
2026-10-05 21:26:38 fb_cover.py (own, networkx VF2 + interchange random walk): 6+6 14 reps pairwise non-iso, 3000 samples all covered (14 hit); 7+7 208 reps pairwise non-iso, 6000 samples all covered (206 hit). genbg F[B] list consistent.
2026-10-05 21:26:59 method-2 jobs at ~5 min CPU each (load avg now ~22). Plan: if not done by ~20 min CPU, add a complete u1/N(w) case split as a hedge.
2026-10-05 21:27:20 hedge script code/run_k44free_split.sh ready (u1 position split, 11 jobs per (case, deg w)); smoke test on n21k44 OK (UNSAT with star, SAT without).
2026-10-05 21:28:03 observation: every n=23 enum model (416 K44 + 1232 5+5|6+6) was UNSAT at the first solve, iters=1 cuts=0: no (1.2) cut was ever added, so the computer check of Theorem C3 at n = 23 does not use (F3)/L5 (only F2, D1/D2, no K44 in X[B+w]). Same for method-2 y1pp d4.
2026-10-05 21:28:44 REVIEW F1 reworded: second method for 'no smallest counterexample n<=18' is SCOUT §2.1 (genbg+ptool on E4 a<=9, C1 s<=8), not STATE F2-rep (4-regular only).
2026-10-05 21:29:28 tnok44.py: 6 sampled K44|7+7 instances (classes 0, 50, 207 x deg w) UNSAT with NO B-side facts (no k44w, no r12): the shape seems to follow from F2 + D1 + counts alone (sample only, not claimed).
2026-10-05 21:29:44 REVIEW §3 updated (method-1 controls, no-L5 observation). Waiting on method 2 (3 jobs ~8 min CPU).
2026-10-05 21:30:24 check: method-1 run 21:12-21:17 used c1ref.py before the 21:20 symG edit (spawned workers import at start); symA logic unchanged since. Load avg 61; method-2 jobs ~8 min CPU.
2026-10-05 21:30:42 waiting on method 2 (y1pp d5, y1b1 d4, y1b1 d5 at ~8.3 min CPU).
2026-10-05 21:31:04 method 2 still running (~8.6 min CPU each); compute for the K44 case so far ~0.95 core-h of 4. Cap plan: stop method 2 at ~2.5 more core-h if unfinished.
2026-10-05 21:31:36 polling method 2; REVIEW draft re-read, counts in §3 checked against outputs.
2026-10-05 21:31:53 REVIEW §3: fb_cover result added. Waiting on monitor events for method 2 (no hedge launched; load ~25).
2026-10-05 21:35:59 method 2 at 12.8 min CPU each (3 jobs); K44-case compute ~1.15 core-h; cap ~22:30.
2026-10-05 21:39:40 method 2: case y1pp deg5 UNSAT (1106 s wall, iters=1). Case y1pp complete (d4 90 s, d5 1106 s). Remaining y1b1 d4, d5 (~16 min CPU each).
2026-10-05 21:43:52 method 2: case y1b1 deg4 UNSAT (1350 s, iters=1). 3 of 4 done, all UNSAT; y1b1 deg5 running (~19 min CPU). K44-case compute ~1.5 core-h.
2026-10-05 21:47:47 waiting on y1b1 deg5 (21.5 min CPU).
2026-10-05 21:52:55 probe: y1b1 deg5 with u1=A:0 UNSAT in 58 s. HEDGE launched: run_k44free_split.sh y1b1 5 (11 u1-position subcases, nice 10) -> code/k44split_y1b1_d5_*.out; unsplit y1b1 deg5 keeps running (25 min CPU).
2026-10-05 21:57:07 hedge y1b1 d5: 10/11 u1 subcases UNSAT (A0-A3, B1-B6; 41-107 s each); u1=B:0 (q') running; unsplit at 27.7 min CPU.
2026-10-05 21:57:35 RESULT method 2 complete: y1pp d4 UNSAT (90 s), y1pp d5 UNSAT (1106 s), y1b1 d4 UNSAT (1350 s), y1b1 d5 UNSAT via complete u1 split (11/11 subcases UNSAT, 41-249 s, 976 s total). Unsplit y1b1 d5 stopped at ~28 min CPU (redundant); orphan worker+tracker killed. No jobs running. K44-case compute ~1.96 core-h (method 1 1720 s, method 2 ~5245 s); lane total ~2.25 core-h.
2026-10-05 21:58:20 END: shasum -a 256 -c FROZEN.sha256 -> PAPER.md: OK. REVIEW.md FINAL written. No detached jobs running.
