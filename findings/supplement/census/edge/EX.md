# ex(n) for n = 17 to 20: bipartite, Δ ≤ 6, no nonempty 4-regular subgraph

Lane excensus (wave6), 2026-10-05 23:19 to 2026-10-06 EDT. ex(n) is the maximum number of edges of a
simple bipartite graph on n vertices with maximum degree at most 6 and no nonempty 4-regular
subgraph. Rung (b) throughout: computed bounds and exact values, no Lean, no `check.sh`.

## 1. Answer

The table between the markers is rewritten by `code/collect.py` from the shard files; it is current
as of its time stamp. The detached jobs A, B, C are listed in `JOBS.md`.

<!-- COLLECT:BEGIN -->
Written 2026-10-06 03:28:11 EDT by `code/collect.py` from the shard files; rules in section 3.

| n | ex(n) | Basis |
|---|---|---|
| 17 | **43** | complete. e = 44 (sides 8 + 9): 0 graphs in both class orders; e ≥ 45: census F1(17); lower bound `data/witness_n17.g6` |
| 18 | **46** | complete. e = 47: sides 8 + 10, 0 graphs in both orders; sides 9 + 9 (job A), 0 graphs; e ≥ 48: census F1(18); lower bound `data/witness_n18.g6` |
| 19 | **49** | complete. e = 50 (job B, sides 9 + 10): 0 graphs; e = 51 forces δ ≥ 5 (Lemma B): 0 graphs in both orders; e ≥ 52: impossible (Lemma B; also QB(5)); lower bound `data/witness_n19.g6` |
| 20 | **52 or 53** | e ≥ 55 impossible (Lemma B); e = 54 forces δ ≥ 5 and job C (10 + 10) gave 0; e = 53 not run (over budget, section 5); lower bound `data/witness_n20.g6` |

So QB(7) (e ≥ 3n − 7 forces a nonempty 4-regular subgraph) holds for 4 ≤ n ≤ 19, and QB(6) holds for 4 ≤ n ≤ 20.

Detached jobs (`code/jobs.tsv`):

| Job | Class | Shards done | Output graphs (no 4-regular subgraph) | user CPU s | Status | Re-check of output |
|---|---|---|---|---|---|---|
| n18_99_e47 | n=18 e=47=3n-7 sides 9+9 delta>=4 | 40/40 | 0 | 2,057 | COMPLETE | - |
| n19_910_e50 | n=19 e=50=3n-7 sides 9+10 delta>=4 | 200/200 | 0 | 24,486 | COMPLETE | - |
| n20_1010_e54_d5 | n=20 e=54=3n-6 sides 10+10 delta>=5 | 200/200 | 0 | 5,575 | COMPLETE | - |
<!-- COLLECT:END -->

Lower bounds: ex(n) ≥ 3n − 8 for n = 15 to 20 by the explicit graphs `data/witness_n<N>.g6`
(section 4.3), so no census at the 3n − 8 level was needed. Upper bounds: sections 2 and 3.

## 2. Facts used

| Fact | Statement | Status | Where |
|---|---|---|---|
| QB(4) | simple bipartite, Δ ≤ 6, n ≥ 2, e ≥ 3n − 4 ⇒ nonempty 4-regular subgraph | Lean, `check.sh` PASS (`Erdos585.qb4`) | `STATE.md` LEAN-QB4 |
| QB(5) | same with n ≥ 3 and e ≥ 3n − 5; so ex(n) ≤ 3n − 6 for every n ≥ 3 | paper, refereed: `wave4/qb5/PAPER4.md` Theorem 4.1; `REVIEW4.md` (FINAL) "QB(5) is proved": ACCEPT WITH FIXES, no mathematical error, no census input | `wave4/qb5/` |
| base | c(n') ≤ 3n' − 8 for every n' ≤ 16 (c = maximum with δ ≥ 4 added). No counted graph with δ ≥ 4 for n' ≤ 10; maxima 25, 26, 31, 33, 37 at n' = 11 to 15 (so 3n' − 8 is attained at 11, 13, 15); c(16) ≤ 39 | computed: census lane (geng_q4: every e for n' ≤ 13, e ≥ 30 at 14, e ≥ 33 at 15, e ≥ 40 at 16) and re-run here: `geng_q4 -b -d4 -D6 -u n (3n−7):(3n)` → 0 for n = 8..16 (`logs/base/`) | `census/CENSUS.md` Jobs 2-3, `census/f1/q4free_bip_n1{1,2,3,5}*.g6` |
| F1(17) | δ ≥ 4, e ≥ 45 at n = 17: none (`genbg_q4 -u -d4:4 -D6:6 9 8 45:48`, sides forced 8 + 9) | computed, one method | `census/CENSUS.md` Job 3 |
| F1(18) | δ ≥ 4, e ≥ 48 at n = 18: none (pieces 10 + 8 at e = 48, 9 + 9 at e = 48..54) | computed, one method | `census/CENSUS.md` Job 3, `STATE.md` F1-18 |

## 3. The argument

Call G *counted* if it is simple, bipartite, Δ(G) ≤ 6 and has no nonempty 4-regular subgraph. Every
subgraph of a counted graph is counted. Let c(n) be the maximum number of edges of a counted graph on
n vertices with δ ≥ 4.

**Lemma A (peeling).** For n ≥ 6, ex(n) ≤ max(3n − 9, max over 1 ≤ n' ≤ n of c(n') + 3(n − n')).
Proof: delete vertices of degree at most 3 one at a time until none is left; each deletion removes at
most 3 edges. If n' ≥ 1 vertices remain, they induce a counted graph with δ ≥ 4, so
e(G) ≤ c(n') + 3(n − n'). If none remain, list the vertices in reverse order of deletion: each has at
most 3 neighbors earlier in the list, and the first six induce a bipartite graph with at most 9 edges,
so e(G) ≤ 9 + 3(n − 6) = 3n − 9. ∎
So c(n') ≤ 3n' − 8 for all n' ≤ N gives ex(n) ≤ 3n − 8 for 6 ≤ n ≤ N (and ex(4) = 4, ex(5) = 6 directly).

**Lemma B (one deletion).** Every counted G on n ≥ 2 vertices has δ(G) ≥ e(G) − ex(n − 1), since G − v
for a vertex v of minimum degree is counted. If ex(n − 1) ≤ 3(n − 1) − 8 = 3n − 11, then:
- e ≥ 3n − 5 forces δ ≥ 6, so G is 6-regular; a regular bipartite graph is a union of perfect
  matchings (König), and four of them form a 4-regular subgraph: impossible. (QB(5) gives this too.)
- e = 3n − 6 forces δ ≥ 5.
- e = 3n − 7 forces δ ≥ 4.

So, given ex(n − 1) = 3n − 11 and a witness with 3n − 8 edges, ex(n) = 3n − 8 exactly when there is no
counted graph with δ ≥ 4 and e = 3n − 7 and none with δ ≥ 5 and e = 3n − 6.

**Side sizes.** In a counted graph each side S has e = Σ_S deg ≤ 6|S|, and e ≥ δ|S|. This holds for
every proper 2-coloring, so the census of a level needs only the side splits these inequalities
allow: n = 17, e = 44: 8 + 9. n = 18, e = 47: 8 + 10 and 9 + 9. n = 19, e = 50: 9 + 10. n = 19, e = 51,
δ ≥ 5: 9 + 10. n = 20, e = 53: 9 + 11 and 10 + 10. n = 20, e = 54, δ ≥ 5: 10 + 10 only (on 9 + 11 the
11-side would carry at least 11 · 5 = 55 > 54 edges).

**Generators.** `genbg_q4 [-X-2] -d a:b -D 6:6 n1 n2 e:e [r/mod] [file]` is nauty 2.8.9 genbg with a
PRUNE1 hook (`q4prune_bg.c`) that drops an intermediate graph (first class plus some second-class
vertices) when q4core.h finds a 4-regular subgraph through the newest vertex. Containing a 4-regular
subgraph is inherited by supergraphs and each intermediate graph is a subgraph of all its completions,
so the prune is sound; with symmetric degree flags, running one order (n1, n2) lists every bicoloured
graph with those class sizes. The res/mod shards of one command partition its output (controls: the
census lane's `-X` split sums 485 and 24,231; this lane's driver self-test in `code/selftest/`, 24,231
with r/4). Output graphs are counted graphs.

**Chain.**
1. n = 17: the base and the two runs at e = 44 give c(n') ≤ 3n' − 8 for n' ≤ 17 (with F1(17)), so
   ex(17) ≤ 43 by Lemma A; witness → **ex(17) = 43**.
2. n = 18: add e = 47 (8 + 10 done; 9 + 9 is job A) and F1(18): c(n') ≤ 3n' − 8 for n' ≤ 18, so ex(18) = 46.
3. n = 19: Lemma B with ex(18) = 46: e = 50 with δ ≥ 4 (job B), e = 51 with δ ≥ 5 (done, 0), e ≥ 52
   impossible. Both empty ⇒ ex(19) = 49.
4. n = 20: Lemma B with ex(19) = 49: e ≥ 55 impossible, e = 54 needs δ ≥ 5 (job C), e = 53 needs δ ≥ 4
   (not run, section 5). So ex(20) ∈ {52, 53} once C is empty.

The collector applies exactly these rules; any output graph in a job flips the affected rows to a
"!!!" line (a graph with 3n − 7 or 3n − 6 edges and no 4-regular subgraph), re-decided by pysat and
q4filter and given a glucose4 DRAT proof checked by `code/certify.py`.

## 4. Runs

### 4.1 Complete foreground runs (each under `timeout 240`, `nice -n 10`; logs in `logs/pilot/`)

| n, e | Command | Graphs | user s |
|---|---|---|---|
| 17, 44 | `genbg_q4 -d4:4 -D6:6 9 8 44:44` | 0 | 32.95 |
| 17, 44 | `genbg_q4 -d4:4 -D6:6 8 9 44:44` (other order) | 0 | 27.33 |
| 18, 47 (8 + 10) | `genbg_q4 -d4:4 -D6:6 8 10 47:47` | 0 | 114.49 |
| 18, 47 (8 + 10) | `genbg_q4 -d4:4 -D6:6 10 8 47:47` (other order) | 0 | 23.73 |
| 19, 51, δ ≥ 5 | `genbg_q4 -d5:5 -D6:6 10 9 51:51` | 0 | 186.27 |
| 19, 51, δ ≥ 5 | `genbg_q4 -d5:5 -D6:6 9 10 51:51` (other order) | 0 | 16.62 |
| n ≤ 16, e ≥ 3n − 7 | `geng_q4 -b -d4 -D6 -u n (3n−7):(3n)`, n = 8..16 (`logs/base/`) | 0 each | 16.36 at n = 16, < 1.1 otherwise |

### 4.2 Detached jobs (genbg_q4 SHA-256 `a29067ac…bd84404c`, same as the census lane)

| Job | Command | Shards | Pilot fit t = P + W/mod | Projected core-s |
|---|---|---|---|---|
| A | `genbg_q4 -X-2 -d4:4 -D6:6 9 9 47:47 r/40` | 40 | 0/200 8.3 s, 100/200 7.9 s, 7/20 65.8 s, 13/20 64.2 s: W ≈ 1,270, P ≈ 1.8 | 1,340 |
| B | `genbg_q4 -X-2 -d4:4 -D6:6 9 10 50:50 r/200` | 200 | 0/2000 15.0 s, 0/200 118.2 s, 100/200 115.6 s: W ≈ 22,700, P ≈ 3.7 | 23,400 |
| C | `genbg_q4 -X-2 -d5:5 -D6:6 10 10 54:54 r/200` | 200 | 0/2000 3.2 s, 0/200 29.4 s, 100/200 28.9 s (unsplit and 7/20 hit 240 s): W ≈ 5,770, P ≈ 0.3 | 5,800 |

Timing caveat: during the run the load average was 78 to 156 on 18 cores (other lanes and projects),
and job A's shards used about 1.5 times their pilot CPU, so the jobs may total about 46,000 core-s.

### 4.3 Witnesses (lower bounds), `code/witness.py`, `data/WITNESSES.txt`

Start: the first e = 37 graph of `census/f1/q4free_bip_n15_e33-45.g6` (n = 15, δ ≥ 4, graph6
`N????BoBvoXwn_^O]W?`); then five vertices of degree 3 each, so e = 3n − 8 at every step:
`data/witness_n15.g6` to `data/witness_n20.g6` (sides 7 + 8, 7 + 9, 8 + 9, 8 + 10, 9 + 10, 10 + 10;
Δ = 6). Each one is checked bipartite with Δ ≤ 6 and e = 3n − 8, and 4-regular-free three ways: pysat
CaDiCaL with validate_sat.py's encoding (UNSAT), q4filter (q4core.h, none), and glucose4 on the same
CNF (`data/witness_n<N>.cnf`) with a DRAT proof (`data/witness_n<N>.drat`) that the script's own RUP
checker verifies down to the empty clause (9 lemmas each; the checker rejects a bogus empty proof and a
bogus unit lemma, and a truncated proof). Independently of SAT, each added vertex has degree 3 when
added, so peeling them returns to the census graph.

## 5. Over budget: n = 20, e = 53

Not launched. Pilots (`logs/pilot/`): 10 + 10 with δ ≥ 4, `-X-2 ... 0/2000` did not finish in 240 s,
which projects to at least 2000 × 240 ≈ 480,000 core-s (133 core-h) if that shard is typical. 10 + 10 with the second class δ ≥ 5 (covers every
graph with a side of minimum degree ≥ 5, by swapping colors): 0/200 took 122.2 s, about 24,000 core-s.
9 + 11 (the 9-side then has degrees ≥ 5): unsplit did not finish in 90 s, and the one shard tried,
0/200 with `-X-2`, did not finish in 120 s in either class order, which projects to more than 24,000
core-s at that split. The open case is 10 + 10 or 9 + 11 at e = 53
with δ ≥ 4; in it, for every degree-4 vertex v, G − v is an extremal 19-vertex graph (Lemma B), which
might seed a smarter search. So the n = 20 answer stops at ex(20) ∈ {52, 53}.

## 6. Method status

All census pieces use the q4core.h decider inside nauty generators: one method in the sense of the
census lane. Second generation orders (same binary) exist for n = 17 at e = 44, n = 18 at 8 + 10, and
n = 19 at e = 51; 9 + 9 at n = 18 is symmetric. The base levels n ≤ 16 at e ≥ 3n − 6 have a second,
independent method (plain geng 2.9.3 + pysat, census lane), and so does n = 14 at e = 34, 35; the
3n − 7 level at n ≤ 13 and at n = 15, 16, and the n = 17 to 20 pieces here, have one. The witnesses have three
deciders and a checked proof. Independent second methods priced, not run: plain genbg 2.9.3 + pysat
on n = 17, e = 44 (14,087,019 graphs, about 1 to 1.5 core-h at about 4,000 graphs per second),
n = 18 at 8 + 10 (8,584,858) and n = 19 at e = 51, δ ≥ 5 (10,055,368).

## 7. Files

`code/run_excensus.sh` (driver), `code/jobs.tsv`, `code/queue.txt`, `code/collect.py` (collector),
`code/witness.py`, `code/certify.py` (DRAT certificates), `code/selftest/` (self-tests), `data/` (witnesses, CNFs, DRAT proofs,
collector output), `logs/` (shards, pilots, base re-run, `driver.log`), `JOBS.md`, `RESUME.md`, `LOG.md`.
