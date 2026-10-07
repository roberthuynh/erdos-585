# N.md: what N the rigid-set exclusion plus a census gives for B6

wave4/theory, 2026-10-05. Answers Robert's question. One page; details in `NOTES.md` §3-§7.

## The chain

1. Let B be a simple bipartite 6-regular graph on N vertices with no pair (N even). For any vertex o,
   B − o is bipartite, Δ ≤ 6, n = N − 1, e = 3N − 6 = 3n − 3 ≥ 3n − 4, and pair-free: a W1b
   counterexample on N − 1 vertices.
2. Take a W1b counterexample X with n minimal, then e minimal; n ≤ N − 1. By PAPER Lemma 1, X is
   sparse (g(S) ≥ 10 for 2 ≤ |S| ≤ n − 1), δ ≥ 4, e = 3n − 4, and X is E4 (n even) or C1 (n odd).
3. So B6 holds on N vertices once there is no such X of E4 type with n ≤ N − 2 and none of C1 type
   with n ≤ N − 1.

## The best N

| Case | W1b proved for | B6 for | What it rests on |
|---|---|---|---|
| (1) today, unconditional | n ≤ 18 | N ≤ 20 | W1b census (two methods) gives N ≤ 18; a direct B6 census gives N = 20 (below) |
| (2a) + 2EC' + H22 | E4 types n ≤ 22; C1 types still open | N ≤ 20 (direct census) | C1 type blocks any gain (n = 19, 21 are C1 only) |
| (2b) + 2EC' + H22 + C1(9) census | n ≤ 20 | N ≤ 20 | no gain over the direct census; C1(9): ~150M graphs, ~17 core-h generation plus port tests |
| (2c) + 2EC' + its C1 analog + H22 | n ≤ 23 (C1 at n = 21, 23 uses H20, H22 on X − y) | N ≤ 24 | gap item 4 (not done) |
| (2d) as (2c) with H_M | n ≤ M + 1 | N ≤ M + 2 | H24 ≈ 3×10^8 graphs, est. 50-100 core-h; H26 another ~70×, out of reach |
| (3) cap of the route | E4 types n ≤ 34 | N ≤ 36 at best | n < 36 is where the rigid-set exclusion stops |

Notes. (2a): n = 19 and 21 are odd, so only C1 instances live there; without the C1 case the E4
result does not move N. (2c): for C1 type the 4-factor lives on X − y (n − 1 vertices), so H22 covers
C1 up to n = 23. (3): the exclusion uses PAPER Prop 5 with census L5: a set with g = 10 and ≥ 3
vertices has a pair-free level −5 core on ≥ 18 vertices, and every rigid certificate in a sparse E4
instance needs two complementary g = 10 sets (NOTES §7), so n ≥ 36. Each extra 2 vertices of L5 raise
the cap by 4 (L5 at 18-19 vertices: est. 10^8-10^9 graphs, not measured). In practice the H census
binds long before 34; beyond n ≈ 24 the route needs an HD theorem (gap item 3), not a census.
Direct B6 census, run 2026-10-05 16:30: `genbg -q -d6:6 -D6:6 10 10 60:60` gives 121,790 graphs and
`pairc f` finds a pair in every one (4 parts, 0 pair-free, about 4 core-min; files
`b6_20_part_*.err`), so B6 holds at N = 20 (one method). At N = 22 a 1/400 slice of
`genbg -u -d6:6 -D6:6 11 11 66:66` did not finish in 280 s, so that census costs at least ~30 core-h
of generation (likely far more), plus the pair tests.

## Dependencies and status

| Item | Status |
|---|---|
| PAPER Lemma 1 (smallest W1b counterexample is sparse E4 or C1, δ ≥ 4) | reviewed, ACCEPT (wave3/pairs/REVIEW.md) |
| PAPER Lemma 2 (sparse E4 has a 4-factor), Prop 3 ((5,1) sets) | reviewed, ACCEPT |
| PAPER Prop 5 (g = 10, \|S\| ≥ 3 ⇒ core ≥ 18) and Cor 6 (n ≥ 36) | reviewed, ACCEPT WITH FIX (\|S\| ≥ 3) |
| Census L5 (no pair-free level −5 bipartite, δ ≥ 4, n ≤ 17) | census, one method (genbg + pairc); referee spot-check to 13 vertices with own code |
| W1b n ≤ 18 | census, two methods: F2 (geng -b + pairc, 585-fable) and the pairs-lane E4 a ≤ 9 / C1 s ≤ 8 censuses (genbg + ptool; referee re-ran a ≤ 7) |
| H22 (bipartite 4-regular, no 2-edge cut, n ≤ 22 ⇒ HD) | census: one method at n = 22, two methods for n ≤ 20 (referee) |
| C1-PAPER Lemma 4.4 (bad ports carry ≤ 2 units) | reviewed, two referees ACCEPT |
| LP rigidity criterion, classification of s ≤ 1 sets, no rigid set for n < 36 (NOTES §3-§7) | unreviewed paper; criterion code-checked on 386,304 sets, classification on all 52,557 sparse E4 with n ≤ 16 |
| 2EC' | OPEN. No counterexample in ~800 sparse instances (random, block, necklace); a repair rule (atom plus shortest Lemma 7 cycle) lowered the number of bad sets at every step in all 362 necklace instances |
| C1 analog (gap item 4) | not done |

## What the C1 type needs

At a good port y (exists by C1-PAPER Lemma 4.4), Y = X − y is balanced with deficiency 5 or 6 per
side and g ≥ 10 for every S with 2 ≤ |S| ≤ |Y| (including Y itself). Needed: (i) the classification
of s ≤ 1 sets for deficiency 5 or 6 (balanced forced sets become possible); (ii) a rigid-set
exclusion; (iii) 2EC' for Y, where a component without a 2-edge cut suffices; then H_{n−1}.

## S6 (va6 lane)

S6 at a port y asks for a Hamilton-decomposable 4-factor of Γ − y, which is balanced with deficiency 5
per side and g = 10 on the whole vertex set. My tools apply directly:
- `tools.py rigid_sets` lists every rigid set of Γ − y exactly (the LP criterion holds for any
  bipartite graph with a 4-factor). One rigid set refutes S6 at y, so it is a cheap filter.
- Sparsity of Γ gives more than sparsity of Γ − y: adding y back, g_Γ(S + y) = g(S) + 6 − 2D(S_Q),
  so g(S) ≥ 4 + 2D(S_Q) in Γ − y (the Q-deficiency of Γ − y sits on N(y)). Then s(S) ≥ 2 − j(S), so
  no balanced set has s ≤ 1: no thin set and no "(5,0)" set (which would disconnect every 4-factor)
  at any port, for every n. A full rigid-set exclusion for Γ − y by the NOTES §3-§4 method looks
  within reach without any census; not yet done.
- The rest of S6 is 2EC' for these instances plus an HD statement.
