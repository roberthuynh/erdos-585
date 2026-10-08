# Erdős Problem 585

> What is the maximum number of edges that a graph on n vertices can have if it does not contain
> two edge-disjoint cycles with the same vertex set?
>
> [erdosproblems.com/585](https://www.erdosproblems.com/585) (Erdős 1976)

Hi, I'm Robert Huynh, currently a second-year MBA student at Harvard Business School. While
absolutely not a mathematician, I'm a founder and always excited to tackle new problems like this,
especially if I can use AI. I've also been pretty inspired by the recent breakthroughs from the
large frontier labs and so I've spent these past few days attempting to see how far I can go
pointing a team of AI agents at this open problem. This repo holds what a team of agents plus me
steering has been able to do.

## Status

The problem is still open, as far as I know (October 2026). The known bounds on f(n), the maximum
number of edges of a graph on n vertices with no two edge-disjoint cycles on the same vertex set,
are f(n) ≥ c·n log log n (Pyber, Rödl and Szemerédi, 1995) and f(n) ≤ n (log n)^O(1) (Chakraborti,
Janzer, Methuku and Montgomery, Adv. Math. 2025; arXiv 2024). Below, two such cycles are called a
pair. Nothing in this repository changes either of those bounds.

This repo has 3 kinds of results: (1) results verified in Lean, (2) computer searches you can rerun,
and (3) written proofs that AI agents wrote and reviewed but no human has checked yet.

## Verified in Lean

Each result below compiles with no `sorry` and uses only the standard axioms (`propext`,
`Classical.choice`, `Quot.sound`). Reproduce one with `./check.sh <file> <declaration>`.

| Result | Lean declaration |
|---|---|
| f(n) = n(n−1)/2 for n ≤ 4; f(5) = 9; f(6) = 12; f(7) = 16 | `Erdos585.maxEdges_eq_choose_two_of_le_four`, `Erdos585.maxEdges_five`, `Erdos585.maxEdges_six`, `Erdos585.maxEdges_seven` |
| f(n) ≥ 3n − 5 for n ≥ 7 (double wheel); f(n) ≥ 3n − 4 for n ≥ 9 | `Erdos585.three_mul_sub_five_le_maxEdges`, `Erdos585.three_mul_sub_four_le_maxEdges` |
| f(n+1) ≥ f(n) + 3 for n ≥ 3 | `Erdos585.maxEdges_succ_ge` |
| f(n) ≥ 4n − 13 for n ≥ 10; f(n) ≥ 5n − 15⌊√n⌋ − 10 for n ≥ 16 | `Erdos585.four_mul_sub_thirteen_le_maxEdges`, `Erdos585.five_mul_sub_sqrt_le_maxEdges` |
| f(11) ≥ 31, f(12) ≥ 36 | `Erdos585.thirty_one_le_maxEdges_eleven`, `Erdos585.thirty_six_le_maxEdges_twelve` |
| A 5-regular graph on 32 vertices with no such pair | `Erdos585.RegularFive.exists_five_regular_pairfree` |
| A bipartite 5-regular graph on 104 vertices with no such pair | `Erdos585.BipartiteFive.exists_bipartite_five_regular_pairfree` |
| A 5-regular graph on 18 vertices with no such pair | `Erdos585.RegularFive18.exists_five_regular_pairfree` |
| Every bipartite graph with maximum degree at most 6, n ≥ 3 vertices and at least 3n − 5 edges has a nonempty 4-regular subgraph | `Erdos585.qb5` |
| Every bipartite graph with maximum degree at most 6, n ≥ 2 vertices and at least 3n − 4 edges has a nonempty 4-regular subgraph (implied by the row above; it was proved first, and the proof of `qb5` builds on it) | `Erdos585.qb4` |
| For any bipartite 6-regular graph and any vertex v, the graph minus v still has a nonempty 4-regular subgraph (it has n − 1 vertices and 3(n − 1) − 3 edges, so this follows from the rows above) | `Erdos585.exists_four_regular_avoiding_of_bipartite_six_regular` |

All are in `Openmath/Proofs/Final.lean` except the three graphs
(`Openmath/Proofs/RegularFive18.lean`, `Openmath/Proofs/RegularFive.lean`,
`Openmath/Proofs/BipartiteFive.lean`, with edge lists in `graphs/` and a checker,
`graphs/verify_graphs.py`) and the three 4-regular subgraph results
(`Openmath/Proofs/QB4/Statement.lean`, `Openmath/Proofs/QB5/Statement.lean`).
`python3 scripts/check_axioms.py` checks the axioms and the recorded statement of every one at once,
along with eight supporting declarations: 25 in all, listed in `scripts/headline-theorems.json`.

The 4-regular subgraph results are about 4-regular subgraphs, not pairs. Every pair is a 4-regular
subgraph (the union of its two cycles), but a 4-regular subgraph need not contain a pair, so these
results do not settle whether 6-regular graphs have a pair. For comparison, Remark 3.6 of Alon,
Friedland and Kalai (J. Combin. Theory Ser. B 37, 1984) gives a nonempty 4-regular subgraph in every
bipartite graph with maximum degree at most 7 and at least 3n − 2 edges. The agents did not find the
3n − 4 or 3n − 5 bounds in the literature they searched (October 2026). I do not claim they are new:
nothing here is claimed as new until an expert has compared it with the literature. For small
bipartite graphs with maximum degree at most 6 the truth is lower still: an unreviewed computer
search by two programs finds that 3n − 7 edges are enough for 4 ≤ n ≤ 19, and
`findings/supplement/census/edge/` has examples with 3n − 8 edges and no 4-regular subgraph.

QB(4) and QB(5) are this project's labels (the 4 and 5 are the slack in 3n − 4 and 3n − 5, not a
degree), and in the files under `QB4/` and `QB5/` a "pair" means a pair of vertex sets, not a pair
of cycles.

The linear lower bounds come from explicit constructions. For large n they are far below the known
lower bound of order n log log n.

## Computations

Exact values f(1), …, f(10) = 0, 1, 3, 6, 9, 12, 16, 19, 23, 27 were reported by
[Erdős Problem a Day](https://erdosproblemaday.com/report/585) on July 28, 2026
(read October 8, 2026). This repository reproduces those values. Programs and results are in
`computations/`; `computations/COMMANDS.md` gives the commands, outputs and upper-bound case checks.
The new computational entries beyond that report are f(11) = 31 and f(12) = 36;
the programs and logs are in `findings/supplement/small-values/`. The [saved upper certificates](findings/supplement/small-values/certificates/README.md)
now let a separate checker verify every positive rejection and every admissible extension.
The upper exclusions remain computational and share nauty's canonical generation;
separate certificate checking is not an independent graph census.

## Census

The three 5-regular graphs above show that being 5-regular does not force a pair, and the 18-vertex
one has the least order according to the reported complete census: no 5-regular graph on 16 or
fewer vertices is pair-free (through 14 by two separately written programs; at 16 by one complete
pruned search, with a second program on part of it). The tag includes the 20,000 completed shard
indices and aggregate records, but omits the raw per-shard logs and empty outputs. The complete
16-vertex exclusion has not had a complete independent replication. Its evidence is computational;
the 18-vertex witness itself is Lean verified. See `findings/supplement/census/`. Minimum degree alone never forces a pair: the Pyber, Rödl and
Szemerédi construction has no 3-regular subgraph and has order n log log n edges. It is pair-free:
a pair would give a 4-regular graph, and every 4-regular simple graph contains a 3-regular subgraph
(Read and Wilson, *An Atlas of Graphs*, Chapter 5, Theorem 11). Its growing average degree also
gives subgraphs of arbitrarily large minimum degree by repeatedly deleting vertices below half
the original average degree. I know of no result either way on whether every 6-regular graph has a pair.
The `census/` folder holds a computer search aimed at that case. Every graph with maximum degree at
most 6, minimum degree at least 4 and at least 3n − 4 edges was checked on 11 and 12 vertices, every
bipartite one on 13 to 18 vertices, and every 6-regular graph on 13 and 14 vertices. This was done
using nauty's `geng` to list graphs and the pair test in `census/programs/pairc.c`. We looked at
about 150 million of these graphs in all and every one of them had a pair. Every 6-regular graph is
in this class (it has 3n edges), so if that holds for every n, every 6-regular graph has a pair. I'm
keeping the search as evidence of this, not a proof, and it is weak evidence: the smallest pair-free
5-regular graph has 18 vertices and the smallest bipartite one I know of has 104, while the
6-regular search stops at 14 vertices and the bipartite search at 18. The commands are in
`census/programs/COMMANDS.md` and the logs are in `census/logs/`.

## Written proofs (AI-written and AI-reviewed)

I am looking for help with these. The written proofs are in `findings/`: AI agents wrote them and
other AI agents reviewed them, and no mathematician has checked them. If you work in extremal graph
theory and are willing to look at one, please open an issue.

`findings/FINDINGS.md` lists every result in this repo with its evidence (Lean, computation, or
written proof), the files behind it, and the checks I most need an expert's help with (section 6).
The main written candidates:

- Every bipartite 6-regular graph on at most 24 vertices has a pair. This rests on three written
  proofs and four computer searches, three of them done by two separately written programs.
- Every graph with maximum degree at most 6, n ≥ 2 vertices and at least 3n − 2 edges has a nonempty
  4-regular subgraph (from the Lean result above and Tutte's f-factor theorem).
- "Every bipartite 6-regular graph has a pair" is equivalent to its vertex-deleted form: every
  bipartite 6-regular graph minus any one vertex has a pair.
- If every bipartite 6-regular graph has a pair, then f(n) is of order n log log n (an immediate
  consequence of Pyber, Rödl and Szemerédi, 1995, and Janzer and Sudakov, Forum Math. Pi 2023).
- If every bipartite regular graph on N vertices with degree at least a constant times (log N)^3 has
  a pair, then f(n) = O(n (log n)^4), directly from Theorem 1.5 of Chakraborti, Janzer, Methuku and
  Montgomery, "Regular subgraphs at every density" (Trans. Amer. Math. Soc. 2026).

How they were reviewed: each written proof was reviewed by at least one separate AI agent in a fresh
context, and the reviewer reran any computation with its own code. The reviewer was often the same
model as the author, so some proofs got a second or third reviewer, including one on a different
Claude model (Fable 5.1 reviewing work by Opus 5.5). Section 7 of the findings lists the models
behind each part of the work, including the reviews. AI review is a filter, and AI reviewers can
miss errors, so none of this is verified yet. That's why I'm seeking help. The supplement
(`findings/supplement/`) keeps the proofs and reviews as they were written, with every later edit
recorded.

## The formal statement

`Openmath/Target.lean` is the statement I proposed to
[google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures). It
defines `maxEdges` and the pair predicate used above. No human Lean expert has reviewed it yet. If
it is merged, this repository will import the upstream statement instead.

## How this was made

I pointed AI agents (OpenAI's GPT-6 Astra and Anthropic's Claude Fable 5.1 and Claude Opus 5.5) at
the recent literature to find techniques that might apply to Erdős 585. The agents proposed ideas,
wrote proofs and search programs, and reviewed each other's work. The Lean results were also checked
by the Lean kernel, and the exact values were cross-checked by separately written programs. Between
passes I steered them back toward the main question when they tunneled into dead ends or into
methods that would cost more than my budget allowed, and I made sure we had checkpoints and new
directions to try.

Most of my steering was setting the rules for what counts as progress and pushing the agents toward
novel approaches. First, I set the rules for what actually counted. A Lean result counted only when
`check.sh` passed: the build has no `sorry` and uses only the 3 standard axioms. For QB(5), a
separate agent also compared the Lean statement with the written one, and separate reviewers checked
every row of the "Verified in Lean" table against its Lean statement. In the later passes, every
main written claim needed either a Lean proof or a review by a separate agent in a fresh context,
and results for fixed sizes were recorded as fixed-size results, never as the general case. For the
key computer searches I asked for a second, separately written program, and the findings say which
searches have one. In the last pass, long computations ran as a small pilot first, with a budget cap
and a stop command. I tracked what each pass cost (section 8 of the findings has the figures),
parked directions that were not paying off, and had the agents keep a dated log of my decisions.

Second, I kept pushing the agents to look at the math literature and at other AI-assisted math
research for related results and methods they could apply here, instead of starting from scratch.
For example, the conditional route in the findings goes through a recent theorem of Chakraborti,
Janzer, Methuku and Montgomery on regular subgraphs.

## AI use

The formal statements, Lean proofs, written proofs, constructions and search programs in this
repository were produced with AI agents; section 7 of `findings/FINDINGS.md` says which model did
what. I read the results, the checks and the claims they support.

I'm an MBA candidate at Harvard Business School, not in a mathematics program, and I did not check
the mathematics myself. I take full responsibility for any errors. No mathematician has reviewed the
mathematics yet, although I am looking for help: if you find an error or know of prior work, or are
willing to help, please open an issue and I'd love to get in contact with you.

The [literature comparisons](literature/README.md) identify earlier mathematics behind
the existing results and credit Alejandro Zarzuelo Urdiales's dated public literature and proof-coverage review.

## Build

Needs elan (Lean's installer), Python 3.10 or later for the checks and the computations, and a C
compiler with nauty 2.9.3 only for the census. After the Mathlib cache download, the build takes a
few minutes.

```bash
lake exe cache get
lake build
./check.sh Openmath/Proofs/Final.lean Erdos585.maxEdges_seven
python3 scripts/check_axioms.py
```

## License and citation

Apache-2.0 (see `LICENSE` and `NOTICE`). To cite this work, see `CITATION.cff`.
