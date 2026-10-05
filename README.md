# Erdős Problem 585

> What is the maximum number of edges that a graph on n vertices can have if it does not contain
> two edge-disjoint cycles with the same vertex set?
>
> [erdosproblems.com/585](https://www.erdosproblems.com/585) (Erdős 1976)

Hi - I'm Robert Huynh, currently a second-year MBA student at Harvard Business School. While
absolutely not a mathematician, I'm a founder and always excited to tackle new problems like this,
especially if I can use AI. I've also been pretty inspired by the recent breakthroughs from the
large frontier labs and so I've spent these past few days attempting to see how far I can go
pointing a team of AI agents at this open problem. This repo holds what a team of agents plus me
steering has been able to do.

## Status

The problem is open. Call two edge-disjoint cycles with the same vertex set a pair, and write f(n)
for the maximum number of edges of a graph on n vertices with no pair. The known bounds are
f(n) ≥ c·n log log n (Pyber, Rödl and Szemerédi, 1995) and f(n) ≤ n (log n)^O(1) (Chakraborti,
Janzer, Methuku and Montgomery, 2024).

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

All are in `Openmath/Proofs/Final.lean` except the two graphs (`RegularFive.lean`, `BipartiteFive.lean`),
whose edge lists are in `graphs/`. `python3 scripts/check_axioms.py` checks every one at once.

The linear lower bounds come from explicit constructions. For large n they are far below the known
n log log n growth.

## Computations

Exact values f(1), …, f(10) = 0, 1, 3, 6, 9, 12, 16, 19, 23, 27, by exhaustive search. Programs
and results are in `computations/`, and `computations/COMMANDS.md` gives the commands, their outputs,
and the argument for the upper bounds.

## Census

The two 5-regular graphs above show that degree 5 does not force a pair; whether degree 6 does is
open as far as I know. The `census/` folder holds a computer search aimed at that case. Every graph
with maximum degree at most 6, minimum degree at least 4 and at least 3n − 4 edges was checked on 11
and 12 vertices, every bipartite one on 13 to 18 vertices, and every 6-regular graph on 13 and 14
vertices. This was done using nauty's `geng` to list graphs and the pair test in
`census/programs/pairc.c`. We looked at about 150 million of these graphs in all and every one of
them had a pair. If that holds for every n, every bipartite 6-regular graph has a pair. I'm keeping
the search as evidence of this, not a proof. The commands are in `census/programs/COMMANDS.md` and
the logs are in `census/logs/`.

## The formal statement

`Openmath/Target.lean` is the statement I proposed to
[google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures).
If it is merged, this repository will import the upstream statement instead.

## How this was made

I used the latest AI models and pointed AI agents (OpenAI's GPT-6 Astra and Anthropic's Claude
models, mainly Fable 5.1 and Opus 5.5) to research novel techniques and recent breakthroughs, and
see if we can apply them to Erdős 585. The AI agents would propose ideas, write proofs and search
programs, and even review each other's work. The Lean results were also checked by the Lean kernel,
and the exact values were cross-checked by separately written programs. As the AI agents made
passes, I made sure to steer them towards the big goal instead of tunneling into dead ends or
techniques that would cost way more than my budget allowed. I also made sure that we had plenty of
checkpoints and new avenues to attempt verified progress.

## AI use

The formal statement, Lean proofs, constructions and search programs in this repository were
produced with AI agents. I reviewed the results, the checks and the claims they support, and wrote
this README with AI help. No mathematician has reviewed the mathematics yet. I'm currently in the
process of contacting mathematicians to help me check them against the literature. If you find an
error or know of prior work, or are willing to help, please open an issue and I'd love to get in
contact with you.

## Build

Needs elan (Lean's installer), Python 3.10 or later for the computations, and a C compiler with
nauty 2.9.3 only for the census. After the Mathlib cache download, the build takes a few minutes.

```bash
lake exe cache get
lake build
./check.sh Openmath/Proofs/Final.lean Erdos585.maxEdges_seven
```

## License and citation

Apache-2.0 (see `LICENSE` and `NOTICE`). To cite this work, see `CITATION.cff`.
