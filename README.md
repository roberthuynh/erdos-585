# Erdős Problem 585 in Lean 4

What is the maximum number of edges that a graph on $n$ vertices can have if it does not contain
two edge-disjoint cycles with the same vertex set? ([erdosproblems.com/585](https://www.erdosproblems.com/585);
Erdős 1976, Problem 29.)

- `pr/585.lean`, identical to `openmath/Openmath/Target.lean`: the statement as proposed to
  google-deepmind/formal-conjectures.
- `openmath/Openmath/Proofs/`: kernel-checked results about it. `Final.lean` states them in terms
  of the statement file's `maxEdges`.
- `triage/`: the programs and outputs behind the exact values.

Kernel-checked, with axioms `propext`, `Classical.choice` and `Quot.sound` only:

- `maxEdges n = n.choose 2` for `n ≤ 4`, and `maxEdges 5 = 9`.
- `maxEdges n + 3 ≤ maxEdges (n + 1)` for `n ≥ 3`: a vertex of degree 3 lies on no such pair.
- `3 * n - 5 ≤ maxEdges n` for `n ≥ 7`: the double wheel K2 ∨ C(n−2), two adjacent hubs joined to
  every vertex of a cycle, has no such pair.
- `3 * n - 4 ≤ maxEdges n` for `n ≥ 9`: K2 ∨ θ(2,3,3), where θ(2,3,3) is two vertices joined by
  paths of lengths 2, 3 and 3, has no such pair on 9 vertices, and the previous item extends it.

Exact values for n = 1 to 10: 0, 1, 3, 6, 9, 12, 16, 19, 23, 27. Each was found by exhaustive
search (`triage/erdos585_small.py`) and cross-checked by a second method: a pass over all graphs
for n ≤ 6, an independently written checker for n = 7 and 8 (`triage/erdos585_verify.py`), and a
reduction from the extremal graphs on n − 1 vertices for n = 9 and 10 (`triage/erdos585_n9.py`).
The double wheel is extremal for n = 7 and 8, but not for n = 9.

Known asymptotics, stated but not proved here: maxEdges n ≫ n log log n (Pyber, Rödl and
Szemerédi 1995) and maxEdges n ≤ n (log n)^O(1) (Chakraborti, Janzer, Methuku and Montgomery
2024). The true order of growth is open.

Build, with Lean v4.33.1:

    cd openmath && lake exe cache get && lake build Openmath Openmath.Proofs.Final

Check one theorem (build, no `sorry`, axioms) from the repo root:

    ./check.sh Openmath/Proofs/Final.lean Erdos585.maxEdges_five

The Lean and the search programs were written with Claude (Anthropic). Every theorem here is
checked by Lean's kernel, and every value by two methods.
