/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import Openmath.Proofs.DoubleWheel
import Openmath.Proofs.Extension

/-!
# Erdős 585: the results in upstream vocabulary

The statements below use only `HasTwoEdgeDisjointCyclesSameVertexSet` and `maxEdges` from
`Openmath.Target`. Each follows from the `Finset`-form results in this directory through the
bridge in `Openmath.Proofs.Compat`:

* `maxEdges n = n.choose 2` for `n ≤ 4`, and `maxEdges 5 = 9`;
* `3 n - 6 ≤ maxEdges n` for `n ≥ 5`, `3 n - 5 ≤ maxEdges n` for `n ≥ 7`, and
  `3 n - 4 ≤ maxEdges n` for `n ≥ 9`;
* the double wheel `K₂ ∨ Cₘ` with `m ≥ 5` and `K₂ ∨ θ(2,3,3)` have no two edge-disjoint cycles
  with the same vertex set;
* `maxEdges n + 3 ≤ maxEdges (n + 1)` for `n ≥ 3`.
-/

open SimpleGraph Finset

namespace Erdos585

/-- For $n \leq 4$ the maximum is $\binom{n}{2}$, attained by the complete graph. -/
theorem maxEdges_eq_choose_two_of_le_four (n : ℕ) (hn : n ≤ 4) : maxEdges n = n.choose 2 :=
  maxEdges_eq_of_isGreatest (le_four n hn)

/-- For $n = 5$ the maximum is $9$, attained by $K_5$ minus an edge. -/
theorem maxEdges_five : maxEdges 5 = 9 :=
  maxEdges_eq_of_isGreatest five

/-- For $n \geq 5$ the maximum is at least $3n - 6$. -/
theorem three_mul_sub_six_le_maxEdges (n : ℕ) (hn : 5 ≤ n) : 3 * n - 6 ≤ maxEdges n :=
  le_maxEdges_of_mem (three_mul_sub_six_mem n hn)

/-- For $n \geq 7$ the maximum is at least $3n - 5$, by the double wheel. -/
theorem three_mul_sub_five_le_maxEdges (n : ℕ) (hn : 7 ≤ n) : 3 * n - 5 ≤ maxEdges n :=
  le_maxEdges_of_mem (three_mul_sub_five_mem_edgeCounts n hn)

/-- For $n \geq 9$ the maximum is at least $3n - 4$, by $K_2 \vee \theta(2,3,3)$ and extension. -/
theorem three_mul_sub_four_le_maxEdges (n : ℕ) (hn : 9 ≤ n) : 3 * n - 4 ≤ maxEdges n :=
  le_maxEdges_of_mem (three_mul_sub_four_mem n hn)

/-- The double wheel on a rim of length at least five has no two edge-disjoint cycles with the
same vertex set. -/
theorem doubleWheel_not_hasTwoEdgeDisjointCyclesSameVertexSet (k : ℕ) (hk : 2 ≤ k) :
    ¬ HasTwoEdgeDisjointCyclesSameVertexSet (doubleWheel (k + 3)) :=
  fun h => doubleWheel_not_hasPair k hk ((hasPairF_iff _).2 h)

/-- $K_2 \vee \theta(2,3,3)$ has no two edge-disjoint cycles with the same vertex set. -/
theorem thetaWheel_not_hasTwoEdgeDisjointCyclesSameVertexSet :
    ¬ HasTwoEdgeDisjointCyclesSameVertexSet thetaWheel :=
  fun h => theta_not_hasPair ((hasPairF_iff _).2 h)

/-- For $n \geq 3$, adding a vertex of degree three to a maximiser gives
$\mathrm{maxEdges}(n + 1) \geq \mathrm{maxEdges}(n) + 3$. -/
theorem maxEdges_succ_ge (n : ℕ) (hn : 3 ≤ n) : maxEdges n + 3 ≤ maxEdges (n + 1) :=
  le_maxEdges_of_mem (mem_edgeCounts_succ hn (maxEdges_mem_edgeCounts n))

end Erdos585
