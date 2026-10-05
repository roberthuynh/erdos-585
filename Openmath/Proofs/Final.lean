/-
Copyright 2026 Robert Huynh.

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
import Openmath.Proofs.SmallExact
import Openmath.Proofs.MatchingSubdivision
import Openmath.Proofs.TwoHubFamily
import Openmath.Proofs.LatinIncidence
import Openmath.Proofs.AdjacentHubs

/-!
# Erdős 585: the results in upstream vocabulary

The statements below are about `HasTwoEdgeDisjointCyclesSameVertexSet` and `maxEdges` from
`Openmath.Target`; three also name a local construction. Each follows from the `Finset`-form
results in this directory through the bridge in `Openmath.Proofs.Compat`:

* `maxEdges n = n.choose 2` for `n ≤ 4`, and exact values `9, 12, 16` at `n = 5, 6, 7`;
* `3 n - 6 ≤ maxEdges n` for `n ≥ 5`, `3 n - 5 ≤ maxEdges n` for `n ≥ 7`, and
  `3 n - 4 ≤ maxEdges n` for `n ≥ 9`;
* the double wheel `K₂ ∨ Cₘ` with `m ≥ 5` and `K₂ ∨ θ(2,3,3)` have no two edge-disjoint cycles
  with the same vertex set;
* `maxEdges n + 3 ≤ maxEdges (n + 1)` for `n ≥ 3`.
* `4 n - 13 ≤ maxEdges n` for `n ≥ 10`, including `31 ≤ maxEdges 11`;
* `36 ≤ maxEdges 12`, using the join of two adjacent hubs and the Petersen graph;
* `5 m² ≤ maxEdges (m² + 3m + 2)` from Latin-square incidence graphs, and
  `5 n - 15 floor(sqrt n) - 10 ≤ maxEdges n` for `n ≥ 16`;
* a matching-subdivision construction; complete bases on `2k` vertices yield
  `8k² - 3k + 1 ≤ maxEdges (2k² + 2)`.
-/

open SimpleGraph Finset

namespace Erdos585

/-- For $n \leq 4$ the maximum is $\binom{n}{2}$, attained by the complete graph. -/
theorem maxEdges_eq_choose_two_of_le_four (n : ℕ) (hn : n ≤ 4) : maxEdges n = n.choose 2 :=
  maxEdges_eq_of_isGreatest (le_four n hn)

/-- For $n = 5$ the maximum is $9$, attained by $K_5$ minus an edge. -/
theorem maxEdges_five : maxEdges 5 = 9 :=
  maxEdges_eq_of_isGreatest five

/-- For six vertices the maximum is twelve. -/
theorem maxEdges_six : maxEdges 6 = 12 :=
  maxEdges_eq_of_isGreatest six

/-- For seven vertices the maximum is sixteen, attained by the double wheel. -/
theorem maxEdges_seven : maxEdges 7 = 16 :=
  maxEdges_eq_of_isGreatest seven

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

/-- Subdivide the edges outside a matching, retain the matching, and join two adjacent hubs. -/
theorem matchingSubdivision_not_hasTwoEdgeDisjointCyclesSameVertexSet
    {V : Type*} [Fintype V] [DecidableEq V] (H M : SimpleGraph V)
    [DecidableRel H.Adj] [DecidableRel M.Adj] (hM : ∀ v, M.degree v ≤ 1) :
    ¬ HasTwoEdgeDisjointCyclesSameVertexSet (MatchingSubdivision.ofBase H M) :=
  fun h => MatchingSubdivision.ofBase_not_hasPair M H hM ((hasPairF_iff _).2 h)

/-- Complete even bases with perfect matchings give an explicit family approaching four edges
per vertex. This is a linear lower bound, below the known superlinear asymptotic bound. -/
theorem complete_matching_subdivision_lower_bound (k : ℕ) :
    8 * k ^ 2 - 3 * k + 1 ≤ maxEdges (2 * k ^ 2 + 2) :=
  MatchingSubdivision.complete_even_lower_bound k

/-- A uniform explicit linear lower bound from a sparse strip and two independent hubs. -/
theorem four_mul_sub_thirteen_le_maxEdges (n : ℕ) (hn : 10 ≤ n) :
    4 * n - 13 ≤ maxEdges n :=
  TwoHubFamily.four_mul_sub_thirteen_le n hn

/-- The eleven-vertex lower bound. -/
theorem thirty_one_le_maxEdges_eleven : 31 ≤ maxEdges 11 :=
  TwoHub.thirty_one_le

/-- A lower bound on twelve vertices. -/
theorem thirty_six_le_maxEdges_twelve : 36 ≤ maxEdges 12 :=
  AdjacentHubs.thirty_six_le

/-- Latin-square incidence graphs with two hubs give a family approaching five edges per vertex. -/
theorem latin_incidence_lower_bound (m : ℕ) : 5 * m ^ 2 ≤ maxEdges (m ^ 2 + 3 * m + 2) :=
  LatinIncidence.five_mul_sq_le m

/-- A uniform explicit lower bound approaching five edges per vertex. -/
theorem five_mul_sub_sqrt_le_maxEdges (n : ℕ) (hn : 16 ≤ n) :
    5 * n - 15 * Nat.sqrt n - 10 ≤ maxEdges n :=
  LatinIncidence.five_mul_sub_sqrt_le n hn

end Erdos585
