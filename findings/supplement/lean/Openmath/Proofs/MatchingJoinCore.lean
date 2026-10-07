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
import Openmath.Proofs.MatchingJoinPaths
import Openmath.Proofs.MatchingJoinSelection
import Openmath.Proofs.MatchingJoinDegree
import Openmath.Proofs.MatchingJoinCycles

/-! # Every arbitrary matching join of the checked quintic seed contains a faithful pair -/

open SimpleGraph Finset
namespace Erdos585.MatchingJoin

/-- The unrestricted bijection is handled by the proved terminal selection. -/
theorem graph_hasPair (f : Equiv.Perm (Fin 32)) : HasPairF (graph f) := by
  obtain ⟨z⟩ := selection_nonempty f
  have hp : TwoPaths RegularFive.graph (embed false z.x0) (embed true z.x1)
      (embed false z.y0) (embed true z.y1) := by
    simpa using whole_twoPaths false z.x0 z.y0 z.x1 z.y1 z.h0 z.h1
  have hq : TwoPaths RegularFive.graph (f (embed false z.x0)) (f (embed true z.x1))
      (f (embed false z.y0)) (f (embed true z.y1)) := by
    rw [z.fx0,z.fx1,z.fy0,z.fy1]
    exact whole_twoPaths z.s z.a0 z.b0 z.a1 z.b1 z.k0 z.k1
  apply hasPair_of_twoPaths f
    (by simpa using embed_ne_other false z.x0 z.x1)
    (by simpa using embed_ne_other false z.y0 z.y1)
    (fun h => z.h0.1 (embed_injective false h))
    (by simpa using embed_ne_other false z.x0 z.y1)
    (fun h => (embed_ne_other false z.y0 z.x1) h.symm)
    (fun h => z.h1.1 (embed_injective true h)) hp hq

/-- Actual order, regular degree, edge count, and the original faithful predicate. -/
theorem every_matching_join (f : Equiv.Perm (Fin 32)) :
    Fintype.card (Fin 32 × Bool) = 64 ∧
      (graph f).IsRegularOfDegree 6 ∧ (graph f).edgeFinset.card = 192 ∧
      HasTwoEdgeDisjointCyclesSameVertexSet (graph f) := by
  exact ⟨vertex_count,graph_regular f,graph_edge_count f,(hasPairF_iff _).mp (graph_hasPair f)⟩

/-- The actual avoiding quintic seed admits no avoiding arbitrary matching join. -/
theorem matching_join_raising_counterexample :
    RegularFive.graph.IsRegularOfDegree 5 ∧
      ¬ HasTwoEdgeDisjointCyclesSameVertexSet RegularFive.graph ∧
      ∀ f : Equiv.Perm (Fin 32),
        Fintype.card (Fin 32 × Bool) = 64 ∧
          (graph f).IsRegularOfDegree 6 ∧ (graph f).edgeFinset.card = 192 ∧
          HasTwoEdgeDisjointCyclesSameVertexSet (graph f) := by
  exact ⟨RegularFive.graph_degree,(hasPairF_iff _).not.mp RegularFive.graph_not_hasPair,
    every_matching_join⟩

end Erdos585.MatchingJoin
