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
import Mathlib.Combinatorics.SimpleGraph.Matching
import Openmath.Proofs.SmallExact

/-!
# Actual faithful pairs from two connected cycle factors

The hypotheses specify actual graphs, nonempty neighborhoods, and reachability.
Actual cycle walks are extracted from `IsCycles`; no walk or support equality is
assumed. The two factors need not exhaust the host's edges.
-/

namespace Erdos585.CycleFactors

open SimpleGraph

variable {V : Type*}

/-- A nontrivial connected cycle factor gives an actual spanning cycle walk. -/
theorem cycle_of_reachable_of_isCycles [Finite V]
    (H : SimpleGraph V) (x : V) (hcyc : H.IsCycles)
    (hn : (H.neighborSet x).Nonempty) (hall : ∀ v, H.Reachable x v) :
    ∃ p : H.Walk x x, p.IsCycle ∧ ∀ v, v ∈ p.support := by
  classical
  let c := H.connectedComponentMk x
  have hc : ∀ v, v ∈ c.supp := by
    intro v
    exact ConnectedComponent.sound (hall v).symm
  obtain ⟨p, hp, hs⟩ :=
    hcyc.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp (hc x) hn
  refine ⟨p, hp, ?_⟩
  intro v
  apply p.mem_verts_toSubgraph.mp
  rw [hs]
  exact hc v

/-- Two edge-disjoint connected cycle factors of one host give a faithful pair. -/
theorem hasPair_of_connected_factors [Finite V] [DecidableEq V]
    (G R B : SimpleGraph V) (x : V)
    (hcycR : R.IsCycles) (hcycB : B.IsCycles)
    (hnR : (R.neighborSet x).Nonempty) (hnB : (B.neighborSet x).Nonempty)
    (hallR : ∀ v, R.Reachable x v) (hallB : ∀ v, B.Reachable x v)
    (hleR : R ≤ G) (hleB : B ≤ G)
    (hdis : Disjoint R.edgeSet B.edgeSet) : HasPairF G := by
  classical
  obtain ⟨p, hp, hps⟩ := cycle_of_reachable_of_isCycles R x hcycR hnR hallR
  obtain ⟨q, hq, hqs⟩ := cycle_of_reachable_of_isCycles B x hcycB hnB hallB
  refine ⟨x, x, p.mapLe hleR, q.mapLe hleB,
    hp.mapLe hleR, hq.mapLe hleB, ?_, ?_⟩
  · ext v
    simp [hps v, hqs v]
  · rw [Walk.edges_mapLe_eq_edges, Walk.edges_mapLe_eq_edges]
    apply Finset.disjoint_left.mpr
    intro e he hf
    exact Set.disjoint_left.mp hdis
      (p.edges_subset_edgeSet (List.mem_toFinset.mp he))
      (q.edges_subset_edgeSet (List.mem_toFinset.mp hf))

/-- The same actual-factor hypotheses imply the original problem predicate. -/
theorem hasTwoEdgeDisjointCyclesSameVertexSet_of_connected_factors
    [Finite V] [DecidableEq V]
    (G R B : SimpleGraph V) (x : V)
    (hcycR : R.IsCycles) (hcycB : B.IsCycles)
    (hnR : (R.neighborSet x).Nonempty) (hnB : (B.neighborSet x).Nonempty)
    (hallR : ∀ v, R.Reachable x v) (hallB : ∀ v, B.Reachable x v)
    (hleR : R ≤ G) (hleB : B ≤ G)
    (hdis : Disjoint R.edgeSet B.edgeSet) :
    HasTwoEdgeDisjointCyclesSameVertexSet G :=
  (hasPairF_iff G).mp
    (hasPair_of_connected_factors G R B x hcycR hcycB hnR hnB hallR hallB hleR hleB hdis)

end Erdos585.CycleFactors
