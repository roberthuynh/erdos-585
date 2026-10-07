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
import Openmath.Proofs.CutGluing

/-!
# A five-regular graph on eighteen vertices without a forbidden cycle pair

The nine-vertex block has a triangle `{0, 1, 2}` joined to every vertex of `{3, 4, 5}`, and a
triangle `{6, 7, 8}` with `6 ~ 3, 4, 5`, `7 ~ 3, 4` and `8 ~ 5`. Every vertex of the block has
at most three neighbors with a smaller label (the block is 3-degenerate). In a pair, the largest
vertex of the common vertex set would need four neighbors in that set, so the block has no pair.

Two copies of the block, the second with every label shifted by 9, joined by the three edges
`(8, 17)`, `(8, 16)` and `(7, 17)`, form a five-regular graph on eighteen vertices. A pair cannot
cross a cut of at most three edges (`CutGluing.lean`), so this graph has no pair either.
The construction is not a novelty claim.
-/

open SimpleGraph Finset

namespace Erdos585.RegularFive18

/-- If every vertex has at most three neighbors with a smaller label, there is no pair: the
largest vertex of the common vertex set has four neighbors along the pair, all smaller. -/
theorem not_hasPairF_of_card_lt_le_three {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : ∀ v, ((G.neighborFinset v).filter (· < v)).card ≤ 3) : ¬ HasPairF G := by
  rintro ⟨u, w, p, q, hp, hq, hS, hE⟩
  obtain ⟨v, hv, hmax⟩ :=
    p.support.toFinset.exists_max_image id ⟨u, List.mem_toFinset.2 p.start_mem_support⟩
  have hsub : pairNbrs p q v ⊆ (G.neighborFinset v).filter (· < v) := by
    intro x hx
    have hadj := adj_of_mem_pairNbrs hx
    rw [Finset.mem_filter, mem_neighborFinset]
    exact ⟨hadj, lt_of_le_of_ne
      (hmax x (List.mem_toFinset.2 (mem_support_of_mem_pairNbrs hS (mem_pairNbrs_symm hx))))
      hadj.ne.symm⟩
  have h4 := card_pairNbrs hp hq hS hE (List.mem_toFinset.1 hv)
  have hle := card_le_card hsub
  have h3 := h v
  omega

/-- The nine-vertex block: a triangle joined to an independent triple, and a second triangle
attached to that triple. -/
def block : SimpleGraph (Fin 9) := .fromRel fun a b =>
  (a, b) ∈ ([(0,1),(0,2),(1,2),(0,3),(0,4),(0,5),(1,3),(1,4),(1,5),(2,3),(2,4),(2,5),
    (6,7),(6,8),(7,8),(3,6),(4,6),(5,6),(3,7),(4,7),(5,8)] : List (Fin 9 × Fin 9))

instance : DecidableRel block.Adj := inferInstanceAs (DecidableRel (SimpleGraph.fromRel _).Adj)

theorem block_not_hasPair : ¬ HasPairF block :=
  not_hasPairF_of_card_lt_le_three block (by decide)

/-- The block vertex of a vertex of the 18-vertex graph: its label modulo 9. -/
def modNine (x : Fin 18) : Fin 9 := ⟨x.val % 9, Nat.mod_lt _ (by decide)⟩

/-- The 18-vertex construction: two copies of the block joined by three edges. -/
def graph : SimpleGraph (Fin 18) := .fromRel fun a b =>
  (a.val / 9 = b.val / 9 ∧ block.Adj (modNine a) (modNine b)) ∨
    (a, b) ∈ ([(8,17),(8,16),(7,17)] : List (Fin 18 × Fin 18))

instance : DecidableRel graph.Adj := inferInstanceAs (DecidableRel (SimpleGraph.fromRel _).Adj)

theorem graph_not_hasPair : ¬ HasPairF graph := by
  apply not_hasPairF_of_small_cut_map (fun x : Fin 18 => x.val / 9)
    {s(8,17), s(8,16), s(7,17)} (by decide) block modNine (by decide) block_not_hasPair
  · decide
  · decide

theorem graph_degree : ∀ v, graph.degree v = 5 := by decide

theorem graph_edge_count : graph.edgeFinset.card = 45 := by
  have h := sum_degrees_eq_twice_card_edges graph
  simp only [graph_degree, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul] at h
  omega

/-- Degree five alone does not force two edge-disjoint cycles with the same vertex set, already
on eighteen vertices. -/
theorem exists_five_regular_pairfree :
    ∃ G : SimpleGraph (Fin 18), (∀ v, (G.neighborSet v).ncard = 5) ∧
      ¬ HasTwoEdgeDisjointCyclesSameVertexSet G := by
  refine ⟨graph, ?_, ?_⟩
  · intro v
    simpa only [← card_neighborFinset_eq_degree, ← Set.ncard_coe_finset,
      coe_neighborFinset] using graph_degree v
  · exact (hasPairF_iff graph).not.mp graph_not_hasPair

end Erdos585.RegularFive18
