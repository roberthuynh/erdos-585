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
# A five-regular graph without a forbidden cycle pair

Four eight-vertex blocks are joined across cuts of sizes three and two.
The construction is not a novelty claim.
-/

open SimpleGraph Finset
namespace Erdos585.RegularFive

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-- The eight-vertex block: the double wheel on C₅ without its hub edge, plus a degree-three vertex. -/
def block : SimpleGraph (Fin 8) := .fromRel fun a b =>
  (a, b) ∈ ([(0,3),(0,4),(0,5),(1,3),(1,4),(1,6),(1,7),(2,3),(2,5),
    (2,6),(2,7),(3,6),(3,7),(4,5),(4,6),(4,7),(5,6),(5,7)] : List (Fin 8 × Fin 8))

instance : DecidableRel block.Adj := inferInstanceAs (DecidableRel (SimpleGraph.fromRel _).Adj)

/-- The surviving seven vertices, in cyclic order and then the two hubs. -/
def toWheel (x : Fin 8) : Fin 5 ⊕ Fin 2 :=
  ![.inl 0, .inl 0, .inl 2, .inl 1, .inl 4, .inl 3, .inr 0, .inr 1] x

def blockPull : block.induce {x | x ≠ 0} →g doubleWheel 5 where
  toFun x := toWheel x.1
  map_rel' := by decide

lemma blockPull_injective : Function.Injective blockPull := by decide

/-- The degree-three vertex cannot occur in a pair; the rest embeds in a double wheel. -/
theorem block_not_hasPair : ¬ HasPairF block := by
  rintro ⟨u, v, p, q, hp, hq, hS, hE⟩
  have hzero : (0 : Fin 8) ∉ p.support :=
    not_mem_support_of_degree_le_three hp hq hS hE (by decide : block.degree 0 ≤ 3)
  have hps : ∀ x ∈ p.support, x ∈ {x : Fin 8 | x ≠ 0} := by
    rintro x hx rfl
    exact hzero hx
  have hqs : ∀ x ∈ q.support, x ∈ {x : Fin 8 | x ≠ 0} := by
    intro x hx
    apply hps
    rwa [← List.mem_toFinset, hS, List.mem_toFinset]
  have hpair := (pair_map_iff (Embedding.induce {x : Fin 8 | x ≠ 0}).toHom
    (Embedding.induce (G := block) _).injective (p.induce _ hps) (q.induce _ hqs)).1
    (by rw [Walk.map_induce, Walk.map_induce]; exact ⟨hp, hq, hS, hE⟩)
  exact doubleWheel_not_hasPair 2 (by omega)
    ((HasPairF.map ⟨_, _, _, _, hpair⟩ blockPull blockPull_injective))

def modEight (x : Fin 16) : Fin 8 := ⟨x.val % 8, Nat.mod_lt _ (by decide)⟩

/-- Two blocks joined by three edges, with two remaining degree deficits. -/
def half : SimpleGraph (Fin 16) := .fromRel fun a b =>
  (a.val / 8 = b.val / 8 ∧ block.Adj (modEight a) (modEight b)) ∨
    (a, b) ∈ ([(0,9),(0,10),(1,8)] : List (Fin 16 × Fin 16))

instance : DecidableRel half.Adj := inferInstanceAs (DecidableRel (SimpleGraph.fromRel _).Adj)

theorem half_not_hasPair : ¬ HasPairF half := by
  apply not_hasPairF_of_small_cut_map (fun x : Fin 16 => x.val / 8)
    {s(0,9), s(0,10), s(1,8)} (by decide) block modEight (by decide) block_not_hasPair
  · decide
  · decide

def modSixteen (x : Fin 32) : Fin 16 := ⟨x.val % 16, Nat.mod_lt _ (by decide)⟩

/-- The 32-vertex construction, formed by joining two halves with two edges. -/
def graph : SimpleGraph (Fin 32) := .fromRel fun a b =>
  (a.val / 16 = b.val / 16 ∧ half.Adj (modSixteen a) (modSixteen b)) ∨
    (a, b) ∈ ([(2,18),(8,24)] : List (Fin 32 × Fin 32))

instance : DecidableRel graph.Adj := inferInstanceAs (DecidableRel (SimpleGraph.fromRel _).Adj)

theorem graph_not_hasPair : ¬ HasPairF graph := by
  apply not_hasPairF_of_small_cut_map (fun x : Fin 32 => x.val / 16)
    {s(2,18), s(8,24)} (by decide) half modSixteen (by decide) half_not_hasPair
  · decide
  · decide

theorem graph_degree : ∀ v, graph.degree v = 5 := by decide

theorem graph_edge_count : graph.edgeFinset.card = 80 := by
  have h := sum_degrees_eq_twice_card_edges graph
  simp only [graph_degree, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul] at h
  omega

/-- Degree five alone does not force two edge-disjoint cycles with the same vertex set. -/
theorem exists_five_regular_pairfree :
    ∃ G : SimpleGraph (Fin 32), (∀ v, (G.neighborSet v).ncard = 5) ∧
      ¬ HasTwoEdgeDisjointCyclesSameVertexSet G := by
  refine ⟨graph, ?_, ?_⟩
  · intro v
    simpa only [← card_neighborFinset_eq_degree, ← Set.ncard_coe_finset,
      coe_neighborFinset] using graph_degree v
  · exact (hasPairF_iff graph).not.mp graph_not_hasPair

end Erdos585.RegularFive
