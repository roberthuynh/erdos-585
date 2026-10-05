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
import Openmath.Proofs.BipartiteBalance
import Openmath.Proofs.DensityCore

/-!
# Two hubs without an independence assumption

A rim density certificate excludes forbidden pairs even when the hubs are
adjacent. The twelve-vertex specialization is the join of K₂ and Petersen.
-/
open SimpleGraph Finset
namespace Erdos585.AdjacentHubs
open BipartiteBalance

variable {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]

/-- At least three rim vertices remain after removing at most two hubs. -/
def RimSparse (c : V → Bool) : Prop :=
  ∀ R : Finset V, (∀ x ∈ R, c x = true) → 3 ≤ R.card →
    (∀ x ∈ R, 2 ≤ (R.filter (G.Adj x)).card) →
    (DensityCore.inside G R).card + 4 < 2 * R.card

omit [Fintype V] [DecidableRel G.Adj] in
open Classical in
lemma walk_true_weight_le (c : V → Bool) {a : V} (p : G.Walk a a) :
    (∑ e ∈ p.edges.toFinset, edgeWeight (fun v => if c v then 1 else -1) e) ≤
      2 * ((p.edges.toFinset.filter (sameTrue c)).card : ℤ) := by
  classical
  calc
    _ ≤ ∑ e ∈ p.edges.toFinset, (if sameTrue c e then (2 : ℤ) else 0) := by
      apply sum_le_sum
      intro e _
      induction e using Sym2.inductionOn with | _ a b => ?_
      cases ha : c a <;> cases hb : c b <;> simp [sameTrue, ha, hb]
    _ = _ := by simp [sum_ite, mul_comm]

/-- Sparse rims exclude a pair with at most two hubs, adjacent or otherwise. -/
theorem not_hasPair (c : V → Bool)
    (hcap : (univ.filter fun x => c x = false).card ≤ 2)
    (hsparse : RimSparse (G := G) c) : ¬ HasPairF G := by
  classical
  rintro ⟨u, v, p, q, hp, hq, hS, hE⟩
  let S := p.support.toFinset
  let R := S.filter fun x => c x = true
  let T := S.filter fun x => c x = false
  let U := p.edges.toFinset ∪ q.edges.toFinset
  have ht : T.card ≤ 2 := (card_le_card (show T ⊆ univ.filter (fun x => c x = false)
      from fun x hx => mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hx).2⟩)).trans hcap
  have hrim : ∀ x ∈ R, c x = true := fun x hx => (mem_filter.mp hx).2
  have hpart : R ∪ T = S := by
    ext x
    cases hc : c x <;> simp [R, T, hc]
  have hdegree : ∀ x ∈ S, (S.filter fun w => s(x,w) ∈ U).card = 4 := by
    intro x hx
    exact card_neighbors_of_pair hp hq hS hE (List.mem_toFinset.mp hx)
  have hR : 3 ≤ R.card := by
    have htotal := card_union_le R T
    rw [hpart] at htotal
    have hsize := five_le_card_support hp hq hS hE
    change 5 ≤ S.card at hsize
    omega
  have hmin : ∀ x ∈ R, 2 ≤ (R.filter (G.Adj x)).card := by
    intro x hx
    have hxs : x ∈ S := (mem_filter.mp hx).1
    have hsub : S.filter (fun w => s(x,w) ∈ U) ⊆ R.filter (G.Adj x) ∪ T := by
      intro w hw
      obtain ⟨hws, he⟩ := mem_filter.mp hw
      have ha := (mem_support_and_adj_of_mem_union_edges hS he).2
      cases hc : c w
      · exact mem_union_right _ (mem_filter.mpr ⟨hws, hc⟩)
      · exact mem_union_left _ (mem_filter.mpr ⟨mem_filter.mpr ⟨hws, hc⟩, ha⟩)
    have hh := (card_le_card hsub).trans (card_union_le _ _)
    rw [hdegree x hxs] at hh
    omega
  have hweight : (∑ x ∈ S, (if c x then (1 : ℤ) else -1)) =
      (R.card : ℤ) - (T.card : ℤ) := by
    simp [R, T, sum_ite, ← Bool.not_eq_true, sub_eq_add_neg]
  have hwp := walk_true_weight_le c p
  have hwq := walk_true_weight_le c q
  rw [cycle_weight_sum _ hp] at hwp
  rw [cycle_weight_sum _ hq, ← hS] at hwq
  change 2 * (∑ x ∈ S, _) ≤ 2 * _ at hwp hwq
  rw [hweight] at hwp hwq
  have hdis : Disjoint (p.edges.toFinset.filter (sameTrue c))
      (q.edges.toFinset.filter (sameTrue c)) := hE.mono (filter_subset _ _) (filter_subset _ _)
  have hcard : (U.filter (sameTrue c)).card =
      (p.edges.toFinset.filter (sameTrue c)).card +
      (q.edges.toFinset.filter (sameTrue c)).card := by
    rw [show U.filter (sameTrue c) = p.edges.toFinset.filter (sameTrue c) ∪
      q.edges.toFinset.filter (sameTrue c) from filter_union _ _ _, card_union_of_disjoint hdis]
  have hsub : U.filter (sameTrue c) ⊆ DensityCore.inside G R := by
    intro e he
    obtain ⟨heu, hec⟩ := mem_filter.mp he
    induction e using Sym2.inductionOn with | _ a b => ?_
    have hb := mem_support_and_adj_of_mem_union_edges hS heu
    have ha : a ∈ S := by
      rw [Sym2.eq_swap] at heu
      exact (mem_support_and_adj_of_mem_union_edges hS heu).1
    exact mem_inter.mpr ⟨mem_edgeFinset.mpr hb.2, mk_mem_sym2_iff.mpr
      ⟨mem_filter.mpr ⟨ha, hec a (by simp)⟩, mem_filter.mpr ⟨hb.1, hec b (by simp)⟩⟩⟩
  have hd := card_le_card hsub
  have hs := hsparse R hrim hR hmin
  omega

/-- The twelve-vertex witness. -/
def graph : SimpleGraph (Fin 12) := .fromRel fun a b =>
  (a,b) ∈ ([(0,3),(0,6),(0,9),(0,10),(0,11),(1,4),(1,6),(1,8),
    (1,10),(1,11),(2,5),(2,6),(2,7),(2,10),(2,11),(3,7),
    (3,8),(3,10),(3,11),(4,7),(4,9),(4,10),(4,11),(5,8),
    (5,9),(5,10),(5,11),(6,10),(6,11),(7,10),(7,11),(8,10),
    (8,11),(9,10),(9,11),(10,11)] : List (Fin 12 × Fin 12))
instance : DecidableRel graph.Adj := inferInstanceAs (DecidableRel (SimpleGraph.fromRel _).Adj)

def rim (x : Fin 12) : Bool := x.val < 10

set_option maxRecDepth 65536 in
set_option maxHeartbeats 20000000 in
lemma graph_sparse : RimSparse (G := graph) rim := by
  unfold RimSparse
  decide

lemma graph_pairfree : ¬ HasPairF graph :=
  not_hasPair rim (by decide) graph_sparse

lemma graph_edge_count : graph.edgeFinset.card = 36 := by decide

/-- A kernel-checked lower bound on twelve vertices. -/
theorem thirty_six_le : 36 ≤ maxEdges 12 := by
  apply le_maxEdges_of_mem
  refine ⟨graph, graph_pairfree, ?_⟩
  rw [← coe_edgeFinset, Set.ncard_coe_finset, graph_edge_count]

end Erdos585.AdjacentHubs
