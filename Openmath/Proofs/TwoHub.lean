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
# A two-hub density criterion

An independent set of at most two hubs leaves a useful density obstruction on
the remaining vertices. The concrete eleven-vertex graph below has 31 edges.
-/
open SimpleGraph Finset
namespace Erdos585.TwoHub
open BipartiteBalance

variable {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A density certificate on the rim, restricted to sets that could support a pair. -/
def RimSparse (c : V → Bool) : Prop :=
  ∀ R : Finset V, (∀ x ∈ R, c x = true) → 4 ≤ R.card →
    (∀ x ∈ R, 2 ≤ (R.filter (G.Adj x)).card) →
    (DensityCore.inside G R).card + 4 < 2 * R.card

/-- Two independent hubs cannot overcome the rim density certificate. -/
theorem not_hasPair (c : V → Bool)
    (hind : ∀ a b, G.Adj a b → c a = true ∨ c b = true)
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
  have hR : 4 ≤ R.card := by
    by_cases hT : T.Nonempty
    · obtain ⟨x, hx⟩ := hT
      have hxs := (mem_filter.mp hx).1
      have hxc := (mem_filter.mp hx).2
      have hsub : S.filter (fun w => s(x,w) ∈ U) ⊆ R := by
        intro w hw
        obtain ⟨hws, he⟩ := mem_filter.mp hw
        have ha := (mem_support_and_adj_of_mem_union_edges hS he).2
        have hc := hind x w ha
        exact mem_filter.mpr ⟨hws, hc.resolve_left (by simp [hxc])⟩
      have hh := card_le_card hsub
      rw [hdegree x hxs] at hh
      exact hh
    · have he : T = ∅ := not_nonempty_iff_eq_empty.mp hT
      have heq : R = S := by simpa [he] using hpart
      rw [heq]
      exact (five_le_card_support hp hq hS hE).trans' (by decide)
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
  have hwp := walk_true_weight c hind p
  have hwq := walk_true_weight c hind q
  rw [cycle_weight_sum _ hp] at hwp
  rw [cycle_weight_sum _ hq, ← hS] at hwq
  change 2 * _ = 2 * (∑ x ∈ S, _) at hwp hwq
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

/-- The 31-edge finite witness. -/
def graph : SimpleGraph (Fin 11) := .fromRel fun a b =>
  (a,b) ∈ ([(0,4),(0,8),(0,9),(0,10),(1,3),(1,7),(1,9),(1,10),
    (2,7),(2,8),(2,9),(2,10),(3,5),(3,8),(3,9),(3,10),(4,6),(4,7),
    (4,9),(4,10),(5,6),(5,8),(5,9),(5,10),(6,7),(6,9),(6,10),
    (7,9),(7,10),(8,9),(8,10)] : List (Fin 11 × Fin 11))
instance : DecidableRel graph.Adj := inferInstanceAs (DecidableRel (SimpleGraph.fromRel _).Adj)

def rim (x : Fin 11) : Bool := x.val < 9

set_option maxRecDepth 65536 in
set_option maxHeartbeats 16000000 in
lemma graph_sparse : RimSparse (G := graph) rim := by
  unfold RimSparse
  decide

lemma graph_pairfree : ¬ HasPairF graph :=
  not_hasPair rim (by decide) (by decide) graph_sparse

lemma graph_edge_count : graph.edgeFinset.card = 31 := by decide

/-- A kernel-checked lower bound. -/
theorem thirty_one_le : 31 ≤ maxEdges 11 := by
  apply le_maxEdges_of_mem
  refine ⟨graph, graph_pairfree, ?_⟩
  rw [← coe_edgeFinset, Set.ncard_coe_finset, graph_edge_count]

end Erdos585.TwoHub
