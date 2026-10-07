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
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

/-!
# Connected even subgraphs do not suffice for Erdős 585

An eleven-vertex bipartite graph has two edge-disjoint connected spanning
subgraphs of positive even degree but no pair of simple cycles on a common
vertex set. The host has degrees six at two hubs and four elsewhere.
This local control is not a novelty claim.
-/

open SimpleGraph Finset
namespace Erdos585.BipartiteEulerian

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

def graph : SimpleGraph (Fin 11) := .fromRel fun a b =>
  (a, b) ∈ ([(0,5),(0,6),(0,7),(0,8),(0,9),(0,10),
    (1,5),(1,6),(1,7),(1,8),(1,9),(1,10),
    (2,5),(2,6),(2,7),(2,8),(3,5),(3,6),(3,9),(3,10),
    (4,7),(4,8),(4,9),(4,10)] : List (Fin 11 × Fin 11))

instance : DecidableRel graph.Adj := inferInstanceAs (DecidableRel (SimpleGraph.fromRel _).Adj)

lemma core_degree : ∀ x : Fin 11, 2 ≤ x.val → graph.degree x = 4 := by decide

/-- Every pair of core vertices is joined by at most three core steps. -/
lemma core_steps : ∀ x y : Fin 11, 2 ≤ x.val → 2 ≤ y.val →
    ∃ a b : Fin 11,
      (x = a ∨ (2 ≤ x.val ∧ graph.Adj x a)) ∧
      (a = b ∨ (2 ≤ a.val ∧ graph.Adj a b)) ∧
      (b = y ∨ (2 ≤ b.val ∧ graph.Adj b y)) := by decide

theorem not_hasPair : ¬ HasPairF graph := by
  rintro ⟨u, v, p, q, hp, hq, hS, hE⟩
  have key : ∀ x : Fin 11, 2 ≤ x.val → x ∈ p.support.toFinset →
      ∀ w, graph.Adj x w → s(x, w) ∈ p.edges.toFinset ∪ q.edges.toFinset := by
    intro x hx hi w hw
    have h4 := card_neighbors_of_pair hp hq hS hE (List.mem_toFinset.1 hi)
    have hsub : p.support.toFinset.filter
        (fun w => s(x, w) ∈ p.edges.toFinset ∪ q.edges.toFinset) ⊆
        graph.neighborFinset x := by
      intro z hz
      exact (mem_neighborFinset _ _ _).2
        (mem_support_and_adj_of_mem_union_edges hS (Finset.mem_filter.1 hz).2).2
    have heq := Finset.eq_of_subset_of_card_le hsub
      (by rw [card_neighborFinset_eq_degree, core_degree x hx, h4])
    have hw' := (mem_neighborFinset _ _ _).2 hw
    rw [← heq, Finset.mem_filter] at hw'
    exact hw'.2
  have step : ∀ x y : Fin 11, x ∈ p.support.toFinset →
      (x = y ∨ (2 ≤ x.val ∧ graph.Adj x y)) → y ∈ p.support.toFinset := by
    intro x y hx h
    rcases h with rfl | ⟨hc, ha⟩
    · exact hx
    · exact (mem_support_and_adj_of_mem_union_edges hS (key x hc hx y ha)).1
  have hcore : ∃ x : Fin 11, 2 ≤ x.val ∧ x ∈ p.support.toFinset := by
    by_contra h
    push Not at h
    have hsub : p.support.toFinset ⊆ ({0, 1} : Finset (Fin 11)) := by
      intro x hx
      have hxlt : x.val < 2 := by
        by_contra hn
        exact h x (by omega) hx
      fin_cases x <;> simp_all
    have h5 := five_le_card_support hp hq hS hE
    have hc := Finset.card_le_card hsub
    have he : ({0, 1} : Finset (Fin 11)).card = 2 := by decide
    omega
  obtain ⟨x, hx, hxs⟩ := hcore
  have hall : ∀ y : Fin 11, 2 ≤ y.val → y ∈ p.support.toFinset := by
    intro y hy
    obtain ⟨a, b, hxa, hab, hby⟩ := core_steps x y hx hy
    exact step b y (step a b (step x a hxs hxa) hab) hby
  have hspoke : ∀ y : Fin 11, 5 ≤ y.val →
      s(0, y) ∈ p.edges.toFinset ∪ q.edges.toFinset := by
    intro y hy
    rw [Sym2.eq_swap]
    exact key y (by omega) (hall y (by omega)) 0
      ((by decide : ∀ y : Fin 11, 5 ≤ y.val → graph.Adj y 0) y hy)
  have hh : (0 : Fin 11) ∈ p.support := by
    have he : s(5, 0) ∈ p.edges.toFinset ∪ q.edges.toFinset := by
      rw [Sym2.eq_swap]; exact hspoke 5 (by decide)
    exact List.mem_toFinset.1 (mem_support_and_adj_of_mem_union_edges hS he).1
  have h4 := card_neighbors_of_pair hp hq hS hE hh
  have hsub : ({5, 6, 7, 8, 9, 10} : Finset (Fin 11)) ⊆ p.support.toFinset.filter
      (fun w => s(0, w) ∈ p.edges.toFinset ∪ q.edges.toFinset) := by
    intro y hy
    have hge : 5 ≤ y.val :=
      (by decide : ∀ y : Fin 11, y ∈ ({5,6,7,8,9,10} : Finset (Fin 11)) → 5 ≤ y.val) y hy
    exact Finset.mem_filter.2 ⟨hall y (by omega), hspoke y hge⟩
  have hc := Finset.card_le_card hsub
  have he : ({5, 6, 7, 8, 9, 10} : Finset (Fin 11)).card = 6 := by decide
  omega

def red : SimpleGraph (Fin 11) := .fromRel fun a b =>
  (a, b) ∈ ([(0,5),(5,2),(2,7),(7,1),(1,9),(9,0),
    (0,6),(6,3),(3,10),(10,4),(4,8),(8,0)] : List (Fin 11 × Fin 11))

def blue : SimpleGraph (Fin 11) := .fromRel fun a b =>
  (a, b) ∈ ([(1,6),(6,2),(2,8),(8,1),
    (1,5),(5,3),(3,9),(9,4),(4,7),(7,0),(0,10),(10,1)] : List (Fin 11 × Fin 11))

instance : DecidableRel red.Adj := inferInstanceAs (DecidableRel (SimpleGraph.fromRel _).Adj)
instance : DecidableRel blue.Adj := inferInstanceAs (DecidableRel (SimpleGraph.fromRel _).Adj)

lemma red_connected : red.Connected := by decide
lemma blue_connected : blue.Connected := by decide

lemma graph_bipartite : graph.IsBipartite := by
  refine ⟨⟨fun x => if x.val < 5 then 0 else 1, ?_⟩⟩
  decide

/-- The even-degree relaxation fails even for a bipartite host with maximum degree six. -/
theorem counterexample :
    graph.IsBipartite ∧
    (∀ v, 4 ≤ graph.degree v ∧ graph.degree v ≤ 6) ∧
    red ≤ graph ∧ blue ≤ graph ∧ Disjoint red blue ∧
    red.Connected ∧ blue.Connected ∧
    (∀ v, 0 < red.degree v ∧ Even (red.degree v)) ∧
    (∀ v, 0 < blue.degree v ∧ Even (blue.degree v)) ∧
    ¬ HasTwoEdgeDisjointCyclesSameVertexSet graph := by
  refine ⟨graph_bipartite, by decide, ?_, ?_, ?_, red_connected,
    blue_connected, by decide, by decide, ?_⟩
  · exact (by decide : ∀ a b, red.Adj a b → graph.Adj a b)
  · exact (by decide : ∀ a b, blue.Adj a b → graph.Adj a b)
  · rw [disjoint_iff]
    ext a b
    decide +revert
  · exact fun h => not_hasPair ((hasPairF_iff graph).2 h)

end Erdos585.BipartiteEulerian
