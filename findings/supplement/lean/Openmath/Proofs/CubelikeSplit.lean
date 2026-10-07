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
import Openmath.Proofs.CubelikeWitness
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

/-!
# Incidence splitting does not preserve faithful-pair avoidance

A fourteen-vertex bipartite graph is obtained by identifying two disjoint
antipodal pairs on one shore of Q₄. Its connected degree-four core forces
every putative faithful pair to use all eight edges at a hub, which is
impossible. Splitting just the two degree-eight hubs into their original
four-neighbor groups recovers the actual positive four-cube.
-/

open SimpleGraph Finset

namespace Erdos585.CubelikeSplit

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

/-- Left indices 0 through 7; hubs 8,9; four other right vertices 10 through 13. -/
def source : SimpleGraph (Fin 14) := .fromRel fun a b =>
  (a, b) ∈ ([
    (0,8),(0,9),(1,8),(1,9),(2,8),(2,9),(3,8),(3,9),
    (4,8),(4,9),(5,8),(5,9),(6,8),(6,9),(7,8),(7,9),
    (0,10),(0,12),(1,11),(1,13),(2,10),(2,11),(3,10),(3,11),
    (4,12),(4,13),(5,12),(5,13),(6,10),(6,12),(7,11),(7,13)
  ] : List (Fin 14 × Fin 14))

instance : DecidableRel source.Adj :=
  inferInstanceAs (DecidableRel (SimpleGraph.fromRel _).Adj)

/-- The actual vertex identification, with nonsingleton fibers {0,15} and {3,12}. -/
def collapse : Fin 16 → Fin 14 := ![8,0,1,9,2,10,11,3,4,12,13,5,9,6,7,8]

def core : Finset (Fin 14) := univ.erase 8 |>.erase 9

theorem source_bipartite : source.IsBipartite := by
  refine ⟨⟨fun v => if v.val < 8 then 0 else 1, ?_⟩⟩
  decide

theorem source_degrees : ∀ v, source.degree v = if v = 8 ∨ v = 9 then 8 else 4 := by
  decide

lemma core_degree : ∀ v ∈ core, source.degree v = 4 := by decide

lemma core_connected : (source.induce (↑core : Set (Fin 14))).Connected := by decide

/-- Actual adjacency closure propagates across the nonhub core. -/
lemma core_propagate (P : Fin 14 → Prop)
    (hstep : ∀ a b, a ∈ core → P a → source.Adj a b → P b)
    {x y : Fin 14} (hx : x ∈ core) (hy : y ∈ core) (hp : P x) : P y := by
  have follow : ∀ {a b : (↑core : Set (Fin 14))},
      (source.induce (↑core : Set (Fin 14))).Walk a b → P a.val → P b.val := by
    intro a b w
    induction w with
    | nil => exact id
    | @cons a b c hab w ih =>
      intro ha
      exact ih (hstep a.val b.val a.property ha hab)
  exact follow (core_connected.preconnected ⟨x, hx⟩ ⟨y, hy⟩).some hp

/-- The source has no actual edge-disjoint cycle pair on any common vertex support. -/
theorem source_avoiding : ¬ HasPairF source := by
  rintro ⟨u, v, p, q, hp, hq, hS, hE⟩
  have key : ∀ x, x ∈ core → x ∈ p.support.toFinset →
      ∀ w, source.Adj x w → s(x,w) ∈ p.edges.toFinset ∪ q.edges.toFinset := by
    intro x hx hi w hw
    have h4 := card_neighbors_of_pair hp hq hS hE (List.mem_toFinset.mp hi)
    have hsub : p.support.toFinset.filter
        (fun w => s(x,w) ∈ p.edges.toFinset ∪ q.edges.toFinset) ⊆
        source.neighborFinset x := by
      intro z hz
      exact (mem_neighborFinset _ _ _).2
        (mem_support_and_adj_of_mem_union_edges hS (mem_filter.mp hz).2).2
    have heq := Finset.eq_of_subset_of_card_le hsub
      (by rw [card_neighborFinset_eq_degree, core_degree x hx, h4])
    have hw' := (mem_neighborFinset _ _ _).2 hw
    rw [← heq, mem_filter] at hw'
    exact hw'.2
  have hcore : ∃ x ∈ core, x ∈ p.support.toFinset := by
    by_contra h
    push Not at h
    have hsub : p.support.toFinset ⊆ ({8,9} : Finset (Fin 14)) := by
      intro x hx
      have hn : x ∉ core := fun hc => h x hc hx
      simp [core] at hn
      simp only [mem_insert, mem_singleton]
      tauto
    have h5 := five_le_card_support hp hq hS hE
    have hc := card_le_card hsub
    have ht : ({8,9} : Finset (Fin 14)).card = 2 := by decide
    omega
  obtain ⟨x, hx, hxs⟩ := hcore
  have hall : ∀ y ∈ core, y ∈ p.support.toFinset := by
    intro y hy
    apply core_propagate (fun z => z ∈ p.support.toFinset) ?_ hx hy hxs
    intro a b ha hpa hab
    exact (mem_support_and_adj_of_mem_union_edges hS (key a ha hpa b hab)).1
  have hspoke : ∀ y : Fin 14, y ∈ ({0,1,2,3,4,5,6,7} : Finset (Fin 14)) →
      s(8,y) ∈ p.edges.toFinset ∪ q.edges.toFinset := by
    intro y hy
    have hyc : y ∈ core :=
      (by decide : ∀ z : Fin 14, z ∈ ({0,1,2,3,4,5,6,7} : Finset (Fin 14)) →
        z ∈ core) y hy
    rw [Sym2.eq_swap]
    exact key y hyc (hall y hyc) 8
      ((by decide : ∀ z : Fin 14, z ∈ ({0,1,2,3,4,5,6,7} : Finset (Fin 14)) →
        source.Adj z 8) y hy)
  have hh : (8 : Fin 14) ∈ p.support := by
    have he : s(0,8) ∈ p.edges.toFinset ∪ q.edges.toFinset := by
      rw [Sym2.eq_swap]
      exact hspoke 0 (by decide)
    exact List.mem_toFinset.mp (mem_support_and_adj_of_mem_union_edges hS he).1
  have h4 := card_neighbors_of_pair hp hq hS hE hh
  have hsub : ({0,1,2,3,4,5,6,7} : Finset (Fin 14)) ⊆ p.support.toFinset.filter
      (fun y => s(8,y) ∈ p.edges.toFinset ∪ q.edges.toFinset) := by
    intro y hy
    have hyc : y ∈ core :=
      (by decide : ∀ z : Fin 14, z ∈ ({0,1,2,3,4,5,6,7} : Finset (Fin 14)) →
        z ∈ core) y hy
    exact mem_filter.mpr ⟨hall y hyc, hspoke y hy⟩
  have hc := card_le_card hsub
  have ht : ({0,1,2,3,4,5,6,7} : Finset (Fin 14)).card = 8 := by decide
  omega

theorem collapse_surjective : Function.Surjective collapse := by decide

/-- All and only the two displayed vertex fibers are split in the output. -/
theorem collapse_fibers : ∀ v : Fin 14,
    (univ.filter fun i : Fin 16 => collapse i = v).card =
      if v = 8 ∨ v = 9 then 2 else 1 := by decide

/-- Every source edge comes from actual output edges, with no inserted adjacency. -/
theorem adjacency_quotient : ∀ x y : Fin 14, source.Adj x y ↔
    ∃ a b : Fin 16, collapse a = x ∧ collapse b = y ∧ CubelikeWitness.q4.Adj a b := by
  decide

/-- Distinct output incidence edges do not merge under the vertex identification. -/
theorem edge_injective : ∀ a b c d : Fin 16,
    CubelikeWitness.q4.Adj a b → CubelikeWitness.q4.Adj c d →
    collapse a = collapse c → collapse b = collapse d → a = c ∧ b = d := by decide

theorem output_bipartite : CubelikeWitness.q4.IsBipartite := by
  refine ⟨⟨fun v => if CubelikeWitness.weight4 v.val % 2 = 0 then 0 else 1, ?_⟩⟩
  decide

theorem output_regular : CubelikeWitness.q4.IsRegularOfDegree 4 := by
  change ∀ v, CubelikeWitness.q4.degree v = 4
  decide

/-- Actual neighborhood splitting can turn an avoiding bipartite graph into a regular
bipartite graph with a faithful pair. The edge correspondence preserves every incidence. -/
theorem counterexample :
    source.IsBipartite ∧ ¬ HasTwoEdgeDisjointCyclesSameVertexSet source ∧
    CubelikeWitness.q4.IsBipartite ∧ CubelikeWitness.q4.IsRegularOfDegree 4 ∧
    HasTwoEdgeDisjointCyclesSameVertexSet CubelikeWitness.q4 ∧
    Function.Surjective collapse ∧
    (∀ v : Fin 14, (univ.filter fun i : Fin 16 => collapse i = v).card =
      if v = 8 ∨ v = 9 then 2 else 1) ∧
    (∀ x y : Fin 14, source.Adj x y ↔
      ∃ a b : Fin 16, collapse a = x ∧ collapse b = y ∧ CubelikeWitness.q4.Adj a b) ∧
    (∀ a b c d : Fin 16, CubelikeWitness.q4.Adj a b → CubelikeWitness.q4.Adj c d →
      collapse a = collapse c → collapse b = collapse d → a = c ∧ b = d) := by
  exact ⟨source_bipartite, fun h => source_avoiding ((hasPairF_iff source).mpr h),
    output_bipartite, output_regular, (hasPairF_iff _).mp CubelikeWitness.hasPair_q4,
    collapse_surjective, collapse_fibers, adjacency_quotient, edge_injective⟩

end Erdos585.CubelikeSplit
