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
import Openmath.Proofs.BipartiteSeparation
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

/-! # The local obstruction used by the factor-exchange experiment

Removing one designated edge from each planted Hamilton cycle leaves a graph
with no spanning cycle. Two cuts, both incident to vertex 4, prove the claim.
The complete 54-vertex recoloring obstruction is a separate written argument.
-/
open SimpleGraph Finset
namespace Erdos585.FactorExchange
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

def reduced : SimpleGraph (Fin 18) :=
  BipartiteSeparation.graph.deleteEdges {s(0,17), s(1,13)}
instance : DecidableRel reduced.Adj := inferInstanceAs
  (DecidableRel (BipartiteSeparation.graph.deleteEdges _).Adj)

def side : Fin 2 → Finset (Fin 18) := ![
  {0,1,2,3,9,10,11,12}, {5,6,7,8,13,14,15,16,17}]
def cut : Fin 2 → Finset (Sym2 (Fin 18)) := ![
  {s(4,10),s(4,12)}, {s(4,13),s(4,16)}]
def color (i : Fin 2) (v : Fin 18) : Bool := decide (v ∈ side i)

lemma cut_valid : ∀ i a b, reduced.Adj a b → color i a ≠ color i b → s(a,b) ∈ cut i :=
  by decide
lemma cut_card : ∀ i, (cut i).card = 2 := by decide
lemma color_nonconstant : ∀ i, ∃ a b, color i a ≠ color i b := by decide

lemma spanning_uses_cut {u : Fin 18} (p : reduced.Walk u u) (hp : p.IsCycle)
    (hspan : p.support.toFinset = univ) (i : Fin 2) : cut i ⊆ p.edges.toFinset := by
  have hmem : ∀ v, v ∈ p.support := by
    intro v
    rw [← List.mem_toFinset, hspan]
    exact mem_univ v
  obtain ⟨a,b,hab⟩ := color_nonconstant i
  have htwo : 2 ≤ (cut i ∩ p.edges.toFinset).card := by
    by_cases h : color i u = color i a
    · exact two_le_card_cut_edges (color i) (cut i) (cut_valid i) p hp.isTrail (hmem b)
        (fun he => hab (h.symm.trans he))
    · exact two_le_card_cut_edges (color i) (cut i) (cut_valid i) p hp.isTrail (hmem a) h
  have heq : cut i ∩ p.edges.toFinset = cut i :=
    eq_of_subset_of_card_le inter_subset_left (by simpa only [cut_card] using htwo)
  exact (inter_eq_left.mp heq)

/-- The two surviving cuts would force four neighbors of vertex 4 on one cycle. -/
theorem no_spanning_cycle {u : Fin 18} (p : reduced.Walk u u) (hp : p.IsCycle) :
    p.support.toFinset ≠ univ := by
  intro hspan
  have hmem : ∀ v, v ∈ p.support := by
    intro v
    rw [← List.mem_toFinset, hspan]
    exact mem_univ v
  have h0 := spanning_uses_cut p hp hspan 0
  have h1 := spanning_uses_cut p hp hspan 1
  have hsub : ({10,12,13,16} : Finset (Fin 18)) ⊆
      p.support.toFinset.filter (fun w => s(4,w) ∈ p.edges) := by
    intro w hw
    simp only [mem_insert, mem_singleton] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · exact mem_filter.mpr ⟨List.mem_toFinset.mpr (hmem _),
        List.mem_toFinset.mp (h0 (by decide))⟩
    · exact mem_filter.mpr ⟨List.mem_toFinset.mpr (hmem _),
        List.mem_toFinset.mp (h0 (by decide))⟩
    · exact mem_filter.mpr ⟨List.mem_toFinset.mpr (hmem _),
        List.mem_toFinset.mp (h1 (by decide))⟩
    · exact mem_filter.mpr ⟨List.mem_toFinset.mpr (hmem _),
        List.mem_toFinset.mp (h1 (by decide))⟩
  have hle := card_le_card hsub
  have hcard : ({10,12,13,16} : Finset (Fin 18)).card = 4 := by decide
  rw [hcard, card_filter_mem_edges hp (hmem 4)] at hle
  omega

end Erdos585.FactorExchange
