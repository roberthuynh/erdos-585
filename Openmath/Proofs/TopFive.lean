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
import Openmath.Proofs.Compat

/-!
# Erdős 585: the complete graph on five vertices

$K_5$ contains two edge-disjoint Hamiltonian cycles, and a graph on five vertices with ten edges
is $K_5$. Together these bound the extremal number for $n = 5$ from above by $9$.
-/

open SimpleGraph Finset

namespace Erdos585

/-- The complete graph on five vertices. -/
abbrev K5 : SimpleGraph (Fin 5) := ⊤

lemma top_adj_of_ne {a b : Fin 5} (h : a ≠ b) : K5.Adj a b := by simpa [K5] using h

/-- The Hamiltonian cycle 0-1-2-3-4-0 of $K_5$. -/
def cycA : K5.Walk 0 0 :=
  .cons (top_adj_of_ne (a := 0) (b := 1) (by decide))
    (.cons (top_adj_of_ne (a := 1) (b := 2) (by decide))
      (.cons (top_adj_of_ne (a := 2) (b := 3) (by decide))
        (.cons (top_adj_of_ne (a := 3) (b := 4) (by decide))
          (.cons (top_adj_of_ne (a := 4) (b := 0) (by decide)) .nil))))

/-- The Hamiltonian cycle 0-2-4-1-3-0 of $K_5$, edge-disjoint from the first. -/
def cycB : K5.Walk 0 0 :=
  .cons (top_adj_of_ne (a := 0) (b := 2) (by decide))
    (.cons (top_adj_of_ne (a := 2) (b := 4) (by decide))
      (.cons (top_adj_of_ne (a := 4) (b := 1) (by decide))
        (.cons (top_adj_of_ne (a := 1) (b := 3) (by decide))
          (.cons (top_adj_of_ne (a := 3) (b := 0) (by decide)) .nil))))

lemma cycA_isCycle : cycA.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  exact ⟨by decide, by simp [cycA], by decide⟩

lemma cycB_isCycle : cycB.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  exact ⟨by decide, by simp [cycB], by decide⟩

lemma cycA_cycB_support : cycA.support.toFinset = cycB.support.toFinset := by decide

lemma cycA_cycB_edges : Disjoint cycA.edges.toFinset cycB.edges.toFinset := by decide

/-- $K_5$ contains two edge-disjoint cycles with the same vertex set. -/
theorem hasPair_top_five : HasPairF K5 :=
  ⟨0, 0, cycA, cycB, cycA_isCycle, cycB_isCycle, cycA_cycB_support, cycA_cycB_edges⟩

/-- A graph on five vertices with ten edges is complete. -/
theorem eq_top_of_ncard_edgeSet_eq_ten (G : SimpleGraph (Fin 5)) (h : G.edgeSet.ncard = 10) :
    G = ⊤ := by
  classical
  rw [← coe_edgeFinset, Set.ncard_coe_finset] at h
  have htop : (⊤ : SimpleGraph (Fin 5)).edgeFinset.card = 10 := by
    rw [card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin]
    decide
  have hsub : G.edgeFinset ⊆ (⊤ : SimpleGraph (Fin 5)).edgeFinset :=
    edgeFinset_subset_edgeFinset.mpr le_top
  exact edgeFinset_inj.mp (Finset.eq_of_subset_of_card_le hsub (by rw [h, htop]))

/-- Without two edge-disjoint cycles on the same vertex set, a graph on five vertices has at most
nine edges. -/
theorem ncard_edgeSet_le_nine_of_not_hasPair (G : SimpleGraph (Fin 5))
    (h : ¬ HasPairF G) : G.edgeSet.ncard ≤ 9 := by
  classical
  have hle : G.edgeSet.ncard ≤ 10 := by
    rw [← coe_edgeFinset, Set.ncard_coe_finset]
    have h' := card_edgeFinset_le_card_choose_two (G := G)
    rw [Fintype.card_fin] at h'
    exact h'.trans (by decide)
  by_contra hlt
  have h10 : G.edgeSet.ncard = 10 := by omega
  have hG : G = ⊤ := eq_top_of_ncard_edgeSet_eq_ten G h10
  subst hG
  exact h hasPair_top_five

/-- The upper half of $f(5) = 9$. -/
theorem edgeCounts_five_upper : ∀ m ∈ edgeCounts 5, m ≤ 9 := by
  rintro m ⟨G, hG, rfl⟩
  exact ncard_edgeSet_le_nine_of_not_hasPair G hG

end Erdos585
