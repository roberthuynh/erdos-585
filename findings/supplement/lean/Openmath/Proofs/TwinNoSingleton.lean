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
import Openmath.Proofs.TwinCoreForcing
import Mathlib.Logic.Equiv.Basic

/-!
# Actual bipartite hosts without singleton twin classes

The finite partition is constructed from the host's right neighborhoods. No
quotient graph or cycle witness is part of the final forcing hypotheses.
-/

namespace Erdos585.TwinNoSingleton

open SimpleGraph Finset

variable {A R : Type*} [Fintype A] [Fintype R] [DecidableEq R]
    (G : SimpleGraph (A ⊕ R)) [DecidableRel G.Adj]

/-- The actual right neighborhood of a left vertex. -/
def rightNeighborhood (a : A) : Finset R :=
  univ.filter fun r => G.Adj (.inl a) (.inr r)

omit [Fintype A] [DecidableEq R] in
@[simp] theorem mem_rightNeighborhood (a : A) (r : R) :
    r ∈ rightNeighborhood G a ↔ G.Adj (.inl a) (.inr r) := by
  simp [rightNeighborhood]

/-- Exactly the right neighborhoods that occur in the host. -/
def classSet : Finset (Finset R) := univ.image (rightNeighborhood G)

/-- An equal-neighborhood class is named by its common right neighborhood. -/
abbrev TwinClass := {s : Finset R // s ∈ classSet G}

/-- The actual left vertices in one equal-neighborhood class. -/
abbrev Fiber (i : TwinClass G) := {a : A // rightNeighborhood G a = i.val}

def classSize (i : TwinClass G) : ℕ := Fintype.card (Fiber G i)

theorem classSize_ge_two
    (htwins : ∀ a : A, ∃ b : A, b ≠ a ∧
      ∀ r : R, G.Adj (.inl a) (.inr r) ↔ G.Adj (.inl b) (.inr r))
    (i : TwinClass G) : 2 ≤ classSize G i := by
  obtain ⟨a, _, ha⟩ := mem_image.mp i.property
  obtain ⟨b, hba, hab⟩ := htwins a
  have hneigh : rightNeighborhood G b = rightNeighborhood G a := by
    ext r
    simpa only [mem_rightNeighborhood] using (hab r).symm
  have hcard : 1 < Fintype.card (Fiber G i) :=
    Fintype.one_lt_card_iff.mpr
      ⟨⟨a, ha⟩, ⟨b, hneigh.trans ha⟩, by
        intro h
        exact hba (congrArg Subtype.val h).symm⟩
  exact hcard

/-- Enumerating each exact fiber and forgetting its neighborhood label gives A. -/
noncomputable def leftEquiv : (Σ i : TwinClass G, Fin (classSize G i)) ≃ A :=
  (Equiv.sigmaCongrRight fun i => (Fintype.equivFin (Fiber G i)).symm).trans
    (Equiv.sigmaSubtypeFiberEquiv (rightNeighborhood G)
      (fun s => s ∈ classSet G)
      (fun a => mem_image.mpr ⟨a, mem_univ _, rfl⟩))

theorem leftEquiv_neighborhood (i : TwinClass G) (a : Fin (classSize G i)) :
    rightNeighborhood G (leftEquiv G ⟨i, a⟩) = i.val :=
  ((Fintype.equivFin (Fiber G i)).symm a).property

/-- Incidences are read from the actual common neighborhoods. -/
def incidences : Finset (TwinClass G × R) :=
  univ.filter fun e => e.2 ∈ e.1.val

@[simp] theorem mem_incidences (i : TwinClass G) (r : R) :
    (i, r) ∈ incidences G ↔ r ∈ i.val := by
  simp [incidences]

/-- The grouped presentation is isomorphic to the given graph. -/
noncomputable def groupedIso
    (hleft : ∀ a b : A, ¬ G.Adj (.inl a) (.inl b))
    (hright : ∀ r s : R, ¬ G.Adj (.inr r) (.inr s)) :
    TwinCoreForcing.groupedGraph (incidences G) (classSize G) ≃g G where
  toEquiv := (leftEquiv G).sumCongr (Equiv.refl R)
  map_rel_iff' := by
    intro x y
    cases x with
    | inl x =>
      cases y with
      | inl y => exact iff_false_intro (hleft _ _)
      | inr r =>
        change G.Adj (.inl (leftEquiv G x)) (.inr r) ↔ (x.1, r) ∈ incidences G
        rw [← mem_rightNeighborhood, mem_incidences, leftEquiv_neighborhood]
    | inr r =>
      cases y with
      | inl y =>
        change G.Adj (.inr r) (.inl (leftEquiv G y)) ↔ (y.1, r) ∈ incidences G
        rw [G.adj_comm, ← mem_rightNeighborhood, mem_incidences,
          leftEquiv_neighborhood]
      | inr s => exact iff_false_intro (hright _ _)

/-- An actual capped bipartite host at the critical density forces the faithful
cycle pair whenever every left vertex has a distinct equal-neighborhood twin. -/
theorem hasPair_of_no_singleton_twins
    (hleft : ∀ a b : A, ¬ G.Adj (.inl a) (.inl b))
    (hright : ∀ r s : R, ¬ G.Adj (.inr r) (.inr s))
    (hmax : ∀ v, G.degree v ≤ 6)
    (hedges : G.edgeFinset.card + 2 = 3 * Fintype.card (A ⊕ R))
    (htwins : ∀ a : A, ∃ b : A, b ≠ a ∧
      ∀ r : R, G.Adj (.inl a) (.inr r) ↔ G.Adj (.inl b) (.inr r)) :
    HasTwoEdgeDisjointCyclesSameVertexSet G := by
  classical
  let e := groupedIso G hleft hright
  have hgroupmax : ∀ v,
      (TwinCoreForcing.groupedGraph (incidences G) (classSize G)).degree v ≤ 6 := by
    intro v
    rw [← e.degree_eq v]
    exact hmax (e v)
  have hgroupedges :
      (TwinCoreForcing.groupedGraph (incidences G) (classSize G)).edgeFinset.card + 2 =
        3 * Fintype.card ((Σ i : TwinClass G, Fin (classSize G i)) ⊕ R) := by
    rw [e.card_edgeFinset_eq, Fintype.card_congr e.toEquiv]
    exact hedges
  have hp := TwinCoreForcing.groupedGraph_hasPair_of_no_singletons
    (incidences G) (classSize G) (classSize_ge_two G htwins) hgroupmax hgroupedges
  exact TwinCoreForcing.faithfulPair_map hp e.toHom e.injective

end Erdos585.TwinNoSingleton
