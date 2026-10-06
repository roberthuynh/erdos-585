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
import Mathlib.Combinatorics.SimpleGraph.Coloring.EdgeLabeling
import Mathlib.Combinatorics.SimpleGraph.Matching

/-! # Actual component-union swaps of a full edge coloring

The operation is defined on actual edges, with its selection indexed by
actual connected components of the original two-color graph. Fullness,
component cycle witnesses, and the original-color palette bound are proved.
-/

namespace Erdos585.KempeSwap104

open SimpleGraph

variable {V C : Type*} {G : SimpleGraph V}

/-- Every vertex has exactly one neighbor in every color. -/
def FullColoring (φ : G.EdgeLabeling C) : Prop :=
  ∀ v c, ∃! w, (φ.labelGraph c).Adj v w

/-- The actual graph consisting of two color classes. -/
def twoFactor (φ : G.EdgeLabeling C) (a b : C) : SimpleGraph V :=
  φ.labelGraph a ⊔ φ.labelGraph b

@[simp] theorem twoFactor_adj (φ : G.EdgeLabeling C) (a b : C) (u v : V) :
    (twoFactor φ a b).Adj u v ↔
      (φ.labelGraph a).Adj u v ∨ (φ.labelGraph b).Adj u v := Iff.rfl

theorem twoFactor_le (φ : G.EdgeLabeling C) (a b : C) : twoFactor φ a b ≤ G :=
  sup_le φ.labelGraph_le φ.labelGraph_le

/-- The actual subgraph consisting of a finite set of original colors. -/
def colorSubgraph (φ : G.EdgeLabeling C) (T : Finset C) : SimpleGraph V :=
  ⨆ c ∈ T, φ.labelGraph c

@[simp] theorem colorSubgraph_adj (φ : G.EdgeLabeling C) (T : Finset C) (u v : V) :
    (colorSubgraph φ T).Adj u v ↔ ∃ c ∈ T, (φ.labelGraph c).Adj u v := by
  simp [colorSubgraph]

theorem colorSubgraph_le (φ : G.EdgeLabeling C) (T : Finset C) : colorSubgraph φ T ≤ G := by
  intro u v huv
  obtain ⟨c, _, hc⟩ := (colorSubgraph_adj φ T u v).mp huv
  exact φ.labelGraph_le hc

/-- Selection by any set of actual two-color components. -/
def Selected (φ : G.EdgeLabeling C) (a b : C)
    (J : Set (twoFactor φ a b).ConnectedComponent) (v : V) : Prop :=
  (twoFactor φ a b).connectedComponentMk v ∈ J

section Swap

variable [DecidableEq C]

/-- At a selected vertex transpose the two colors; all other colors are fixed. -/
noncomputable def swappedLabel (φ : G.EdgeLabeling C) (a b : C)
    (J : Set (twoFactor φ a b).ConnectedComponent) (u v : V) (h : G.Adj u v) : C := by
  classical
  exact if Selected φ a b J u then Equiv.swap a b (φ.get u v h) else φ.get u v h

theorem swappedLabel_symm (φ : G.EdgeLabeling C) (a b : C)
    (J : Set (twoFactor φ a b).ConnectedComponent) (u v : V) (h : G.Adj u v) :
    swappedLabel φ a b J v u h.symm = swappedLabel φ a b J u v h := by
  classical
  have hcomm : φ.get v u h.symm = φ.get u v h := by
    rw [EdgeLabeling.get_comm]
  by_cases hc : φ.get u v h = a ∨ φ.get u v h = b
  · have hfactor : (twoFactor φ a b).Adj u v := by
      rcases hc with hc | hc
      · exact Or.inl ((EdgeLabeling.labelGraph_adj u v).mpr ⟨h, hc⟩)
      · exact Or.inr ((EdgeLabeling.labelGraph_adj u v).mpr ⟨h, hc⟩)
    have heq := ConnectedComponent.connectedComponentMk_eq_of_adj hfactor
    have hsel : Selected φ a b J u ↔ Selected φ a b J v := by
      unfold Selected
      rw [heq]
    by_cases hu : Selected φ a b J u
    · have hv := hsel.mp hu
      simp only [swappedLabel, hu, hv, if_true, hcomm]
    · have hv : ¬Selected φ a b J v := fun hv => hu (hsel.mpr hv)
      simp only [swappedLabel, hu, hv, if_false, hcomm]
  · have ha : φ.get u v h ≠ a := fun ha => hc (Or.inl ha)
    have hb : φ.get u v h ≠ b := fun hb => hc (Or.inr hb)
    simp [swappedLabel, hcomm, Equiv.swap_apply_of_ne_of_ne ha hb]

/-- Swap two colors on any union of their actual components. -/
noncomputable def swap (φ : G.EdgeLabeling C) (a b : C)
    (J : Set (twoFactor φ a b).ConnectedComponent) : G.EdgeLabeling C :=
  EdgeLabeling.mk (swappedLabel φ a b J) (swappedLabel_symm φ a b J)

theorem swap_get (φ : G.EdgeLabeling C) (a b : C)
    (J : Set (twoFactor φ a b).ConnectedComponent) (u v : V) (h : G.Adj u v) :
    (swap φ a b J).get u v h =
      @ite C (Selected φ a b J u) (Classical.propDecidable _)
        (Equiv.swap a b (φ.get u v h)) (φ.get u v h) := by
  rfl

theorem swap_labelGraph_adj_selected (φ : G.EdgeLabeling C) (a b : C)
    (J : Set (twoFactor φ a b).ConnectedComponent) {u : V}
    (hu : Selected φ a b J u) (v : V) (c : C) :
    ((swap φ a b J).labelGraph c).Adj u v ↔
      (φ.labelGraph (Equiv.swap a b c)).Adj u v := by
  rw [EdgeLabeling.labelGraph_adj, EdgeLabeling.labelGraph_adj]
  change (∃ h : G.Adj u v, (swap φ a b J).get u v h = c) ↔
    ∃ h : G.Adj u v, φ.get u v h = Equiv.swap a b c
  simp only [swap_get, hu, if_true, Equiv.swap_apply_eq_iff]

theorem swap_labelGraph_adj_not_selected (φ : G.EdgeLabeling C) (a b : C)
    (J : Set (twoFactor φ a b).ConnectedComponent) {u : V}
    (hu : ¬Selected φ a b J u) (v : V) (c : C) :
    ((swap φ a b J).labelGraph c).Adj u v ↔ (φ.labelGraph c).Adj u v := by
  rw [EdgeLabeling.labelGraph_adj, EdgeLabeling.labelGraph_adj]
  change (∃ h : G.Adj u v, (swap φ a b J).get u v h = c) ↔
    ∃ h : G.Adj u v, φ.get u v h = c
  simp only [swap_get, hu, if_false]

theorem swap_fullColoring (φ : G.EdgeLabeling C) (hφ : FullColoring φ) (a b : C)
    (J : Set (twoFactor φ a b).ConnectedComponent) : FullColoring (swap φ a b J) := by
  classical
  intro u c
  by_cases hu : Selected φ a b J u
  · simpa only [swap_labelGraph_adj_selected φ a b J hu] using hφ u (Equiv.swap a b c)
  · simpa only [swap_labelGraph_adj_not_selected φ a b J hu] using hφ u c

@[simp] theorem swap_empty (φ : G.EdgeLabeling C) (a b : C) : swap φ a b ∅ = φ := by
  apply EdgeLabeling.ext_get
  intro u v h
  simp [swap_get, Selected]

end Swap

theorem twoFactor_neighborSet_nonempty (φ : G.EdgeLabeling C) (hφ : FullColoring φ)
    (a b : C) (v : V) : ((twoFactor φ a b).neighborSet v).Nonempty := by
  obtain ⟨w, hw, _⟩ := hφ v a
  exact ⟨w, Or.inl hw⟩

theorem twoFactor_neighborSet_ncard (φ : G.EdgeLabeling C) (hφ : FullColoring φ)
    {a b : C} (hab : a ≠ b) (v : V) : ((twoFactor φ a b).neighborSet v).ncard = 2 := by
  obtain ⟨x, hx, hux⟩ := hφ v a
  obtain ⟨y, hy, huy⟩ := hφ v b
  have hxy : x ≠ y := by
    intro heq
    subst y
    obtain ⟨h, ha⟩ := (EdgeLabeling.labelGraph_adj v x).mp hx
    obtain ⟨h', hb⟩ := (EdgeLabeling.labelGraph_adj v x).mp hy
    exact hab (ha.symm.trans hb)
  apply Set.ncard_eq_two.mpr
  refine ⟨x, y, hxy, ?_⟩
  ext z
  change ((φ.labelGraph a).Adj v z ∨ (φ.labelGraph b).Adj v z) ↔ z ∈ ({x, y} : Set V)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro (hz | hz)
    · exact Or.inl (hux z hz)
    · exact Or.inr (huy z hz)
  · rintro (rfl | rfl)
    · exact Or.inl hx
    · exact Or.inr hy

theorem twoFactor_isCycles (φ : G.EdgeLabeling C) (hφ : FullColoring φ)
    {a b : C} (hab : a ≠ b) : (twoFactor φ a b).IsCycles := by
  intro v _
  exact twoFactor_neighborSet_ncard φ hφ hab v

/-- Every vertex lies on an actual cycle with exactly its component's support. -/
theorem twoFactor_cycle_at [Finite V] (φ : G.EdgeLabeling C) (hφ : FullColoring φ)
    {a b : C} (hab : a ≠ b) (v : V) :
    ∃ p : (twoFactor φ a b).Walk v v, p.IsCycle ∧
      p.toSubgraph.verts = ((twoFactor φ a b).connectedComponentMk v).supp := by
  exact (twoFactor_isCycles φ hφ hab).exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
    rfl (twoFactor_neighborSet_nonempty φ hφ a b v)

/-- Every component, including those selected for a swap, has a faithful cycle witness. -/
theorem twoFactor_component_cycle [Finite V] (φ : G.EdgeLabeling C) (hφ : FullColoring φ)
    {a b : C} (hab : a ≠ b) (D : (twoFactor φ a b).ConnectedComponent) :
    ∃ (v : V) (p : (twoFactor φ a b).Walk v v), p.IsCycle ∧ p.toSubgraph.verts = D.supp := by
  obtain ⟨v, hv⟩ := D.nonempty_supp
  obtain ⟨p, hp, hS⟩ :=
    (twoFactor_isCycles φ hφ hab).exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
      hv (twoFactor_neighborSet_nonempty φ hφ a b v)
  exact ⟨v, p, hp, hS⟩

section Palette

variable [DecidableEq C]

/-- An explicit set of original colors containing any resulting two-color factor. -/
def canonicalPalette (a b i j : C) : Finset C :=
  if i = a ∨ i = b then {a, b, j}
  else if j = a ∨ j = b then {a, b, i}
  else {i, j}

theorem canonicalPalette_card_le (a b i j : C) : (canonicalPalette a b i j).card ≤ 3 := by
  unfold canonicalPalette
  split_ifs
  · exact Finset.card_le_three
  · exact Finset.card_le_three
  · exact le_trans Finset.card_le_two (by decide)

theorem canonicalPalette_contains (a b i j : C) :
    i ∈ canonicalPalette a b i j ∧ j ∈ canonicalPalette a b i j ∧
      Equiv.swap a b i ∈ canonicalPalette a b i j ∧
      Equiv.swap a b j ∈ canonicalPalette a b i j := by
  unfold canonicalPalette
  split_ifs <;> simp_all [Equiv.swap_apply_def] <;> aesop

theorem canonicalPalette_nonempty (a b i j : C) : (canonicalPalette a b i j).Nonempty :=
  ⟨i, (canonicalPalette_contains a b i j).1⟩

theorem labelGraph_swap_le_colorSubgraph_of_mem (φ : G.EdgeLabeling C) (a b : C)
    (J : Set (twoFactor φ a b).ConnectedComponent) (T : Finset C) {c : C}
    (hc : c ∈ T) (hsc : Equiv.swap a b c ∈ T) :
    (swap φ a b J).labelGraph c ≤ colorSubgraph φ T := by
  classical
  intro u v huv
  obtain ⟨h, hcolor⟩ := (EdgeLabeling.labelGraph_adj u v).mp huv
  change (swap φ a b J).get u v h = c at hcolor
  have hmem : φ.get u v h ∈ T := by
    rw [swap_get] at hcolor
    split_ifs at hcolor
    · rw [Equiv.swap_apply_eq_iff] at hcolor
      rw [hcolor]
      exact hsc
    · rw [hcolor]
      exact hc
  exact (colorSubgraph_adj φ T u v).mpr
    ⟨φ.get u v h, hmem, (EdgeLabeling.labelGraph_adj u v).mpr ⟨h, rfl⟩⟩

/-- Every actual edge of the new factor has one of at most three original colors. -/
theorem twoFactor_swap_le_colorSubgraph (φ : G.EdgeLabeling C) (a b : C)
    (J : Set (twoFactor φ a b).ConnectedComponent) (i j : C) :
    twoFactor (swap φ a b J) i j ≤ colorSubgraph φ (canonicalPalette a b i j) := by
  obtain ⟨hi, hj, hsi, hsj⟩ := canonicalPalette_contains a b i j
  exact sup_le
    (labelGraph_swap_le_colorSubgraph_of_mem φ a b J _ hi hsi)
    (labelGraph_swap_le_colorSubgraph_of_mem φ a b J _ hj hsj)

theorem swap_factor_palette (φ : G.EdgeLabeling C) (a b : C)
    (J : Set (twoFactor φ a b).ConnectedComponent) (i j : C) :
    ∃ T : Finset C, T.Nonempty ∧ T.card ≤ 3 ∧
      twoFactor (swap φ a b J) i j ≤ colorSubgraph φ T :=
  ⟨canonicalPalette a b i j, canonicalPalette_nonempty a b i j,
    canonicalPalette_card_le a b i j, twoFactor_swap_le_colorSubgraph φ a b J i j⟩

/-- Legality and actual component cycles hold for every selected component union. -/
theorem swap_twoFactor_component_cycle [Finite V] (φ : G.EdgeLabeling C)
    (hφ : FullColoring φ) (a b : C) (J : Set (twoFactor φ a b).ConnectedComponent)
    {i j : C} (hij : i ≠ j) (D : (twoFactor (swap φ a b J) i j).ConnectedComponent) :
    ∃ (v : V) (p : (twoFactor (swap φ a b J) i j).Walk v v),
      p.IsCycle ∧ p.toSubgraph.verts = D.supp :=
  twoFactor_component_cycle (swap φ a b J) (swap_fullColoring φ hφ a b J) hij D

end Palette

end Erdos585.KempeSwap104
