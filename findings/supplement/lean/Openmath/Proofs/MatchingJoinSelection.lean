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
import Openmath.Proofs.MatchingJoinDefs

/-!
# Terminal selection for an arbitrary matching between two quintic seeds

At least twenty of the twenty-six terminals map to terminals. The two-by-two
half matrix has opposite cells of size at least three. Three Boolean subtype
vectors contain two comparable vectors, giving the admitted ordered states
simultaneously in the source and target halves.
-/

open Finset

namespace Erdos585.MatchingJoin

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

private def localIndex (x : Fin 32) : Fin 16 := ⟨x.val % 16, Nat.mod_lt _ (by decide)⟩

private def side (x : Fin 32) : Bool := decide (16 ≤ x.val)

private def terminals : Finset (Fin 32) :=
  univ.filter fun x => localIndex x ∈ A ∪ D

private def kind (x : Fin 32) : Bool := decide (localIndex x ∈ D)

private lemma reconstruct : ∀ x : Fin 32, embed (side x) (localIndex x) = x := by
  decide

private lemma terminals_card : terminals.card = 26 := by decide

private lemma missing_card : (univ \ terminals).card = 6 := by decide

private lemma half_card : ∀ s : Bool, (terminals.filter fun x => side x = s).card = 13 := by
  decide

private lemma admitted_of_dominance : ∀ x y : Fin 32,
    x ∈ terminals → y ∈ terminals → side x = side y → x ≠ y →
    (kind y = true → kind x = true) → Admitted (localIndex x) (localIndex y) := by
  decide

private def good (f : Equiv.Perm (Fin 32)) : Finset (Fin 32) :=
  terminals.filter fun x => f x ∈ terminals

private def row (f : Equiv.Perm (Fin 32)) (s : Bool) : Finset (Fin 32) :=
  (good f).filter fun x => side x = s

private def col (f : Equiv.Perm (Fin 32)) (t : Bool) : Finset (Fin 32) :=
  (good f).filter fun x => side (f x) = t

private def cell (f : Equiv.Perm (Fin 32)) (s t : Bool) : Finset (Fin 32) :=
  (row f s).filter fun x => side (f x) = t

private lemma split_card {α : Type*} [DecidableEq α] (S : Finset α) (p : α → Bool) :
    (S.filter fun x => p x = false).card +
      (S.filter fun x => p x = true).card = S.card := by
  simpa using S.card_filter_add_card_filter_not (fun x => p x = false)

private lemma good_card (f : Equiv.Perm (Fin 32)) : 20 ≤ (good f).card := by
  let bad := terminals.filter fun x => f x ∉ terminals
  have hs : (good f).card + bad.card = 26 := by
    simpa [good, bad, terminals_card] using
      terminals.card_filter_add_card_filter_not (fun x => f x ∈ terminals)
  have hsub : bad.image f ⊆ univ \ terminals := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hy
    exact mem_sdiff.mpr ⟨mem_univ _, (mem_filter.mp hx).2⟩
  have hc := card_le_card hsub
  rw [card_image_of_injective _ f.injective, missing_card] at hc
  omega

private lemma row_card_le (f : Equiv.Perm (Fin 32)) (s : Bool) :
    (row f s).card ≤ 13 := by
  have hsub : row f s ⊆ terminals.filter (fun x => side x = s) := by
    intro x hx
    rcases mem_filter.mp hx with ⟨hx, hs⟩
    exact mem_filter.mpr ⟨(mem_filter.mp hx).1, hs⟩
  simpa [half_card] using card_le_card hsub

private lemma col_card_le (f : Equiv.Perm (Fin 32)) (t : Bool) :
    (col f t).card ≤ 13 := by
  have hsub : (col f t).image f ⊆ terminals.filter (fun x => side x = t) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hy
    rcases mem_filter.mp hx with ⟨hx, ht⟩
    exact mem_filter.mpr ⟨(mem_filter.mp hx).2, ht⟩
  have hc := card_le_card hsub
  simpa [card_image_of_injective _ f.injective, half_card] using hc

private lemma rows_split (f : Equiv.Perm (Fin 32)) :
    (row f false).card + (row f true).card = (good f).card :=
  split_card (good f) side

private lemma cols_split (f : Equiv.Perm (Fin 32)) :
    (col f false).card + (col f true).card = (good f).card :=
  split_card (good f) (fun x => side (f x))

private lemma cells_row (f : Equiv.Perm (Fin 32)) (s : Bool) :
    (cell f s false).card + (cell f s true).card = (row f s).card :=
  split_card (row f s) (fun x => side (f x))

private lemma cell_transpose (f : Equiv.Perm (Fin 32)) (s t : Bool) :
    cell f s t = (col f t).filter (fun x => side x = s) := by
  ext x
  simp only [cell, row, col, mem_filter]
  tauto

private lemma cells_col (f : Equiv.Perm (Fin 32)) (t : Bool) :
    (cell f false t).card + (cell f true t).card = (col f t).card := by
  rw [cell_transpose, cell_transpose]
  exact split_card (col f t) side

private lemma opposite_cells (f : Equiv.Perm (Fin 32)) :
    ∃ s : Bool, 3 ≤ (cell f false s).card ∧ 3 ≤ (cell f true (!s)).card := by
  have hg := good_card f
  have hr := rows_split f
  have hc := cols_split f
  have hr0 := row_card_le f false
  have hr1 := row_card_le f true
  have hc0 := col_card_le f false
  have hc1 := col_card_le f true
  have ha := cells_row f false
  have hb := cells_row f true
  have hd := cells_col f false
  have he := cells_col f true
  by_cases h00 : 3 ≤ (cell f false false).card
  · by_cases h11 : 3 ≤ (cell f true true).card
    · exact ⟨false, h00, h11⟩
    · exact ⟨true, by omega, by simp only [Bool.not_true]; omega⟩
  · exact ⟨true, by omega, by simp only [Bool.not_true]; omega⟩

private def dominates (x y : Bool × Bool) : Prop :=
  (y.1 = true → x.1 = true) ∧ (y.2 = true → x.2 = true)

private lemma three_vectors : ∀ a b c : Bool × Bool,
    dominates a b ∨ dominates b a ∨ dominates a c ∨
      dominates c a ∨ dominates b c ∨ dominates c b := by
  unfold dominates
  decide

private lemma cell_pair (f : Equiv.Perm (Fin 32)) (s t : Bool)
    (hcard : 3 ≤ (cell f s t).card) :
    ∃ x y : Fin 32, x ∈ cell f s t ∧ y ∈ cell f s t ∧
      Admitted (localIndex x) (localIndex y) ∧
      Admitted (localIndex (f x)) (localIndex (f y)) := by
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ :=
    two_lt_card_iff.mp (show 2 < (cell f s t).card by omega)
  have choose : ∀ x y, x ∈ cell f s t → y ∈ cell f s t → x ≠ y →
      dominates (kind x, kind (f x)) (kind y, kind (f y)) →
      ∃ x y : Fin 32, x ∈ cell f s t ∧ y ∈ cell f s t ∧
        Admitted (localIndex x) (localIndex y) ∧
        Admitted (localIndex (f x)) (localIndex (f y)) := by
    intro x y hx hy hne hdom
    have hx' : x ∈ terminals ∧ f x ∈ terminals ∧ side x = s ∧ side (f x) = t := by
      simpa [cell, row, good, and_assoc] using hx
    have hy' : y ∈ terminals ∧ f y ∈ terminals ∧ side y = s ∧ side (f y) = t := by
      simpa [cell, row, good, and_assoc] using hy
    refine ⟨x, y, hx, hy, ?_, ?_⟩
    · exact admitted_of_dominance x y hx'.1 hy'.1
        (hx'.2.2.1.trans hy'.2.2.1.symm) hne hdom.1
    · exact admitted_of_dominance (f x) (f y) hx'.2.1 hy'.2.1
        (hx'.2.2.2.trans hy'.2.2.2.symm) (f.injective.ne hne) hdom.2
  rcases three_vectors (kind a, kind (f a)) (kind b, kind (f b))
    (kind c, kind (f c)) with h | h | h | h | h | h
  · exact choose a b ha hb hab h
  · exact choose b a hb ha hab.symm h
  · exact choose a c ha hc hac h
  · exact choose c a hc ha hac.symm h
  · exact choose b c hb hc hbc h
  · exact choose c b hc hb hbc.symm h

/-- Every bijection admits four terminals with the actual half-path endpoint types
simultaneously in both copies of the seed. No graph/path hypothesis is assumed. -/
theorem selection_nonempty (f : Equiv.Perm (Fin 32)) : Nonempty (Selection f) := by
  obtain ⟨s, h0, h1⟩ := opposite_cells f
  obtain ⟨x0, y0, hx0, hy0, hxy0, hfx0⟩ := cell_pair f false s h0
  obtain ⟨x1, y1, hx1, hy1, hxy1, hfx1⟩ := cell_pair f true (!s) h1
  have eqs : ∀ x s t, x ∈ cell f s t →
      embed s (localIndex x) = x ∧ embed t (localIndex (f x)) = f x := by
    intro x s t hx
    have hx' : side x = s ∧ side (f x) = t := by
      simp only [cell, row, good, mem_filter] at hx
      tauto
    constructor
    · simpa [hx'.1] using reconstruct x
    · simpa [hx'.2] using reconstruct (f x)
  have ex0 := eqs x0 false s hx0
  have ey0 := eqs y0 false s hy0
  have ex1 := eqs x1 true (!s) hx1
  have ey1 := eqs y1 true (!s) hy1
  exact ⟨{
    x0 := localIndex x0, y0 := localIndex y0,
    x1 := localIndex x1, y1 := localIndex y1,
    a0 := localIndex (f x0), b0 := localIndex (f y0),
    a1 := localIndex (f x1), b1 := localIndex (f y1),
    s := s, h0 := hxy0, h1 := hxy1, k0 := hfx0, k1 := hfx1,
    fx0 := by rw [ex0.1, ex0.2],
    fy0 := by rw [ey0.1, ey0.2],
    fx1 := by rw [ex1.1, ex1.2],
    fy1 := by rw [ey1.1, ey1.2] }⟩

end Erdos585.MatchingJoin
