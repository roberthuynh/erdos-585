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
import Openmath.Proofs.Haar

/-! # The uniform prime-field Haar construction in affine rank two

The four normalized colors are 0, (1,0), (0,1), and (a,b+1).
The hypotheses a ≠ 0 and (a,b+1) ≠ (1,0) state exactly the needed
transversality and remaining color distinctness. Two actual matching
unions have full successor orbits, derived here by skew shifts.
The final theorem supplies the original faithful actual-cycle predicate.
-/

namespace Erdos585.HaarRankTwo
open Equiv Equiv.Perm Finset HaarWitness

variable {p : ℕ} [Fact p.Prime]

abbrev Vertex (p : ℕ) := ZMod p × ZMod p

def colors (a b : ZMod p) : Finset (Vertex p) :=
  {0, (1, 0), (0, 1), (a, b + 1)}

theorem colors_card (a b : ZMod p) (ha : a ≠ 0) (hdup : (a, b + 1) ≠ (1, 0)) :
    (colors a b).card = 4 := by
  have h₀ : (0 : Vertex p) ≠ (a, b + 1) := by
    intro h
    exact ha (congrArg Prod.fst h).symm
  have hw : (0, (1 : ZMod p)) ≠ (a, b + 1) := by
    intro h
    exact ha (congrArg Prod.fst h).symm
  simp [colors, card_insert_eq_ite, h₀, hdup.symm, hw]
  simp [Prod.ext_iff]

/-- An invertible vertical shear, with the horizontal coordinate fixed. -/
def vertical (f : ZMod p → ZMod p) : Perm (Vertex p) where
  toFun x := (x.1, x.2 + f x.1)
  invFun x := (x.1, x.2 - f x.1)
  left_inv x := by ext <;> simp
  right_inv x := by ext <;> simp

def redMove : Perm (Vertex p) := Equiv.addRight (1, 0)
def redOther : Perm (Vertex p) := vertical (fun x => if x = 0 then 1 else 0)
def blueMove (a b : ZMod p) : Perm (Vertex p) := Equiv.addRight (a, b + 1)
def blueOther : Perm (Vertex p) := vertical (fun x => if x = 0 then 0 else 1)

theorem red_successor :
    redOther⁻¹ * redMove = skew (redInc (p := p) 0) := by
  ext x : 1
  change (x.1 + 1, x.2 + 0 - (if x.1 + 1 = 0 then 1 else 0)) =
    (x.1 + 1, x.2 + redInc 0 x.1)
  have hg : (x.1 = 0 - 1) ↔ x.1 + 1 = 0 := eq_sub_iff_add_eq
  simp only [redInc, hg, add_zero]
  split_ifs <;> simp [sub_eq_add_neg]

theorem red_orbit :
    (redOther⁻¹ * redMove (p := p)).IsCycleOn Set.univ := by
  rw [red_successor]
  exact skew_isCycleOn _ (by simp)

/-- Normalize a nonzero horizontal step to one. -/
def scale (a : ZMod p) (ha : a ≠ 0) : Perm (Vertex p) where
  toFun x := (a * x.1, x.2)
  invFun x := (x.1 / a, x.2)
  left_inv x := by ext <;> simp [ha]
  right_inv x := by ext <;> field_simp

def blueInc (b x : ZMod p) : ZMod p := b + if x = -1 then 1 else 0

@[simp] theorem sum_blueInc (b : ZMod p) : ∑ x, blueInc b x = 1 := by
  simp [blueInc, sum_add_distrib, ZMod.card]

theorem blue_successor (a b : ZMod p) (ha : a ≠ 0) :
    blueOther⁻¹ * blueMove a b = scale a ha * skew (blueInc b) * (scale a ha)⁻¹ := by
  ext x : 1
  change (x.1 + a, x.2 + (b + 1) - (if x.1 + a = 0 then 0 else 1)) =
    (a * (x.1 / a + 1), x.2 + blueInc b (x.1 / a))
  have hg : x.1 / a = -1 ↔ x.1 + a = 0 := by
    rw [div_eq_iff ha]
    constructor <;> intro h <;> linear_combination h
  have hfirst : a * (x.1 / a + 1) = x.1 + a := by field_simp
  rw [hfirst]
  simp only [blueInc, hg]
  split_ifs <;> simp
  ring

theorem blue_orbit (a b : ZMod p) (ha : a ≠ 0) :
    (blueOther⁻¹ * blueMove a b).IsCycleOn Set.univ := by
  rw [blue_successor a b ha]
  have h := (skew_isCycleOn (blueInc b) (by simp)).conj (g := scale a ha)
  simpa using h

theorem redMove_adj (a b : ZMod p) (x : Vertex p) :
    (Haar.graph (colors a b)).Adj (x, false) (redMove x, true) := by
  rw [Haar.graph_cross]
  change x + (1, 0) - x ∈ colors a b
  simp [colors]

theorem blueMove_adj (a b : ZMod p) (x : Vertex p) :
    (Haar.graph (colors a b)).Adj (x, false) (blueMove a b x, true) := by
  rw [Haar.graph_cross]
  change x + (a, b + 1) - x ∈ colors a b
  simp [colors]

theorem redOther_adj (a b : ZMod p) (x : Vertex p) :
    (Haar.graph (colors a b)).Adj (x, false) (redOther x, true) := by
  rw [Haar.graph_cross]
  by_cases hx : x.1 = 0 <;> simp [redOther, vertical, hx, colors, Prod.sub_def]

theorem blueOther_adj (a b : ZMod p) (x : Vertex p) :
    (Haar.graph (colors a b)).Adj (x, false) (blueOther x, true) := by
  rw [Haar.graph_cross]
  by_cases hx : x.1 = 0 <;> simp [blueOther, vertical, hx, colors, Prod.sub_def]

theorem vertical_ne_redMove (f : ZMod p → ZMod p) (x : Vertex p) :
    vertical f x ≠ redMove x := by
  intro h
  have hh := congrArg Prod.fst h
  simp [vertical, redMove] at hh

theorem vertical_ne_blueMove (f : ZMod p → ZMod p) (a b : ZMod p)
    (ha : a ≠ 0) (x : Vertex p) : vertical f x ≠ blueMove a b x := by
  intro h
  have hh := congrArg Prod.fst h
  simp [vertical, blueMove, ha] at hh

theorem redMove_ne_blueMove (a b : ZMod p) (hdup : (a, b + 1) ≠ (1, 0))
    (x : Vertex p) : redMove x ≠ blueMove a b x := by
  intro h
  change x + (1, 0) = x + (a, b + 1) at h
  exact hdup (add_left_cancel h).symm

theorem redOther_ne_blueOther (x : Vertex p) : redOther x ≠ blueOther x := by
  intro h
  have hh := congrArg Prod.snd h
  by_cases hx : x.1 = 0 <;> simp [redOther, blueOther, vertical, hx] at hh

/-- The normalized rank-two Haar graph has a faithful pair for every prime. -/
theorem hasPair (a b : ZMod p) (ha : a ≠ 0) (hdup : (a, b + 1) ≠ (1, 0)) :
    HasPairF (Haar.graph (colors a b)) := by
  apply HaarPair.hasPair_of_matching_permutations _ redMove redOther (blueMove a b) blueOther
    (redMove_adj a b) (redOther_adj a b) (blueMove_adj a b) (blueOther_adj a b)
  · intro x
    exact (vertical_ne_redMove _ x).symm
  · intro x
    exact (vertical_ne_blueMove _ a b ha x).symm
  · intro x
    exact ⟨redMove_ne_blueMove a b hdup x, (vertical_ne_redMove _ x).symm,
      vertical_ne_blueMove _ a b ha x, redOther_ne_blueOther x⟩
  · exact red_orbit
  · exact blue_orbit a b ha
  · exact 0

end Erdos585.HaarRankTwo
