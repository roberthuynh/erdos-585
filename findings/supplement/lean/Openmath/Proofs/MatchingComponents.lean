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
import Openmath.Proofs.HaarPair

/-! # Actual components of a bipartite matching factor -/

namespace Erdos585.MatchingComponents

open SimpleGraph Equiv Equiv.Perm

variable {V : Type*}

def label (f : Perm V) (v : V × Bool) : V :=
  if v.2 then f.symm v.1 else v.1

private lemma cross_labels (f g : Perm V) (x y : V)
    (h : (HaarPair.matchingFactor f g).Adj (x, false) (y, true)) :
    (g⁻¹ * f).SameCycle x (f.symm y) := by
  rcases (HaarPair.factor_cross f g x y).mp h with rfl | rfl
  · simpa only [symm_apply_apply] using (SameCycle.refl (g⁻¹ * f) x)
  · have hh := (SameCycle.refl (g⁻¹ * f) x).symm_apply_right
    have he : (g⁻¹ * f).symm x = f.symm (g x) := rfl
    rw [he] at hh
    exact hh

lemma sameCycle_of_adj (f g : Perm V) {u v : V × Bool}
    (h : (HaarPair.matchingFactor f g).Adj u v) :
    (g⁻¹ * f).SameCycle (label f u) (label f v) := by
  obtain ⟨x, bx⟩ := u
  obtain ⟨y, by_⟩ := v
  cases bx <;> cases by_
  · exact (HaarPair.factor_same f g x y false h).elim
  · exact cross_labels f g x y h
  · exact (cross_labels f g y x h.symm).symm
  · exact (HaarPair.factor_same f g x y true h).elim

theorem sameCycle_of_reachable (f g : Perm V) {u v : V × Bool}
    (h : (HaarPair.matchingFactor f g).Reachable u v) :
    (g⁻¹ * f).SameCycle (label f u) (label f v) := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact SameCycle.rfl
  | cons h p ih => exact (sameCycle_of_adj f g h).trans ih

private lemma successor_reachable (f g : Perm V) (x : V) :
    (HaarPair.matchingFactor f g).Reachable (x, false) ((g⁻¹ * f) x, false) := by
  have h₁ : (HaarPair.matchingFactor f g).Adj (x, false) (f x, true) :=
    (HaarPair.factor_cross f g x (f x)).mpr (Or.inl rfl)
  have h₂ : (HaarPair.matchingFactor f g).Adj ((g⁻¹ * f) x, false) (f x, true) := by
    apply (HaarPair.factor_cross f g _ _).mpr
    exact Or.inr (by simp [mul_apply])
  exact h₁.reachable.trans h₂.symm.reachable

theorem left_reachable_of_sameCycle [Finite V] (f g : Perm V) {a c : V}
    (h : (g⁻¹ * f).SameCycle a c) :
    (HaarPair.matchingFactor f g).Reachable (a, false) (c, false) := by
  obtain ⟨N, rfl⟩ := h.exists_nat_pow_eq
  clear h
  induction N with
  | zero => simp
  | succ N ih =>
    have hs := successor_reachable f g (((g⁻¹ * f) ^ N) a)
    simpa [pow_succ', mul_apply] using ih.trans hs

private lemma to_label (f g : Perm V) (v : V × Bool) :
    (HaarPair.matchingFactor f g).Reachable v (label f v, false) := by
  obtain ⟨x, bx⟩ := v
  cases bx
  · exact Reachable.rfl
  · have hh : (HaarPair.matchingFactor f g).Adj (f.symm x, false) (x, true) := by
      apply (HaarPair.factor_cross f g _ _).mpr
      exact Or.inl (by simp)
    exact hh.symm.reachable

theorem reachable_iff_sameCycle [Finite V] (f g : Perm V) (u v : V × Bool) :
    (HaarPair.matchingFactor f g).Reachable u v ↔
      (g⁻¹ * f).SameCycle (label f u) (label f v) := by
  refine ⟨sameCycle_of_reachable f g, ?_⟩
  intro h
  exact (to_label f g u).trans
    ((left_reachable_of_sameCycle f g h).trans (to_label f g v).symm)

end Erdos585.MatchingComponents
