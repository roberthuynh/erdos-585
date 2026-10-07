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
import Mathlib.LinearAlgebra.Span.Basic

/-! # Actual Haar graph components over ZMod 3

An actual connected component of a Haar graph has one affine coset on
each shore. The converse is proved by concatenating actual two-edge walks
for color differences, including all scalar combinations over ZMod 3.
-/

namespace Erdos585.HaarComponents104

open SimpleGraph

variable {V : Type*} [AddCommGroup V] [Module (ZMod 3) V]

/-- The ZMod 3 span of all color differences from a fixed color. -/
def differenceSpan (S : Finset V) (a : V) : Submodule (ZMod 3) V :=
  Submodule.span (ZMod 3) ((fun s : V => s - a) '' (S : Set V))

theorem sub_mem_differenceSpan (S : Finset V) (a : V) {s : V} (hs : s ∈ S) :
    s - a ∈ differenceSpan S a :=
  Submodule.subset_span ⟨s, hs, rfl⟩

private theorem adj_offset_sub_mem (S : Finset V) (a : V)
    {u v : V × Bool} (h : (Haar.graph S).Adj u v) :
    (v.1 - (if v.2 then a else 0)) - (u.1 - (if u.2 then a else 0)) ∈
      differenceSpan S a := by
  rcases u with ⟨x, b⟩
  rcases v with ⟨y, c⟩
  cases b <;> cases c <;> simp only [Haar.graph, Bool.false_eq_true,
    Bool.true_eq_false, false_and, and_false, or_false, false_or, true_and,
    ite_false, ite_true, sub_zero] at h ⊢
  · have he : y - a - x = (y - x) - a := by abel
    rw [he]
    exact sub_mem_differenceSpan S a h
  · have he : y - (x - a) = -((x - y) - a) := by abel
    rw [he]
    exact (differenceSpan S a).neg_mem (sub_mem_differenceSpan S a h)

/-- Every actual reachable vertex lies in the appropriate shore coset. -/
theorem mem_differenceSpan_of_reachable (S : Finset V) (a X Y : V) (b : Bool)
    (h : (Haar.graph S).Reachable (X, false) (Y, b)) :
    Y - X - (if b then a else 0) ∈ differenceSpan S a := by
  have haux : ∀ {u v : V × Bool}, (Haar.graph S).Reachable u v →
      (v.1 - (if v.2 then a else 0)) - (u.1 - (if u.2 then a else 0)) ∈
        differenceSpan S a := by
    intro u v h
    rw [reachable_iff_reflTransGen] at h
    induction h with
    | refl => simp
    | @tail y z _ hyz ih =>
        have hm := (differenceSpan S a).add_mem ih (adj_offset_sub_mem S a hyz)
        convert hm using 1
        abel
  have hm := haux h
  simpa only [Bool.false_eq_true, ite_false, sub_zero,
    show Y - X - (if b then a else 0) = Y - (if b then a else 0) - X by abel]
    using hm

omit [Module (ZMod 3) V] in
private theorem reachable_add_generator (S : Finset V) {a : V} (ha : a ∈ S)
    {s : V} (hs : s ∈ S) (X : V) :
    (Haar.graph S).Reachable (X, false) (X + (s - a), false) := by
  have h₁ : (Haar.graph S).Adj (X, false) (X + s, true) := by
    rw [Haar.graph_cross]
    simpa using hs
  have h₂ : (Haar.graph S).Adj (X + (s - a), false) (X + s, true) := by
    rw [Haar.graph_cross]
    convert ha using 1
    abel
  exact h₁.reachable.trans h₂.symm.reachable

/-- Span membership supplies actual reachability on the left shore. -/
theorem reachable_add_of_mem_differenceSpan (S : Finset V) {a : V} (ha : a ∈ S)
    {d : V} (hd : d ∈ differenceSpan S a) (X : V) :
    (Haar.graph S).Reachable (X, false) (X + d, false) := by
  have haux : ∀ d ∈ differenceSpan S a, ∀ X : V,
      (Haar.graph S).Reachable (X, false) (X + d, false) := by
    intro d hd
    induction hd using Submodule.span_induction with
    | mem d hd =>
        rcases hd with ⟨s, hs, rfl⟩
        exact reachable_add_generator S ha hs
    | zero =>
        intro X
        simp
    | add d e _ _ hd he =>
        intro X
        simpa only [add_assoc] using (hd X).trans (he (X + d))
    | smul c d _ hd =>
        intro X
        fin_cases c
        · change (Haar.graph S).Reachable (X, false) (X + (0 : ZMod 3) • d, false)
          simp
        · change (Haar.graph S).Reachable (X, false) (X + (1 : ZMod 3) • d, false)
          simpa only [one_smul] using hd X
        · change (Haar.graph S).Reachable (X, false) (X + (2 : ZMod 3) • d, false)
          have htwo : (2 : ZMod 3) • d = d + d := by
            rw [show (2 : ZMod 3) = 1 + 1 by decide, add_smul, one_smul]
          simpa only [htwo, add_assoc] using (hd X).trans (hd (X + d))
  exact haux d hd X

/-- The actual connected component has exactly the two affine shore cosets. -/
theorem reachable_iff_mem_differenceSpan (S : Finset V) {a : V} (ha : a ∈ S)
    (X Y : V) (b : Bool) :
    (Haar.graph S).Reachable (X, false) (Y, b) ↔
      Y - X - (if b then a else 0) ∈ differenceSpan S a := by
  constructor
  · exact mem_differenceSpan_of_reachable S a X Y b
  · intro h
    cases b
    · simp only [Bool.false_eq_true, ite_false, sub_zero] at h
      have hr := reachable_add_of_mem_differenceSpan S ha h X
      simpa using hr
    · simp only [ite_true] at h
      have hr := reachable_add_of_mem_differenceSpan S ha h X
      have he : X + (Y - X - a) = Y - a := by abel
      rw [he] at hr
      have hadj : (Haar.graph S).Adj (Y - a, false) (Y, true) := by
        rw [Haar.graph_cross]
        simpa using ha
      exact hr.trans hadj.reachable

end Erdos585.HaarComponents104
