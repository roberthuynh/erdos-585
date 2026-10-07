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

/-! # The actual degree of a finite Haar graph

The color-neighbor bijection proves regularity directly. Together with
the existing faithful-pair rigidity, it proves the converse direction
of the four-color classification described in Paper83, Section 8.
-/

namespace Erdos585.HaarDegree
open SimpleGraph Finset

variable {V : Type*} [AddCommGroup V] [DecidableEq V] [Fintype V]

theorem degree_false (S : Finset V) (x : V) :
    (Haar.graph S).degree (x, false) = S.card := by
  rw [← card_neighborFinset_eq_degree]
  symm
  apply Finset.card_bij (fun s _ => (x + s, true))
  · intro s hs
    simpa using hs
  · intro s hs t ht h
    exact add_left_cancel (congrArg Prod.fst h)
  · rintro ⟨y, b⟩ hy
    cases b
    · simp at hy
    · refine ⟨y - x, ?_, ?_⟩
      · simpa using hy
      · simp

theorem degree_true (S : Finset V) (x : V) :
    (Haar.graph S).degree (x, true) = S.card := by
  rw [← card_neighborFinset_eq_degree]
  symm
  apply Finset.card_bij (fun s _ => (x - s, false))
  · intro s hs
    apply (mem_neighborFinset _ _ _).2
    exact (Haar.graph_cross S _ _).2 (by simpa using hs) |>.symm
  · intro s hs t ht h
    exact sub_right_injective (congrArg Prod.fst h)
  · rintro ⟨y, b⟩ hy
    cases b
    · have hy' : (Haar.graph S).Adj (y, false) (x, true) :=
        (mem_neighborFinset _ _ _).1 hy |>.symm
      refine ⟨x - y, (Haar.graph_cross S _ _).1 hy', ?_⟩
      simp
    · simp at hy

/-- Every vertex has exactly one distinct neighbor for every color. -/
theorem degree_eq_card (S : Finset V) (x : V × Bool) :
    (Haar.graph S).degree x = S.card := by
  obtain ⟨x, b⟩ := x
  cases b
  · exact degree_false S x
  · exact degree_true S x

/-- The low-degree converse needs no prime-field or symmetry assumption. -/
theorem four_le_card_of_pair (S : Finset V) (h : HasPairF (Haar.graph S)) :
    4 ≤ S.card := by
  obtain ⟨u, v, q, t, hq, ht, hS, hE⟩ := h
  have hd := four_le_degree_of_mem_pair hq ht hS hE q.start_mem_support
  simpa only [degree_eq_card] using hd

end Erdos585.HaarDegree
