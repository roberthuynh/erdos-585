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

/-! # Faithful pairs in prime-field Haar graphs of rank one

Two distinct translations have one full successor orbit. Four distinct
colors therefore split into two actual disjoint spanning cycles.
-/

namespace Erdos585.HaarRankOne

open Equiv Equiv.Perm Finset

variable {p : ℕ} [Fact p.Prime]

lemma translation_successor (a b : ZMod p) :
    ((Equiv.addRight b)⁻¹ * Equiv.addRight a : Perm (ZMod p)) =
      Equiv.addRight (a - b) := by
  ext x
  simp [sub_eq_add_neg, add_assoc]

lemma matching_adj (S : Finset (ZMod p)) (a : ZMod p) (ha : a ∈ S) (x : ZMod p) :
    (Haar.graph S).Adj (x, false) (Equiv.addRight a x, true) := by
  rw [Haar.graph_cross]
  simpa using ha

/-- Four distinct actual colors give a faithful pair, uniformly in the prime. -/
theorem hasPair_of_four_distinct (S : Finset (ZMod p)) (a b c d : ZMod p)
    (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hd : d ∈ S)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) : HasPairF (Haar.graph S) := by
  apply HaarPair.hasPair_of_matching_permutations _
    (Equiv.addRight a) (Equiv.addRight b) (Equiv.addRight c) (Equiv.addRight d)
    (matching_adj S a ha) (matching_adj S b hb)
    (matching_adj S c hc) (matching_adj S d hd)
  · intro x h
    exact hab (add_left_cancel h)
  · intro x h
    exact hcd (add_left_cancel h)
  · intro x
    exact ⟨fun h => hac (add_left_cancel h), fun h => had (add_left_cancel h),
      fun h => hbc (add_left_cancel h), fun h => hbd (add_left_cancel h)⟩
  · rw [translation_successor]
    exact HaarWitness.addRight_isCycleOn _ (sub_ne_zero.mpr hab)
  · rw [translation_successor]
    exact HaarWitness.addRight_isCycleOn _ (sub_ne_zero.mpr hcd)
  · exact 0

end Erdos585.HaarRankOne
