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
import Openmath.Proofs.SmallExact
import Mathlib.Data.Nat.Bitwise

/-!
# Faithful pairs in the four-cube and its antipodal quotient

The explicit walks are the saved Paper65 witnesses. Adjacency is defined
on binary masks, independently of the walks. Injective adjacency-preserving
maps transport each witness to an arbitrary graph.
-/

open SimpleGraph Finset

namespace Erdos585.CubelikeWitness

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The population count of the four low bits of a natural-number mask. -/
def weight4 (n : ℕ) : ℕ := (BitVec.ofNat 4 n).cpop.toNat

/-- Binary four-cube: two masks are adjacent when their XOR has one set bit. -/
def q4 : SimpleGraph (Fin 16) where
  Adj a b := Nat.xor a.val b.val ∈ ({1, 2, 4, 8} : Finset ℕ)
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩

instance : DecidableRel q4.Adj := fun a b =>
  inferInstanceAs (Decidable (Nat.xor a.val b.val ∈ ({1, 2, 4, 8} : Finset ℕ)))

/-- The generator definition is exactly population-count-one adjacency. -/
theorem q4_adj_iff_weight (a b : Fin 16) : q4.Adj a b ↔
    weight4 (Nat.xor a.val b.val) = 1 := by
  revert a b
  decide

/-- The four generators of the four-cube, with no truncation ambiguity. -/
theorem q4_adj_iff (a b : Fin 16) : q4.Adj a b ↔
    Nat.xor a.val b.val = 1 ∨ Nat.xor a.val b.val = 2 ∨
    Nat.xor a.val b.val = 4 ∨ Nat.xor a.val b.val = 8 := by
  revert a b
  decide

/-- Representatives 0 through 7 for the quotient by the antipodal vector 1111. -/
def folded : SimpleGraph (Fin 8) where
  Adj a b := Nat.xor a.val b.val ∈ ({1, 2, 4, 7} : Finset ℕ)
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩

instance : DecidableRel folded.Adj := fun a b =>
  inferInstanceAs (Decidable (Nat.xor a.val b.val ∈ ({1, 2, 4, 7} : Finset ℕ)))

/-- This folded cube is the complete bipartite graph on the parity shores. -/
theorem folded_adj_iff_parity (a b : Fin 8) : folded.Adj a b ↔
    weight4 a.val % 2 ≠ weight4 b.val % 2 := by
  revert a b
  decide

/-- First Hamilton cycle of the four-cube. -/
def q4A : q4.Walk 0 0 :=
  .cons (v := 1) (by decide) (.cons (v := 3) (by decide)
    (.cons (v := 2) (by decide) (.cons (v := 6) (by decide)
    (.cons (v := 4) (by decide) (.cons (v := 5) (by decide)
    (.cons (v := 7) (by decide) (.cons (v := 15) (by decide)
    (.cons (v := 11) (by decide) (.cons (v := 9) (by decide)
    (.cons (v := 13) (by decide) (.cons (v := 12) (by decide)
    (.cons (v := 14) (by decide) (.cons (v := 10) (by decide)
    (.cons (v := 8) (by decide) (.cons (by decide) .nil)))))))))))))))

/-- The edge-disjoint second Hamilton cycle of the four-cube. -/
def q4B : q4.Walk 0 0 :=
  .cons (v := 2) (by decide) (.cons (v := 10) (by decide)
    (.cons (v := 11) (by decide) (.cons (v := 3) (by decide)
    (.cons (v := 7) (by decide) (.cons (v := 6) (by decide)
    (.cons (v := 14) (by decide) (.cons (v := 15) (by decide)
    (.cons (v := 13) (by decide) (.cons (v := 5) (by decide)
    (.cons (v := 1) (by decide) (.cons (v := 9) (by decide)
    (.cons (v := 8) (by decide) (.cons (v := 12) (by decide)
    (.cons (v := 4) (by decide) (.cons (by decide) .nil)))))))))))))))

/-- The first K₄,₄ witness in the folded-cube mask labeling. -/
def foldedA : folded.Walk 0 0 :=
  .cons (v := 1) (by decide) (.cons (v := 3) (by decide)
    (.cons (v := 2) (by decide) (.cons (v := 5) (by decide)
    (.cons (v := 4) (by decide) (.cons (v := 6) (by decide)
    (.cons (v := 7) (by decide) (.cons (by decide) .nil)))))))

/-- The second K₄,₄ witness in the folded-cube mask labeling. -/
def foldedB : folded.Walk 0 0 :=
  .cons (v := 2) (by decide) (.cons (v := 6) (by decide)
    (.cons (v := 1) (by decide) (.cons (v := 5) (by decide)
    (.cons (v := 7) (by decide) (.cons (v := 3) (by decide)
    (.cons (v := 4) (by decide) (.cons (by decide) .nil)))))))

theorem q4A_isCycle : q4A.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  exact ⟨by decide, by simp [q4A], by decide⟩

theorem q4B_isCycle : q4B.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  exact ⟨by decide, by simp [q4B], by decide⟩

theorem foldedA_isCycle : foldedA.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  exact ⟨by decide, by simp [foldedA], by decide⟩

theorem foldedB_isCycle : foldedB.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  exact ⟨by decide, by simp [foldedB], by decide⟩

theorem hasPair_q4 : HasPairF q4 :=
  ⟨0, 0, q4A, q4B, q4A_isCycle, q4B_isCycle, by decide, by decide⟩

theorem hasPair_folded : HasPairF folded :=
  ⟨0, 0, foldedA, foldedB, foldedA_isCycle, foldedB_isCycle, by decide, by decide⟩

/-- An injective adjacency-preserving realization of Q₄ contains the saved pair. -/
theorem hasPair_of_q4 {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (f : Fin 16 → V) (hf : Function.Injective f)
    (hadj : ∀ a b, q4.Adj a b → G.Adj (f a) (f b)) : HasPairF G :=
  hasPair_q4.map ⟨f, fun {a b} h => hadj a b h⟩ hf

/-- An injective realization of the folded cube contains the saved pair. -/
theorem hasPair_of_folded {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (f : Fin 8 → V) (hf : Function.Injective f)
    (hadj : ∀ a b, folded.Adj a b → G.Adj (f a) (f b)) : HasPairF G :=
  hasPair_folded.map ⟨f, fun {a b} h => hadj a b h⟩ hf

end Erdos585.CubelikeWitness
