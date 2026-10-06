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

/-! # An actual six-cycle in every three-color abelian Haar graph

The complete argument is Paper83 Section9 and Paper85
HAAR-EXTRACTION-BOUNDARY.md. Three distinct colors give the six
vertices below, in every additive commutative group. This is a
scope obstruction for exact subgraph extraction, not an avoidance
counterexample or a new extremal lower bound.
-/

namespace Erdos585.HaarSixCycle
open SimpleGraph Finset

variable {V : Type*} [AddCommGroup V]

def cycle (S : Finset V) (s t u : V) (hs : s ∈ S) (ht : t ∈ S) (hu : u ∈ S) :
    (Haar.graph S).Walk (0, false) (0, false) :=
  .cons (v := (s, true)) (by simpa using hs)
    (.cons (v := (s-t, false)) (by
      apply SimpleGraph.Adj.symm
      rw [Haar.graph_cross]
      simpa using ht)
    (.cons (v := (s-t+u, true)) (by
      rw [Haar.graph_cross]
      simpa using hu)
    (.cons (v := (u-t, false)) (by
      apply SimpleGraph.Adj.symm
      rw [Haar.graph_cross]
      have he : s-t+u-(u-t) = s := by abel
      simpa only [he] using hs)
    (.cons (v := (u, true)) (by
      rw [Haar.graph_cross]
      simpa using ht)
    (.cons (by
      apply SimpleGraph.Adj.symm
      rw [Haar.graph_cross]
      simpa using hu) .nil)))))

@[simp] theorem cycle_length (S : Finset V) (s t u : V)
    (hs : s ∈ S) (ht : t ∈ S) (hu : u ∈ S) :
    (cycle S s t u hs ht hu).length = 6 := rfl

theorem cycle_isCycle (S : Finset V) (s t u : V)
    (hs : s ∈ S) (ht : t ∈ S) (hu : u ∈ S)
    (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u) :
    (cycle S s t u hs ht hu).IsCycle := by
  rw [Walk.isCycle_iff_isPath_tail_and_le_length]
  constructor
  · rw [Walk.isPath_def]
    have hst0 : s-t ≠ 0 := sub_ne_zero.mpr hst
    have hut0 : u-t ≠ 0 := sub_ne_zero.mpr htu.symm
    have hsu' : s-t+u ≠ s := by
      intro h
      apply hut0
      have he : s-t+u-s = u-t := by abel
      rw [h, sub_self] at he
      exact he.symm
    simp [cycle, hsu, hst0, hut0, hsu'.symm]
  · simp

/-- The witness is an actual simple-cycle walk, not just an incidence pattern. -/
theorem exists_six_cycle (S : Finset V) (hcard : 3 ≤ S.card) :
    ∃ q : (Haar.graph S).Walk (0, false) (0, false), q.IsCycle ∧ q.length = 6 := by
  obtain ⟨g, hg⟩ := Function.Embedding.exists_of_card_le_finset
    (α := Fin 3) (by simpa using hcard)
  have hm : ∀ i, g i ∈ S := fun i => hg ⟨i, rfl⟩
  refine ⟨cycle S (g 0) (g 1) (g 2) (hm 0) (hm 1) (hm 2), ?_, rfl⟩
  exact cycle_isCycle S _ _ _ _ _ _
    (g.injective.ne (by decide)) (g.injective.ne (by decide)) (g.injective.ne (by decide))

end Erdos585.HaarSixCycle
