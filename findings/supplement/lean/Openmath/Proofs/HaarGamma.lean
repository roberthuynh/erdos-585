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
import Openmath.Proofs.HaarClassification
import Openmath.Proofs.HaarDegree

/-! # Actual forest certificates for prime-field Haar graphs

A single uniform law on at most three actual color matchings meets
every bipartite simple cycle in at least four thirds. The affine-rank
classification supplies the color bound for every avoiding member of
the prime-field Haar class.
-/

noncomputable section
namespace Erdos585.HaarGamma
open SimpleGraph Finset

variable {V : Type*} [AddCommGroup V] [DecidableEq V]

/-- The explicit uniform forest law when the color count is at most three. -/
theorem certificate_of_card_le_three (S : Finset V) (hne : S.Nonempty)
    (hcard : S.card ≤ 3) :
    ∃ w : S → ℝ, (∀ s, 0 ≤ w s) ∧ (∑ s, w s) = 1 ∧
      (∀ s : S, Haar.graph {s.val} ≤ Haar.graph S ∧
        (Haar.graph {s.val}).IsAcyclic) ∧
      ∀ (a : V × Bool) (q : (Haar.graph S).Walk a a), q.IsCycle →
        (4 : ℝ) / 3 ≤ ∑ s : S, w s *
          (CubelikeForest.intersectionCount q (Haar.graph {s.val}) : ℝ) := by
  apply CubelikeForest.forest_cover_certificate
  · simpa using hne.card_pos
  · simpa using hcard
  · intro s
    exact Haar.graph_mono (singleton_subset_iff.mpr s.property)
  · intro s
    exact Haar.singleton_acyclic s.val
  · intro e
    refine Sym2.inductionOn e ?_
    intro x y hxy
    change (Haar.graph S).Adj x y at hxy
    rcases hxy with hxy | hxy
    · refine ⟨⟨y.1 - x.1, hxy.2.2⟩, ?_⟩
      change (Haar.graph {y.1 - x.1}).Adj x y
      exact Or.inl ⟨hxy.1, hxy.2.1, mem_singleton_self _⟩
    · refine ⟨⟨x.1 - y.1, hxy.2.2⟩, ?_⟩
      change (Haar.graph {x.1 - y.1}).Adj x y
      exact Or.inr ⟨hxy.1, hxy.2.1, mem_singleton_self _⟩
  · exact Haar.graph_bipartite S

omit [DecidableEq V] in
lemma nonempty_colors_of_cycle (S : Finset V) {a : V × Bool}
    (q : (Haar.graph S).Walk a a) (hq : q.IsCycle) : S.Nonempty := by
  cases q with
  | nil => exact (hq.not_nil Walk.Nil.nil).elim
  | cons h q =>
    rcases h with h | h <;> exact ⟨_, h.2.2⟩

variable {p : ℕ} [Fact p.Prime] [Module (ZMod p) V]
include p

/-- In a finite prime-field Haar graph, the faithful pair occurs exactly from four colors. -/
theorem hasPair_iff [Fintype V] (S : Finset V) :
    HasTwoEdgeDisjointCyclesSameVertexSet (Haar.graph S) ↔ 4 ≤ S.card := by
  constructor
  · intro h
    exact HaarDegree.four_le_card_of_pair S ((hasPairF_iff _).2 h)
  · intro h
    exact (hasPairF_iff _).1 (HaarClassification.hasPair_of_four (p := p) S h)

/-- Avoidance forces at most three colors in the whole prime-field Haar class. -/
theorem card_le_three_of_avoiding (S : Finset V)
    (ha : ¬ HasTwoEdgeDisjointCyclesSameVertexSet (Haar.graph S)) : S.card ≤ 3 := by
  by_contra hn
  exact ha ((hasPairF_iff _).1
    (HaarClassification.hasPair_of_four (p := p) S (by omega)))

/-- One explicit forest law certifies the whole avoiding Haar class. -/
theorem forest_certificate (S : Finset V) (hne : S.Nonempty)
    (ha : ¬ HasTwoEdgeDisjointCyclesSameVertexSet (Haar.graph S)) :
    ∃ w : S → ℝ, (∀ s, 0 ≤ w s) ∧ (∑ s, w s) = 1 ∧
      (∀ s : S, Haar.graph {s.val} ≤ Haar.graph S ∧
        (Haar.graph {s.val}).IsAcyclic) ∧
      ∀ (a : V × Bool) (q : (Haar.graph S).Walk a a), q.IsCycle →
        (4 : ℝ) / 3 ≤ ∑ s : S, w s *
          (CubelikeForest.intersectionCount q (Haar.graph {s.val}) : ℝ) :=
  certificate_of_card_le_three S hne (card_le_three_of_avoiding (p := p) S ha)

/-- The cycle-law formulation of R-Gamma with the explicit constant four thirds.
The degree restriction is derived from avoidance, and every atom is an actual cycle. -/
theorem regular_gamma_haar (S : Finset V)
    (ha : ¬ HasTwoEdgeDisjointCyclesSameVertexSet (Haar.graph S))
    {J : Type*} [Fintype J] (base : J → V × Bool)
    (q : ∀ j, (Haar.graph S).Walk (base j) (base j))
    (hq : ∀ j, (q j).IsCycle) (lam : J → ℝ)
    (hlam : ∀ j, 0 ≤ lam j) (hlamsum : ∑ j, lam j = 1) :
    ∃ F : SimpleGraph (V × Bool), F ≤ Haar.graph S ∧ F.IsAcyclic ∧
      (4 : ℝ) / 3 ≤ ∑ j, lam j *
        (CubelikeForest.intersectionCount (q j) F : ℝ) := by
  have hJ : Nonempty J := by
    by_contra hn
    have : IsEmpty J := not_nonempty_iff.mp hn
    simp at hlamsum
  obtain ⟨j⟩ := hJ
  have hne := nonempty_colors_of_cycle S (q j) (hq j)
  obtain ⟨w, hw, hwsum, hF, hcert⟩ := forest_certificate (p := p) S hne ha
  exact CubelikeForest.cycle_law_forest_of_certificate
    (fun s : S => Haar.graph {s.val}) w hw hwsum hF (4 / 3) hcert
    base q hq lam hlam hlamsum

end Erdos585.HaarGamma
