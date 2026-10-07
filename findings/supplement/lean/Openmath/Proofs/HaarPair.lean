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
import Openmath.Proofs.HaarCycle
import Openmath.Proofs.SmallExact

/-!
# Actual faithful pairs from two matching-successor cycles

This interface keeps the factors as actual subgraphs of the specified
host and proves support equality and edge disjointness of actual walks.
It does not supply the Haar coordinate identities or affine reductions.
-/

namespace Erdos585.HaarPair

open SimpleGraph Equiv Equiv.Perm

variable {V : Type*}

/-- The actual bipartite union of the two indicated matchings. -/
def matchingFactor (f g : Perm V) : SimpleGraph (V × Bool) :=
  .fromRel fun x y => x.2 = false ∧ y.2 = true ∧ (y.1 = f x.1 ∨ y.1 = g x.1)

lemma factor_cross (f g : Perm V) (x y : V) :
    (matchingFactor f g).Adj (x, false) (y, true) ↔ y = f x ∨ y = g x := by
  simp [matchingFactor, SimpleGraph.fromRel_adj]

lemma factor_same (f g : Perm V) (x y : V) (b : Bool) :
    ¬ (matchingFactor f g).Adj (x, b) (y, b) := by
  cases b <;> simp [matchingFactor, SimpleGraph.fromRel_adj]

lemma factor_le (G : SimpleGraph (V × Bool)) (f g : Perm V)
    (hf : ∀ x, G.Adj (x, false) (f x, true))
    (hg : ∀ x, G.Adj (x, false) (g x, true)) : matchingFactor f g ≤ G := by
  rintro ⟨x, bx⟩ ⟨y, by_⟩ h
  cases bx <;> cases by_
  · exact (factor_same f g x y false h).elim
  · rcases (factor_cross f g x y).mp h with h | h
    · simpa [h] using hf x
    · simpa [h] using hg x
  · rcases (factor_cross f g y x).mp h.symm with h | h
    · simpa [h] using (hf y).symm
    · simpa [h] using (hg y).symm
  · exact (factor_same f g x y true h).elim

lemma factors_edge_disjoint (f g h k : Perm V)
    (hdis : ∀ x, f x ≠ h x ∧ f x ≠ k x ∧ g x ≠ h x ∧ g x ≠ k x) :
    Disjoint (matchingFactor f g).edgeSet (matchingFactor h k).edgeSet := by
  apply Set.disjoint_left.mpr
  intro e he hf
  induction e using Sym2.inductionOn with
  | _ u v =>
    obtain ⟨x, bx⟩ := u
    obtain ⟨y, by_⟩ := v
    change (matchingFactor f g).Adj (x, bx) (y, by_) at he
    change (matchingFactor h k).Adj (x, bx) (y, by_) at hf
    cases bx <;> cases by_
    · exact factor_same f g x y false he
    · have hr := (factor_cross f g x y).mp he
      have hb := (factor_cross h k x y).mp hf
      have hd := hdis x
      aesop
    · have hr := (factor_cross f g y x).mp he.symm
      have hb := (factor_cross h k y x).mp hf.symm
      have hd := hdis y
      aesop
    · exact factor_same f g x y true he

/-- Four actual, disjoint matching edge sets whose two successor permutations
are full cycles give the original faithful forbidden pattern. -/
theorem hasPair_of_matching_permutations [Finite V] [DecidableEq V]
    (G : SimpleGraph (V × Bool)) (r₀ r₁ b₀ b₁ : Perm V)
    (hr₀ : ∀ x, G.Adj (x, false) (r₀ x, true))
    (hr₁ : ∀ x, G.Adj (x, false) (r₁ x, true))
    (hb₀ : ∀ x, G.Adj (x, false) (b₀ x, true))
    (hb₁ : ∀ x, G.Adj (x, false) (b₁ x, true))
    (hrne : ∀ x, r₀ x ≠ r₁ x) (hbne : ∀ x, b₀ x ≠ b₁ x)
    (hdis : ∀ x, r₀ x ≠ b₀ x ∧ r₀ x ≠ b₁ x ∧ r₁ x ≠ b₀ x ∧ r₁ x ≠ b₁ x)
    (hred : (r₁⁻¹ * r₀).IsCycleOn Set.univ)
    (hblue : (b₁⁻¹ * b₀).IsCycleOn Set.univ) (x₀ : V) : HasPairF G := by
  classical
  obtain ⟨p, hp, hps⟩ := HaarCycle.cycle_of_two_matchings (matchingFactor r₀ r₁)
    r₀ r₁ (factor_cross r₀ r₁) (factor_same r₀ r₁) hrne hred x₀
  obtain ⟨q, hq, hqs⟩ := HaarCycle.cycle_of_two_matchings (matchingFactor b₀ b₁)
    b₀ b₁ (factor_cross b₀ b₁) (factor_same b₀ b₁) hbne hblue x₀
  let hR := factor_le G r₀ r₁ hr₀ hr₁
  let hB := factor_le G b₀ b₁ hb₀ hb₁
  refine ⟨(x₀, false), (x₀, false), p.mapLe hR, q.mapLe hB,
    hp.mapLe hR, hq.mapLe hB, ?_, ?_⟩
  · ext v
    simp [hps v, hqs v]
  · rw [Walk.edges_mapLe_eq_edges, Walk.edges_mapLe_eq_edges]
    apply Finset.disjoint_left.mpr
    intro e he hf
    exact Set.disjoint_left.mp (factors_edge_disjoint r₀ r₁ b₀ b₁ hdis)
      (p.edges_subset_edgeSet (List.mem_toFinset.mp he))
      (q.edges_subset_edgeSet (List.mem_toFinset.mp hf))

end Erdos585.HaarPair
