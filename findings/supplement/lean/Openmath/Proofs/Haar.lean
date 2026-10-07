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
import Openmath.Proofs.CubelikeForest
import Openmath.Proofs.SmallExact
import Openmath.Proofs.HaarWitness
import Openmath.Proofs.HaarPair

/-! # Actual bipartite Haar graphs

The colors are arbitrary elements of an additive group, including zero.
An edge of color s joins (x,false) to (x+s,true). Each single color is
an actual matching forest. This file does not identify Haar graphs with
ordinary Cayley graphs on an abelian group.

`rankThree_hasPair` proves the original actual-cycle predicate for every
prime on the four affinely independent coordinate colors. The generic
`hasPair_of_affine` transports this witness into an actual larger Haar
graph through an injective additive map. The full four-color theorem
still requires the affine-rank-one and affine-rank-two constructions and
their rank-selection reduction; none is assumed as a hypothesis here.
-/

namespace Erdos585.Haar
open SimpleGraph Finset

variable {V : Type*} [AddCommGroup V]

def graph (S : Finset V) : SimpleGraph (V × Bool) where
  Adj x y :=
    (x.2 = false ∧ y.2 = true ∧ y.1 - x.1 ∈ S) ∨
    (y.2 = false ∧ x.2 = true ∧ x.1 - y.1 ∈ S)
  symm := ⟨fun _ _ h => h.elim Or.inr Or.inl⟩
  loopless := ⟨by
    intro x h
    rcases h with h | h <;> exact Bool.false_ne_true (h.1.symm.trans h.2.1)⟩

instance [DecidableEq V] (S : Finset V) : DecidableRel (graph S).Adj := fun _ _ =>
  inferInstanceAs (Decidable (_ ∨ _))

@[simp] theorem graph_cross (S : Finset V) (x y : V) :
    (graph S).Adj (x, false) (y, true) ↔ y - x ∈ S := by
  simp [graph]

@[simp] theorem graph_same (S : Finset V) (x y : V) (b : Bool) :
    ¬ (graph S).Adj (x, b) (y, b) := by
  cases b <;> simp [graph]

theorem graph_mono {S T : Finset V} (h : S ⊆ T) : graph S ≤ graph T := by
  intro x y hxy
  rcases hxy with hxy | hxy
  · exact Or.inl ⟨hxy.1, hxy.2.1, h hxy.2.2⟩
  · exact Or.inr ⟨hxy.1, hxy.2.1, h hxy.2.2⟩

theorem graph_bipartite (S : Finset V) : (graph S).IsBipartite := by
  refine ⟨⟨fun x => if x.2 then 1 else 0, ?_⟩⟩
  intro x y hxy
  rcases hxy with hxy | hxy <;> simp [hxy.1, hxy.2.1]

theorem singleton_acyclic (s : V) : (graph {s}).IsAcyclic := by
  classical
  apply CubelikeForest.acyclic_of_neighbor_unique
  intro x y z hxy hxz
  obtain ⟨x, b⟩ := x
  obtain ⟨y, c⟩ := y
  obtain ⟨z, d⟩ := z
  cases b <;> cases c <;> cases d <;>
    simp_all [graph, sub_eq_iff_eq_add]

variable {W : Type*} [AddCommGroup W]

/-- An additive embedding with a separate translation on the second shore. -/
def affineVertex (f : V →+ W) (s₀ : W) (v : V × Bool) : W × Bool :=
  (f v.1 + if v.2 then s₀ else 0, v.2)

theorem affineVertex_injective (f : V →+ W) (hf : Function.Injective f) (s₀ : W) :
    Function.Injective (affineVertex f s₀) := by
  rintro ⟨x, b⟩ ⟨y, c⟩ h
  have hbc := congrArg Prod.snd h
  change b = c at hbc
  subst c
  have hxy := congrArg Prod.fst h
  change f x + _ = f y + _ at hxy
  exact Prod.ext (hf (add_right_cancel hxy)) rfl

def affineHom (S : Finset V) (T : Finset W) (f : V →+ W) (s₀ : W)
    (hS : ∀ s ∈ S, s₀ + f s ∈ T) : graph S →g graph T where
  toFun := affineVertex f s₀
  map_rel' := by
    rintro ⟨x, b⟩ ⟨y, c⟩ hxy
    cases b <;> cases c <;> simp only [graph, Bool.false_eq_true, Bool.true_eq_false,
      false_and, and_false, or_false, false_or, true_and, affineVertex,
      Bool.false_eq_true, ite_false, ite_true, add_zero] at hxy ⊢
    · have he : f y + s₀ - f x = s₀ + f (y - x) := by rw [map_sub]; abel
      rw [he]
      exact hS _ hxy
    · have he : f x + s₀ - f y = s₀ + f (x - y) := by rw [map_sub]; abel
      rw [he]
      exact hS _ hxy

theorem hasPair_of_affine [DecidableEq V] [DecidableEq W]
    (S : Finset V) (T : Finset W) (f : V →+ W) (hf : Function.Injective f) (s₀ : W)
    (hS : ∀ s ∈ S, s₀ + f s ∈ T) (hpair : HasPairF (graph S)) :
    HasPairF (graph T) :=
  hpair.map (affineHom S T f s₀ hS) (affineVertex_injective f hf s₀)

section RankThree
open HaarWitness
variable {p : ℕ} [Fact p.Prime]

/-- The four affinely independent colors in three prime-field coordinates. -/
def rankThreeColors : Finset (Coord p) := {0, (1, 0, 0), (0, 1, 0), (0, 0, 1)}

theorem matchZero_adj (x : Coord p) :
    (graph rankThreeColors).Adj (x, false) (matchZero x, true) := by
  rw [graph_cross]
  by_cases hx : x.1 = x.2.2 <;>
    simp [matchZero, middleShift, hx, rankThreeColors, Prod.sub_def]

theorem matchB_adj (x : Coord p) :
    (graph rankThreeColors).Adj (x, false) (matchB x, true) := by
  rw [graph_cross]
  by_cases hx : x.1 = x.2.2 <;>
    simp [matchB, middleShift, hx, rankThreeColors, Prod.sub_def]

theorem matchA_adj (x : Coord p) :
    (graph rankThreeColors).Adj (x, false) (matchA x, true) := by
  rw [graph_cross]
  change x + (1, 0, 0) - x ∈ rankThreeColors
  simp [rankThreeColors]

theorem matchC_adj (x : Coord p) :
    (graph rankThreeColors).Adj (x, false) (matchC x, true) := by
  rw [graph_cross]
  change x + (0, 0, 1) - x ∈ rankThreeColors
  simp [rankThreeColors]

theorem matchAFinal_adj (x : Coord p) :
    (graph rankThreeColors).Adj (x, false) (matchAFinal x, true) := by
  rcases matchAFinal_cases x with h | h <;> rw [h]
  · exact matchA_adj x
  · exact matchC_adj x

theorem matchCFinal_adj (x : Coord p) :
    (graph rankThreeColors).Adj (x, false) (matchCFinal x, true) := by
  rcases matchCFinal_cases x with h | h <;> rw [h]
  · exact matchC_adj x
  · exact matchA_adj x

/-- Actual edge-disjoint cycles on the same support, uniformly in the prime. -/
theorem rankThree_hasPair : HasPairF (graph (rankThreeColors (p := p))) := by
  apply HaarPair.hasPair_of_matching_permutations _
    matchAFinal matchZero matchCFinal matchB
    matchAFinal_adj matchZero_adj matchCFinal_adj matchB_adj
  · intro x
    exact (middleShift_ne_matchAFinal _ x).symm
  · intro x
    exact (middleShift_ne_matchCFinal _ x).symm
  · intro x
    exact ⟨matchAFinal_ne_matchCFinal x, (middleShift_ne_matchAFinal _ x).symm,
      middleShift_ne_matchCFinal _ x, matchZero_ne_matchB x⟩
  · rw [← redFinal_eq_successor]
    exact redFinal_isCycleOn
  · rw [← blueFinal_eq_successor]
    exact blueFinal_isCycleOn
  · exact 0

end RankThree

end Erdos585.Haar
