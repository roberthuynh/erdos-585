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
import Openmath.Proofs.HaarRankOne
import Openmath.Proofs.HaarRankTwo
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-! # Every four-color prime-field Haar graph contains a faithful pair

The affine reduction uses actual injective additive coordinate maps and
the normalized rank-one, rank-two, and rank-three constructions. No rank
selection, cycle, orbit, or successful graph is an assumed conclusion.
-/

namespace Erdos585.HaarClassification
open Finset

variable {p : ℕ} [Fact p.Prime]
variable {V : Type*} [AddCommGroup V] [Module (ZMod p) V]

def lineMap (a : V) : ZMod p →+ V where
  toFun t := t • a
  map_zero' := zero_smul _ _
  map_add' t u := add_smul t u a

def pairMap (a b : V) : (ZMod p × ZMod p) →+ V where
  toFun x := x.1 • a + x.2 • b
  map_zero' := by simp
  map_add' x y := by simp [add_smul]; abel

def tripleMap (a b c : V) : HaarWitness.Coord p →+ V where
  toFun x := x.1 • a + x.2.1 • b + x.2.2 • c
  map_zero' := by simp
  map_add' x y := by simp [add_smul]; abel

theorem pairMap_injective (a b : V) (h : LinearIndependent (ZMod p) ![a,b]) :
    Function.Injective (pairMap (p := p) a b) := by
  intro x y hxy
  have he : Fintype.linearCombination (ZMod p) ![a,b] ![x.1,x.2] =
      Fintype.linearCombination (ZMod p) ![a,b] ![y.1,y.2] := by
    simpa [Fintype.linearCombination_apply, Fin.sum_univ_two, pairMap] using hxy
  have hv := h.fintypeLinearCombination_injective he
  exact Prod.ext (congrFun hv 0) (congrFun hv 1)

theorem tripleMap_injective (a b c : V) (h : LinearIndependent (ZMod p) ![a,b,c]) :
    Function.Injective (tripleMap (p := p) a b c) := by
  intro x y hxy
  have he : Fintype.linearCombination (ZMod p) ![a,b,c] ![x.1,x.2.1,x.2.2] =
      Fintype.linearCombination (ZMod p) ![a,b,c] ![y.1,y.2.1,y.2.2] := by
    simpa [Fintype.linearCombination_apply, Fin.sum_univ_succ, tripleMap, add_assoc] using hxy
  have hv := h.fintypeLinearCombination_injective he
  exact Prod.ext (congrFun hv 0) (Prod.ext (congrFun hv 1) (congrFun hv 2))

/-- The alternative rank-two chart used when the fourth first coordinate is zero. -/
def flipChart : (ZMod p × ZMod p) →+ (ZMod p × ZMod p) where
  toFun x := (-x.1 - x.2, x.2)
  map_zero' := by simp
  map_add' x y := by ext <;> simp; ring

theorem flipChart_injective : Function.Injective (flipChart (p := p)) := by
  intro x y h
  have hs := congrArg Prod.snd h
  have hf := congrArg Prod.fst h
  change x.2 = y.2 at hs
  change -x.1 - x.2 = -y.1 - y.2 at hf
  rw [hs] at hf
  have hf' : -x.1 = -y.1 := by simpa using hf
  exact Prod.ext (neg_injective hf') hs

variable [DecidableEq V]

theorem hasPair_of_independent (S : Finset V) (a b c : V)
    (h₀ : 0 ∈ S) (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (hc₀ : c ≠ 0) (hca : c ≠ a) (hcb : c ≠ b)
    (hab : LinearIndependent (ZMod p) ![a,b]) : HasPairF (Haar.graph S) := by
  by_cases hspan : c ∈ Submodule.span (ZMod p) ({a,b} : Set V)
  · obtain ⟨x, y, hxy⟩ := Submodule.mem_span_pair.mp hspan
    have hf := pairMap_injective a b hab
    by_cases hx : x = 0
    · subst x
      have hyc : y • b = c := by simpa using hxy
      have hy₀ : y ≠ 0 := by intro h; apply hc₀; simpa [h] using hyc.symm
      have hy₁ : y ≠ 1 := by intro h; apply hcb; simpa [h] using hyc.symm
      have hdup : (1 - y, y - 1 + 1) ≠ (1, (0 : ZMod p)) := by
        intro h
        have hh := congrArg Prod.snd h
        exact hy₀ (by simpa using hh)
      let f := (pairMap (p := p) a b).comp flipChart
      apply Haar.hasPair_of_affine (HaarRankTwo.colors (1-y) (y-1)) S f
        (hf.comp flipChart_injective) a ?_
        (HaarRankTwo.hasPair (1-y) (y-1) (sub_ne_zero.mpr (Ne.symm hy₁)) hdup)
      intro z hz
      simp only [HaarRankTwo.colors, mem_insert, mem_singleton] at hz
      rcases hz with rfl | rfl | rfl | rfl
      · simpa [f, pairMap, flipChart] using ha
      · simpa [f, pairMap, flipChart] using h₀
      · simpa [f, pairMap, flipChart] using hb
      · simpa [f, pairMap, flipChart, hyc, sub_eq_add_neg, add_smul] using hc
    · have hdup : (x, y - 1 + 1) ≠ (1, (0 : ZMod p)) := by
        intro h
        apply hca
        have he := congrArg (pairMap (p := p) a b) h
        simpa [pairMap, hxy] using he
      apply Haar.hasPair_of_affine (HaarRankTwo.colors x (y-1)) S
        (pairMap (p := p) a b) hf 0 ?_ (HaarRankTwo.hasPair x (y-1) hx hdup)
      intro z hz
      simp only [HaarRankTwo.colors, mem_insert, mem_singleton] at hz
      rcases hz with rfl | rfl | rfl | rfl
      · simpa [pairMap] using h₀
      · simpa [pairMap] using ha
      · simpa [pairMap] using hb
      · simpa [pairMap, hxy] using hc
  · have hi : LinearIndependent (ZMod p) ![c,a,b] :=
      hab.finCons (by simpa only [Matrix.range_cons_cons_empty] using hspan)
    apply Haar.hasPair_of_affine Haar.rankThreeColors S (tripleMap (p := p) c a b)
      (tripleMap_injective c a b hi) 0 ?_ Haar.rankThree_hasPair
    intro z hz
    simp only [Haar.rankThreeColors, mem_insert, mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · simpa [tripleMap] using h₀
    · simpa [tripleMap] using hc
    · simpa [tripleMap] using ha
    · simpa [tripleMap] using hb

include p in
theorem hasPair_normalized (S : Finset V) (a b c : V)
    (h₀ : 0 ∈ S) (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (ha₀ : a ≠ 0) (hb₀ : b ≠ 0) (hc₀ : c ≠ 0)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : HasPairF (Haar.graph S) := by
  by_cases hbspan : b ∈ Submodule.span (ZMod p) ({a} : Set V)
  · by_cases hcspan : c ∈ Submodule.span (ZMod p) ({a} : Set V)
    · obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hbspan
      obtain ⟨u, hu⟩ := Submodule.mem_span_singleton.mp hcspan
      have ht₀ : t ≠ 0 := by intro h; apply hb₀; simpa [h] using ht.symm
      have hu₀ : u ≠ 0 := by intro h; apply hc₀; simpa [h] using hu.symm
      have ht₁ : t ≠ 1 := by intro h; apply hab; simpa [h] using ht
      have hu₁ : u ≠ 1 := by intro h; apply hac; simpa [h] using hu
      have htu : t ≠ u := by
        intro h
        exact hbc (ht.symm.trans ((congrArg (fun t : ZMod p => t • a) h).trans hu))
      have hp := HaarRankOne.hasPair_of_four_distinct ({0,1,t,u} : Finset (ZMod p))
        0 1 t u (by simp) (by simp) (by simp) (by simp)
        zero_ne_one ht₀.symm hu₀.symm ht₁.symm hu₁.symm htu
      apply Haar.hasPair_of_affine _ S (lineMap (p := p) a)
        (smul_left_injective (ZMod p) ha₀) 0 ?_ hp
      intro z hz
      simp only [mem_insert, mem_singleton] at hz
      rcases hz with rfl | rfl | rfl | rfl
      · simpa [lineMap] using h₀
      · simpa [lineMap] using ha
      · simpa [lineMap, ht] using hb
      · simpa [lineMap, hu] using hc
    · apply hasPair_of_independent (p := p) S a c b h₀ ha hc hb hb₀ hab.symm hbc
      exact (LinearIndependent.pair_iff' ha₀).2
        (fun t ht => hcspan (Submodule.mem_span_singleton.mpr ⟨t, ht⟩))
  · apply hasPair_of_independent (p := p) S a b c h₀ ha hb hc hc₀ hac.symm hbc.symm
    exact (LinearIndependent.pair_iff' ha₀).2
      (fun t ht => hbspan (Submodule.mem_span_singleton.mpr ⟨t, ht⟩))

include p in
/-- Every four actual colors in a module over a prime field contain the
original faithful pair, with no dimension or rank-selection hypothesis. -/
theorem hasPair_of_four (S : Finset V) (hcard : 4 ≤ S.card) :
    HasPairF (Haar.graph S) := by
  obtain ⟨g, hg⟩ := Function.Embedding.exists_of_card_le_finset
    (α := Fin 4) (by simpa using hcard)
  have hmem : ∀ k, g k ∈ S := fun k => hg ⟨k, rfl⟩
  let a := g 1 - g 0
  let b := g 2 - g 0
  let c := g 3 - g 0
  have ha₀ : a ≠ 0 := sub_ne_zero.mpr (g.injective.ne (by decide))
  have hb₀ : b ≠ 0 := sub_ne_zero.mpr (g.injective.ne (by decide))
  have hc₀ : c ≠ 0 := sub_ne_zero.mpr (g.injective.ne (by decide))
  have hab : a ≠ b := fun h => g.injective.ne (by decide) (sub_left_injective h)
  have hac : a ≠ c := fun h => g.injective.ne (by decide) (sub_left_injective h)
  have hbc : b ≠ c := fun h => g.injective.ne (by decide) (sub_left_injective h)
  have hp := hasPair_normalized (p := p) ({0,a,b,c} : Finset V) a b c
    (by simp) (by simp) (by simp) (by simp) ha₀ hb₀ hc₀ hab hac hbc
  apply Haar.hasPair_of_affine ({0,a,b,c} : Finset V) S (AddMonoidHom.id V)
    Function.injective_id (g 0) ?_ hp
  intro z hz
  simp only [mem_insert, mem_singleton] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · simpa using hmem 0
  · simpa [a, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hmem 1
  · simpa [b, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hmem 2
  · simpa [c, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hmem 3

end Erdos585.HaarClassification
