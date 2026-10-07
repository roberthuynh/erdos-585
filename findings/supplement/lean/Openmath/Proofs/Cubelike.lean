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
import Openmath.Proofs.CubelikeWitness
import Openmath.Proofs.CubelikeForest
import Mathlib.Combinatorics.SimpleGraph.Cayley
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Module

/-!
# Bipartite cubelike graphs

The four-generator orbit argument is written in Paper 65 and the standalone
restricted-class report in Paper 82. This file uses the existing faithful
cycle predicate. No asymptotic or novelty claim is attached to this special case.
-/

open SimpleGraph Finset
namespace Erdos585.Cubelike

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [DecidableEq V]

def mask (i : Fin 16) : Fin 4 → ZMod 2 :=
  ![![0,0,0,0], ![1,0,0,0], ![0,1,0,0], ![1,1,0,0],
    ![0,0,1,0], ![1,0,1,0], ![0,1,1,0], ![1,1,1,0],
    ![0,0,0,1], ![1,0,0,1], ![0,1,0,1], ![1,1,0,1],
    ![0,0,1,1], ![1,0,1,1], ![0,1,1,1], ![1,1,1,1]] i

def image4 (g : Fin 4 → V) (i : Fin 16) : V :=
  ∑ k : Fin 4, mask i k • g k

def bxor (i j : Fin 16) : Fin 16 := ⟨Nat.xor i.val j.val % 16, Nat.mod_lt _ (by decide)⟩

lemma mask_bxor : ∀ i j, mask (bxor i j) = mask i + mask j := by decide

omit [DecidableEq V] in
lemma image4_bxor (g : Fin 4 → V) (i j : Fin 16) :
    image4 g (bxor i j) = image4 g i + image4 g j := by
  simp only [image4, mask_bxor, Pi.add_apply, add_smul, sum_add_distrib]

omit [DecidableEq V] in
lemma image4_zero (g : Fin 4 → V) : image4 g 0 = 0 := by
  simp [image4, mask, Fin.sum_univ_succ]

omit [DecidableEq V] in
lemma image4_single (g : Fin 4 → V) :
    image4 g 1 = g 0 ∧ image4 g 2 = g 1 ∧
    image4 g 4 = g 2 ∧ image4 g 8 = g 3 := by
  simp [image4, mask, Fin.sum_univ_succ]

omit [DecidableEq V] in
lemma add_eq_zero_iff (a b : V) : a + b = 0 ↔ a = b := by
  rw [add_eq_zero_iff_eq_neg, ZModModule.neg_eq_self]

omit [DecidableEq V] in
lemma cayley_adj (S : Finset V) (h0 : 0 ∉ S) (x y : V) :
    (addCayley (S : Set V)).Adj x y ↔ x + y ∈ S := by
  rw [addCayley_adj]
  simp only [ZModModule.neg_eq_self, add_comm y x, or_self, mem_coe]
  constructor
  · exact And.right
  · intro h
    exact ⟨fun he => h0 (by simpa [he, ZModModule.add_self] using h), h⟩

omit [DecidableEq V] in
lemma image4_adj (S : Finset V) (h0 : 0 ∉ S) (g : Fin 4 → V)
    (hg : ∀ k, g k ∈ S) (i j : Fin 16)
    (h : Nat.xor i.val j.val ∈ ({1,2,4,8} : Finset ℕ)) :
    (addCayley (S : Set V)).Adj (image4 g i) (image4 g j) := by
  rw [cayley_adj S h0, ← image4_bxor]
  have hs := image4_single g
  simp only [mem_insert, mem_singleton] at h
  rcases h with h | h | h | h <;>
    simp only [bxor, h, Nat.reduceMod] <;>
    simp_all

def evenMasks : Finset (Fin 16) := {0,3,5,6,9,10,12,15}

lemma cube_color (c : Fin 16 → Fin 2)
    (hc : ∀ i j, CubelikeWitness.q4.Adj i j → c i ≠ c j) :
    ∀ i, i ∉ evenMasks → c i ≠ c 0 := by
  have h1 := hc 0 1 (by decide)
  have h2 := hc 0 2 (by decide)
  have h3 := hc 1 3 (by decide)
  have h4 := hc 0 4 (by decide)
  have h5 := hc 1 5 (by decide)
  have h6 := hc 2 6 (by decide)
  have h7 := hc 3 7 (by decide)
  have h8 := hc 0 8 (by decide)
  have h9 := hc 1 9 (by decide)
  have h10 := hc 2 10 (by decide)
  have h11 := hc 3 11 (by decide)
  have h12 := hc 4 12 (by decide)
  have h13 := hc 5 13 (by decide)
  have h14 := hc 6 14 (by decide)
  have h15 := hc 7 15 (by decide)
  intro i hi
  have hm : ∀ j : Fin 16, j ∉ evenMasks →
      j = 1 ∨ j = 2 ∨ j = 4 ∨ j = 7 ∨ j = 8 ∨ j = 11 ∨ j = 13 ∨ j = 14 := by decide
  rcases hm i hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

lemma image4_kernel (S : Finset V) (h0 : 0 ∉ S) (g : Fin 4 → V)
    (hg : ∀ k, g k ∈ S) (hi : Function.Injective g)
    (hb : (addCayley (S : Set V)).IsBipartite)
    (i : Fin 16) (hz : image4 g i = 0) : i = 0 ∨ i = 15 := by
  obtain ⟨col⟩ := hb
  have he : i ∈ evenMasks := by
    by_contra hn
    have hh := cube_color (fun j => col (image4 g j))
      (fun a b hab => col.valid (image4_adj S h0 g hg a b hab)) i hn
    exact hh (by rw [hz, image4_zero])
  have cases : ∀ j : Fin 16, j ∈ evenMasks →
      j = 0 ∨ j = 15 ∨ j = 3 ∨ j = 5 ∨ j = 6 ∨ j = 9 ∨ j = 10 ∨ j = 12 := by
    decide
  rcases cases i he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl
  all_goals
    simp [image4, mask, Fin.sum_univ_succ] at hz
    have hh := hi ((add_eq_zero_iff _ _).1 hz)
    have hn := congrArg Fin.val hh
    norm_num at hn

lemma image4_injective (S : Finset V) (h0 : 0 ∉ S) (g : Fin 4 → V)
    (hg : ∀ k, g k ∈ S) (hi : Function.Injective g)
    (hb : (addCayley (S : Set V)).IsBipartite) (hn : image4 g 15 ≠ 0) :
    Function.Injective (image4 g) := by
  intro i j hij
  have hz : image4 g (bxor i j) = 0 := by
    rw [image4_bxor, hij, ZModModule.add_self]
  rcases image4_kernel S h0 g hg hi hb _ hz with hz0 | hz15
  · exact (by decide : ∀ i j : Fin 16, bxor i j = 0 → i = j) i j hz0
  · exact False.elim (hn (hz15 ▸ hz))

def up (i : Fin 8) : Fin 16 := ⟨i.val, Nat.lt_trans i.isLt (by decide)⟩

lemma image8_injective (S : Finset V) (h0 : 0 ∉ S) (g : Fin 4 → V)
    (hg : ∀ k, g k ∈ S) (hi : Function.Injective g)
    (hb : (addCayley (S : Set V)).IsBipartite) :
    Function.Injective (fun i : Fin 8 => image4 g (up i)) := by
  intro i j hij
  change image4 g (up i) = image4 g (up j) at hij
  have hz : image4 g (bxor (up i) (up j)) = 0 := by
    rw [image4_bxor, hij, ZModModule.add_self]
  rcases image4_kernel S h0 g hg hi hb _ hz with hz0 | hz15
  · exact (by decide : ∀ i j : Fin 8, bxor (up i) (up j) = 0 → i = j) i j hz0
  · exact False.elim ((by decide : ∀ i j : Fin 8, bxor (up i) (up j) ≠ 15) i j hz15)

omit [DecidableEq V] in
lemma image8_adj (S : Finset V) (h0 : 0 ∉ S) (g : Fin 4 → V)
    (hg : ∀ k, g k ∈ S) (hz : image4 g 15 = 0) (i j : Fin 8)
    (h : CubelikeWitness.folded.Adj i j) :
    (addCayley (S : Set V)).Adj (image4 g (up i)) (image4 g (up j)) := by
  have h7 : image4 g 7 = g 3 := by
    rw [← (image4_single g).2.2.2]
    apply (add_eq_zero_iff _ _).1
    rw [← image4_bxor]
    exact hz
  rw [cayley_adj S h0, ← image4_bxor]
  have hs := image4_single g
  change Nat.xor i.val j.val ∈ ({1,2,4,7} : Finset ℕ) at h
  simp only [mem_insert, mem_singleton] at h
  rcases h with h | h | h | h <;>
    simp only [bxor, up, h, Nat.reduceMod] <;> simp_all

/-- Four distinct generators in a bipartite cubelike graph give actual cycles. -/
theorem hasPair_of_four (S : Finset V) (h0 : 0 ∉ S)
    (hb : (addCayley (S : Set V)).IsBipartite) (hcard : 4 ≤ S.card) :
    HasPairF (addCayley (S : Set V)) := by
  obtain ⟨g, hg⟩ := Function.Embedding.exists_of_card_le_finset
    (α := Fin 4) (by simpa using hcard)
  have hmem : ∀ k, g k ∈ S := fun k => hg ⟨k, rfl⟩
  by_cases hz : image4 g 15 = 0
  · exact CubelikeWitness.hasPair_of_folded _ _
      (image8_injective S h0 g hmem g.injective hb)
      (image8_adj S h0 g hmem hz)
  · exact CubelikeWitness.hasPair_of_q4 _ _
      (image4_injective S h0 g hmem g.injective hb hz)
      (image4_adj S h0 g hmem)

/-- Avoidance bounds the number of generators throughout this whole class. -/
theorem card_le_three_of_avoiding (S : Finset V) (h0 : 0 ∉ S)
    (hb : (addCayley (S : Set V)).IsBipartite)
    (ha : ¬ HasTwoEdgeDisjointCyclesSameVertexSet (addCayley (S : Set V))) :
    S.card ≤ 3 := by
  by_contra hn
  exact ha ((hasPairF_iff _).1 (hasPair_of_four S h0 hb (by omega)))

/-- The edges in one generator direction form an actual matching forest. -/
def generatorForest (s : V) : SimpleGraph V := addCayley (({s} : Finset V) : Set V)

omit [DecidableEq V] in
lemma generatorForest_acyclic (s : V) (hs : s ≠ 0) :
    (generatorForest s).IsAcyclic := by
  apply CubelikeForest.acyclic_of_neighbor_unique
  intro x y z hy hz
  have h0 : 0 ∉ ({s} : Finset V) := by simpa [eq_comm] using hs
  have hy' := (cayley_adj {s} h0 x y).1 hy
  have hz' := (cayley_adj {s} h0 x z).1 hz
  simp only [mem_singleton] at hy' hz'
  exact add_left_cancel (hy'.trans hz'.symm)

/-- A single explicit forest probability law certifies R-Gamma in the whole class. -/
theorem forest_certificate (S : Finset V) (h0 : 0 ∉ S) (hne : S.Nonempty)
    (hb : (addCayley (S : Set V)).IsBipartite)
    (ha : ¬ HasTwoEdgeDisjointCyclesSameVertexSet (addCayley (S : Set V))) :
    ∃ w : S → ℝ, (∀ s, 0 ≤ w s) ∧ (∑ s, w s) = 1 ∧
      (∀ s : S, generatorForest s.val ≤ addCayley (S : Set V) ∧
        (generatorForest s.val).IsAcyclic) ∧
      ∀ (a : V) (p : (addCayley (S : Set V)).Walk a a), p.IsCycle →
        (4 : ℝ) / 3 ≤ ∑ s : S, w s *
          (CubelikeForest.intersectionCount p (generatorForest s.val) : ℝ) := by
  classical
  apply CubelikeForest.forest_cover_certificate
  · simpa using hne.card_pos
  · simpa using card_le_three_of_avoiding S h0 hb ha
  · intro s
    apply addCayley_mono
    intro x hx
    have he : x = s.val := mem_singleton.mp hx
    simpa only [Finset.mem_coe, he] using s.property
  · intro s
    exact generatorForest_acyclic s.val (fun he => h0 (he ▸ s.property))
  · intro e
    refine Sym2.inductionOn e ?_
    intro x y hxy
    change (addCayley (S : Set V)).Adj x y at hxy
    have hs := (cayley_adj S h0 x y).1 hxy
    refine ⟨⟨x + y, hs⟩, ?_⟩
    change (generatorForest (x+y)).Adj x y
    have hn : 0 ∉ ({x+y} : Finset V) := by
      simp only [mem_singleton]
      exact fun he => h0 (he ▸ hs)
    exact (cayley_adj {x+y} hn x y).2 (mem_singleton_self _)
  · exact hb

lemma nonempty_generators_of_cycle (S : Finset V) (h0 : 0 ∉ S)
    {a : V} (p : (addCayley (S : Set V)).Walk a a) (hp : p.IsCycle) : S.Nonempty := by
  cases p with
  | nil => exact (hp.not_nil Walk.Nil.nil).elim
  | cons h p => exact ⟨_, (cayley_adj S h0 _ _).1 h⟩

/-- The cycle-law formulation of R-Gamma, with the explicit constant four thirds.
Every atom is an actual simple cycle of the given Cayley graph. -/
theorem regular_gamma_cubelike (S : Finset V) (h0 : 0 ∉ S)
    (hb : (addCayley (S : Set V)).IsBipartite)
    (ha : ¬ HasTwoEdgeDisjointCyclesSameVertexSet (addCayley (S : Set V)))
    {J : Type*} [Fintype J] (base : J → V)
    (p : ∀ j, (addCayley (S : Set V)).Walk (base j) (base j))
    (hp : ∀ j, (p j).IsCycle) (lam : J → ℝ)
    (hlam : ∀ j, 0 ≤ lam j) (hlamsum : ∑ j, lam j = 1) :
    ∃ F : SimpleGraph V, F ≤ addCayley (S : Set V) ∧ F.IsAcyclic ∧
      (4 : ℝ) / 3 ≤ ∑ j, lam j * (CubelikeForest.intersectionCount (p j) F : ℝ) := by
  have hJ : Nonempty J := by
    by_contra hn
    haveI : IsEmpty J := not_nonempty_iff.mp hn
    simpa using hlamsum
  obtain ⟨j⟩ := hJ
  have hne := nonempty_generators_of_cycle S h0 (p j) (hp j)
  obtain ⟨w, hw, hwsum, hF, hcert⟩ := forest_certificate S h0 hne hb ha
  exact CubelikeForest.cycle_law_forest_of_certificate
    (fun s : S => generatorForest s.val) w hw hwsum hF (4 / 3) hcert
    base p hp lam hlam hlamsum

end Erdos585.Cubelike
