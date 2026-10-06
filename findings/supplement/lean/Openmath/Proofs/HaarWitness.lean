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
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-! # Prime-field successor permutations for Haar graphs

The skew-shift orbit calculation is uniform in the prime. It supplies the
level orbits in the rank-three construction of Paper83. Graph walks and
the affine-rank reduction are separate obligations.
-/

namespace Erdos585.HaarWitness
open Equiv Equiv.Perm Finset

variable {p : ℕ} [Fact p.Prime]

/-- Add one in the first coordinate, with a prescribed vertical increment. -/
def skew (f : ZMod p → ZMod p) : Perm (ZMod p × ZMod p) where
  toFun x := (x.1 + 1, x.2 + f x.1)
  invFun x := (x.1 - 1, x.2 - f (x.1 - 1))
  left_inv x := by ext <;> simp
  right_inv x := by ext <;> simp

@[simp] theorem skew_apply (f : ZMod p → ZMod p) (x : ZMod p × ZMod p) :
    skew f x = (x.1 + 1, x.2 + f x.1) := rfl

theorem skew_pow (f : ZMod p → ZMod p) (n : ℕ) (x : ZMod p × ZMod p) :
    (skew f ^ n) x = (x.1 + n, x.2 + ∑ i ∈ range n, f (x.1 + i)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_apply, ih, skew_apply, sum_range_succ]
    ext <;> simp [Nat.cast_add, Nat.cast_one, add_assoc]

theorem sum_shift (f : ZMod p → ZMod p) (a : ZMod p) :
    ∑ i ∈ range p, f (a + i) = ∑ i : ZMod p, f i := by
  apply sum_bij (fun (i : ℕ) _ => a + (i : ZMod p))
  · intros; exact mem_univ _
  · intro i hi j hj hij
    have heq := congrArg ZMod.val (add_left_cancel hij)
    simpa [ZMod.val_natCast_of_lt (mem_range.mp hi),
      ZMod.val_natCast_of_lt (mem_range.mp hj)] using heq
  · intro b _
    refine ⟨(b - a).val, mem_range.mpr (ZMod.val_lt _), ?_⟩
    simp
  · intros; rfl

theorem skew_pow_prime (f : ZMod p → ZMod p) (x : ZMod p × ZMod p) :
    (skew f ^ p) x = (x.1, x.2 + ∑ i : ZMod p, f i) := by
  simp [skew_pow, sum_shift]

theorem skew_pow_prime_mul (f : ZMod p → ZMod p) (n : ℕ)
    (x : ZMod p × ZMod p) :
    (skew f ^ (p * n)) x = (x.1, x.2 + n * ∑ i : ZMod p, f i) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [Nat.mul_succ, pow_add, mul_apply, skew_pow_prime, ih]
    ext <;> simp [Nat.cast_add, Nat.cast_one]
    ring

/-- A nonzero total increment makes the skew shift one full cycle. -/
theorem skew_isCycleOn (f : ZMod p → ZMod p) (hf : ∑ i, f i ≠ 0) :
    (skew f).IsCycleOn Set.univ := by
  refine ⟨(skew f).bijOn (fun _ => Iff.rfl), ?_⟩
  intro x _ y _
  let n := (y.1 - x.1).val
  let z := (skew f ^ n) x
  have hz : z.1 = y.1 := by simp [z, skew_pow, n]
  let m := ((y.2 - z.2) / ∑ i, f i).val
  have hm : (m : ZMod p) * ∑ i, f i = y.2 - z.2 := by
    simp [m, div_mul_cancel₀ _ hf]
  have hzy : (skew f ^ (p * m)) z = y := by
    rw [skew_pow_prime_mul]
    ext <;> simp [hz, hm]
  have hrel : (skew f).SameCycle z ((skew f ^ (p * m)) z) :=
    (SameCycle.refl (skew f) z).pow_right
  rw [hzy] at hrel
  exact ((SameCycle.refl (skew f) x).pow_right (n := n)).trans hrel

/-- Independent permutations of the fibers of a product. -/
def fiberPerm {I A : Type*} (F : I → Perm A) : Perm (I × A) where
  toFun x := (x.1, F x.1 x.2)
  invFun x := (x.1, (F x.1).symm x.2)
  left_inv x := by simp
  right_inv x := by simp

theorem fiberPerm_pow {I A : Type*} (F : I → Perm A) (n : ℕ) (x : I × A) :
    (fiberPerm F ^ n) x = (x.1, (F x.1 ^ n) x.2) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', mul_apply, ih]
    change (x.1, F x.1 ((F x.1 ^ n) x.2)) = _
    rw [pow_succ', mul_apply]

theorem fiberPerm_sameCycle_iff {I A : Type*} [Finite I] [Finite A]
    (F : I → Perm A) (hF : ∀ i, (F i).IsCycleOn Set.univ) (x y : I × A) :
    (fiberPerm F).SameCycle x y ↔ x.1 = y.1 := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    simpa [fiberPerm_pow] using congrArg Prod.fst hn
  · intro h
    obtain ⟨i, a⟩ := x
    obtain ⟨j, b⟩ := y
    dsimp at h
    subst j
    obtain ⟨n, hn⟩ := ((hF i).2 (Set.mem_univ a) (Set.mem_univ b)).exists_nat_pow_eq
    have hr := (SameCycle.refl (fiberPerm F) (i, a)).pow_right (n := n)
    simpa [fiberPerm_pow, hn] using hr

abbrev Coord (p : ℕ) := ZMod p × ZMod p × ZMod p

def redInc (c a : ZMod p) : ZMod p := if a = c - 1 then -1 else 0

def blueInc (a c : ZMod p) : ZMod p := -1 - redInc a c

@[simp] theorem sum_redInc (c : ZMod p) : ∑ a, redInc c a = -1 := by
  simp [redInc]

@[simp] theorem sum_blueInc (a : ZMod p) : ∑ c, blueInc a c = 1 := by
  simp [blueInc, sum_sub_distrib, ZMod.card]

/-- Put the fixed third coordinate first, then the two moving coordinates. -/
def redCoords : Perm (Coord p) where
  toFun x := (x.2.2, x.1, x.2.1)
  invFun x := (x.2.1, x.2.2, x.1)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Put the fixed first coordinate first, then the moving third and second. -/
def blueCoords : Perm (Coord p) where
  toFun x := (x.1, x.2.2, x.2.1)
  invFun x := (x.1, x.2.2, x.2.1)
  left_inv _ := rfl
  right_inv _ := rfl

def red : Perm (Coord p) :=
  redCoords⁻¹ * fiberPerm (fun c => skew (redInc c)) * redCoords

def blue : Perm (Coord p) :=
  blueCoords⁻¹ * fiberPerm (fun a => skew (blueInc a)) * blueCoords

@[simp] theorem red_apply (x : Coord p) :
    red x = (x.1 + 1, x.2.1 - (if x.1 + 1 = x.2.2 then 1 else 0), x.2.2) := by
  change (x.1 + 1, x.2.1 + redInc x.2.2 x.1, x.2.2) = _
  congr 2
  simp only [redInc, eq_sub_iff_add_eq]
  split_ifs <;> simp

@[simp] theorem blue_apply (x : Coord p) :
    blue x = (x.1, x.2.1 - (if x.1 ≠ x.2.2 + 1 then 1 else 0), x.2.2 + 1) := by
  change (x.1, x.2.1 + blueInc x.1 x.2.2, x.2.2 + 1) = _
  congr 2
  by_cases he : x.2.2 = x.1 - 1
  · have h : ¬x.1 ≠ x.2.2 + 1 := not_ne_iff.mpr ((eq_sub_iff_add_eq).1 he).symm
    simp only [blueInc, redInc, if_pos he, if_neg h]
    simp
  · have h : x.1 ≠ x.2.2 + 1 := fun h => he ((eq_sub_iff_add_eq).2 h.symm)
    simp only [blueInc, redInc, if_neg he, if_pos h]
    simp [sub_eq_add_neg]

/-- Red first-stage components are exactly the third-coordinate levels. -/
theorem red_sameCycle_iff (x y : Coord p) :
    red.SameCycle x y ↔ x.2.2 = y.2.2 := by
  have hh := @sameCycle_conj (Coord p) (fiberPerm (fun c => skew (redInc c)))
    redCoords⁻¹ x y
  simp only [inv_inv] at hh
  rw [red, hh]
  exact fiberPerm_sameCycle_iff _ (fun c => skew_isCycleOn _ (by simp)) _ _

/-- Blue first-stage components are exactly the first-coordinate levels. -/
theorem blue_sameCycle_iff (x y : Coord p) :
    blue.SameCycle x y ↔ x.1 = y.1 := by
  have hh := @sameCycle_conj (Coord p) (fiberPerm (fun a => skew (blueInc a)))
    blueCoords⁻¹ x y
  simp only [inv_inv] at hh
  rw [blue, hh]
  exact fiberPerm_sameCycle_iff _ (fun a => skew_isCycleOn _ (by simp)) _ _

theorem addRight_pow (d : ZMod p) (n : ℕ) (x : ZMod p) :
    (Equiv.addRight d ^ n) x = x + n * d := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_apply, ih]
    change x + n * d + d = _
    simp [Nat.cast_add, Nat.cast_one, add_mul, add_assoc]

theorem addRight_isCycleOn (d : ZMod p) (hd : d ≠ 0) :
    (Equiv.addRight d).IsCycleOn Set.univ := by
  refine ⟨(Equiv.addRight d).bijOn (fun _ => Iff.rfl), ?_⟩
  intro x _ y _
  let n := ((y - x) / d).val
  have hn : (Equiv.addRight d ^ n) x = y := by
    simp [n, div_mul_cancel₀ _ hd]
  have h := (SameCycle.refl (Equiv.addRight d) x).pow_right (n := n)
  rw [hn] at h
  exact h

def mark (u : ZMod p) : Coord p := (u, 0, -u)

def markEmbedding : ZMod p ↪ Coord p where
  toFun := mark
  inj' := by intro u v h; exact congrArg Prod.fst h

/-- Rotate the marked transversal, fixing every unmarked point. -/
noncomputable def markShift (d : ZMod p) : Perm (Coord p) := by
  classical
  exact (Equiv.addRight d).extendDomain markEmbedding.toEquivRange

@[simp] theorem markShift_mark (d u : ZMod p) :
    markShift d (mark u) = mark (u + d) := by
  classical
  exact extendDomain_apply_image _ markEmbedding.toEquivRange u

theorem markShift_fixed (d : ZMod p) (x : Coord p) (hx : ∀ u, x ≠ mark u) :
    markShift d x = x := by
  classical
  apply extendDomain_apply_not_subtype
  rintro ⟨u, hu⟩
  exact hx u hu.symm

noncomputable def redFinal : Perm (Coord p) := red * markShift (-1)
noncomputable def blueFinal : Perm (Coord p) := blue * markShift 1

/-- The final red successor visits every prime-field triple. -/
theorem redFinal_isCycleOn : (redFinal (p := p)).IsCycleOn Set.univ := by
  apply HaarCycle.splice_isCycleOn red redFinal (Equiv.addRight (-1)) mark
  · intro x
    exact ⟨-x.2.2, (red_sameCycle_iff _ _).2 (by simp [mark])⟩
  · intro i j h
    have hh := (red_sameCycle_iff _ _).1 h
    simpa [mark] using hh
  · intro x hx
    change red (markShift (-1) x) = red x
    rw [markShift_fixed _ _ hx]
  · intro i
    change red (markShift (-1) (mark i)) = red (mark (i + -1))
    rw [markShift_mark]
  · exact addRight_isCycleOn _ (by simp)

/-- The final blue successor visits every prime-field triple. -/
theorem blueFinal_isCycleOn : (blueFinal (p := p)).IsCycleOn Set.univ := by
  apply HaarCycle.splice_isCycleOn blue blueFinal (Equiv.addRight 1) mark
  · intro x
    exact ⟨x.1, (blue_sameCycle_iff _ _).2 rfl⟩
  · intro i j h
    exact (blue_sameCycle_iff _ _).1 h
  · intro x hx
    change blue (markShift 1 x) = blue x
    rw [markShift_fixed _ _ hx]
  · intro i
    change blue (markShift 1 (mark i)) = blue (mark (i + 1))
    rw [markShift_mark]
  · exact addRight_isCycleOn _ one_ne_zero

/-- A shear of the middle coordinate, with the other two coordinates fixed. -/
def middleShift (f : ZMod p → ZMod p → ZMod p) : Perm (Coord p) where
  toFun x := (x.1, x.2.1 + f x.1 x.2.2, x.2.2)
  invFun x := (x.1, x.2.1 - f x.1 x.2.2, x.2.2)
  left_inv x := by ext <;> simp
  right_inv x := by ext <;> simp

def matchZero : Perm (Coord p) := middleShift (fun a c => if a = c then 1 else 0)
def matchB : Perm (Coord p) := middleShift (fun a c => if a = c then 0 else 1)
def matchA : Perm (Coord p) := Equiv.addRight (1, 0, 0)
def matchC : Perm (Coord p) := Equiv.addRight (0, 0, 1)
noncomputable def matchAFinal : Perm (Coord p) := matchA * markShift (-1)
noncomputable def matchCFinal : Perm (Coord p) := matchC * markShift 1

theorem red_eq_successor : red (p := p) = matchZero⁻¹ * matchA := by
  ext x : 1
  simp only [red_apply]
  simp [matchZero, matchA, middleShift, mul_apply]

theorem blue_eq_successor : blue (p := p) = matchB⁻¹ * matchC := by
  ext x : 1
  simp only [blue_apply]
  change (x.1, x.2.1 - (if x.1 ≠ x.2.2 + 1 then 1 else 0), x.2.2 + 1) =
    (x.1 + 0, x.2.1 + 0 - (if x.1 + 0 = x.2.2 + 1 then 0 else 1), x.2.2 + 1)
  simp only [add_zero]
  split_ifs <;> simp_all

theorem redFinal_eq_successor :
    redFinal (p := p) = matchZero⁻¹ * matchAFinal := by
  rw [redFinal, matchAFinal, red_eq_successor, mul_assoc]

theorem blueFinal_eq_successor :
    blueFinal (p := p) = matchB⁻¹ * matchCFinal := by
  rw [blueFinal, matchCFinal, blue_eq_successor, mul_assoc]

@[simp] theorem matchAFinal_mark (u : ZMod p) : matchAFinal (mark u) = matchC (mark u) := by
  simp only [matchAFinal, mul_apply, markShift_mark]
  change (u + -1 + 1, 0 + 0, -(u + -1) + 0) = (u + 0, 0 + 0, -u + 1)
  ext <;> ring

@[simp] theorem matchCFinal_mark (u : ZMod p) : matchCFinal (mark u) = matchA (mark u) := by
  simp only [matchCFinal, mul_apply, markShift_mark]
  change (u + 1 + 0, 0 + 0, -(u + 1) + 1) = (u + 1, 0 + 0, -u + 0)
  ext <;> ring

theorem matchAFinal_fixed (x : Coord p) (hx : ∀ u, x ≠ mark u) :
    matchAFinal x = matchA x := by
  change matchA (markShift (-1) x) = matchA x
  rw [markShift_fixed _ _ hx]

theorem matchCFinal_fixed (x : Coord p) (hx : ∀ u, x ≠ mark u) :
    matchCFinal x = matchC x := by
  change matchC (markShift 1 x) = matchC x
  rw [markShift_fixed _ _ hx]

theorem matchAFinal_cases (x : Coord p) :
    matchAFinal x = matchA x ∨ matchAFinal x = matchC x := by
  classical
  by_cases hx : ∃ u, x = mark u
  · obtain ⟨u, rfl⟩ := hx
    exact Or.inr (matchAFinal_mark u)
  · exact Or.inl (matchAFinal_fixed x (not_exists.mp hx))

theorem matchCFinal_cases (x : Coord p) :
    matchCFinal x = matchC x ∨ matchCFinal x = matchA x := by
  classical
  by_cases hx : ∃ u, x = mark u
  · obtain ⟨u, rfl⟩ := hx
    exact Or.inr (matchCFinal_mark u)
  · exact Or.inl (matchCFinal_fixed x (not_exists.mp hx))

theorem middleShift_ne_matchA (f : ZMod p → ZMod p → ZMod p) (x : Coord p) :
    middleShift f x ≠ matchA x := by
  intro h
  have hh := congrArg Prod.fst h
  simp [middleShift, matchA] at hh

theorem middleShift_ne_matchC (f : ZMod p → ZMod p → ZMod p) (x : Coord p) :
    middleShift f x ≠ matchC x := by
  intro h
  have hh := congrArg (fun x : Coord p => x.2.2) h
  simp [middleShift, matchC] at hh

theorem middleShift_ne_matchAFinal (f : ZMod p → ZMod p → ZMod p) (x : Coord p) :
    middleShift f x ≠ matchAFinal x := by
  rcases matchAFinal_cases x with h | h <;> rw [h]
  · exact middleShift_ne_matchA f x
  · exact middleShift_ne_matchC f x

theorem middleShift_ne_matchCFinal (f : ZMod p → ZMod p → ZMod p) (x : Coord p) :
    middleShift f x ≠ matchCFinal x := by
  rcases matchCFinal_cases x with h | h <;> rw [h]
  · exact middleShift_ne_matchC f x
  · exact middleShift_ne_matchA f x

theorem matchZero_ne_matchB (x : Coord p) : matchZero x ≠ matchB x := by
  intro h
  have hh := congrArg (fun x : Coord p => x.2.1) h
  by_cases hx : x.1 = x.2.2 <;> simp [matchZero, matchB, middleShift, hx] at hh

theorem matchA_ne_matchC (x : Coord p) : matchA x ≠ matchC x := by
  intro h
  have hh := congrArg Prod.fst h
  simp [matchA, matchC] at hh

theorem matchAFinal_ne_matchCFinal (x : Coord p) : matchAFinal x ≠ matchCFinal x := by
  classical
  by_cases hx : ∃ u, x = mark u
  · obtain ⟨u, rfl⟩ := hx
    rw [matchAFinal_mark, matchCFinal_mark]
    exact (matchA_ne_matchC _).symm
  · rw [matchAFinal_fixed x (not_exists.mp hx), matchCFinal_fixed x (not_exists.mp hx)]
    exact matchA_ne_matchC x

end Erdos585.HaarWitness
