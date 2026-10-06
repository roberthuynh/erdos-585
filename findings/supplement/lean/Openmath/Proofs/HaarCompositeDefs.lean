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
import Mathlib.GroupTheory.Perm.ViaEmbedding

/-! # Shared data for the composite cyclic Haar construction

The graph has cyclic index group `ZMod (n*n)` and colors `0,n,2*n,1`.
The marked points are the canonical representatives of `ZMod n`.
All definitions name actual permutations; no orbit property is assumed.
-/

namespace Erdos585.HaarComposite

open Equiv Equiv.Perm

abbrev V (n : ℕ) := ZMod (n * n)

variable (n : ℕ) [NeZero n]

def colors : Finset (V n) := {0, (n : V n), 2 * (n : V n), 1}

def mark (r : ZMod n) : V n := (r.val : V n)

@[simp] lemma mark_val (r : ZMod n) : (mark n r).val = r.val := by
  apply ZMod.val_natCast_of_lt
  exact lt_of_lt_of_le r.val_lt (Nat.le_mul_self n)

lemma mark_injective : Function.Injective (mark n) := by
  intro r s h
  apply ZMod.val_injective
  simpa using congrArg ZMod.val h

def markEmbedding : ZMod n ↪ V n := ⟨mark n, mark_injective n⟩

lemma mem_range_mark_iff_val_lt (x : V n) :
    x ∈ Set.range (mark n) ↔ x.val < n := by
  constructor
  · rintro ⟨r, rfl⟩
    simpa using r.val_lt
  · intro hx
    refine ⟨(x.val : ZMod n), ?_⟩
    apply ZMod.val_injective
    rw [mark_val, ZMod.val_natCast_of_lt hx]

noncomputable def markShift (d : ZMod n) : Perm (V n) :=
  (Equiv.addRight d).viaEmbedding (markEmbedding n)

@[simp] lemma markShift_mark (d r : ZMod n) :
    markShift n d (mark n r) = mark n (r + d) := by
  exact viaEmbedding_apply _ (markEmbedding n) r

lemma markShift_fixed (d : ZMod n) (x : V n)
    (hx : x ∉ Set.range (mark n)) : markShift n d x = x := by
  exact viaEmbedding_apply_of_notMem _ (markEmbedding n) x hx

noncomputable def rho : Perm (V n) := markShift n (-1)

@[simp] lemma rho_mark (r : ZMod n) :
    rho n (mark n r) = mark n (r - 1) := by
  simp [rho, sub_eq_add_neg]

lemma rho_fixed (x : V n) (hx : x ∉ Set.range (mark n)) : rho n x = x :=
  markShift_fixed n (-1) x hx

def residue : V n →+* ZMod n := ZMod.castHom (dvd_mul_right n n) (ZMod n)

@[simp] lemma residue_mark (r : ZMod n) : residue n (mark n r) = r := by
  simp [mark, residue]

@[simp] lemma residue_nat : residue n (n : V n) = 0 := by
  simp [residue]

def matchRed1 : Perm (V n) where
  toFun x := if residue n x = 0 then x else x + (n : V n)
  invFun x := if residue n x = 0 then x else x - (n : V n)
  left_inv x := by
    by_cases hx : residue n x = 0 <;> simp [hx, map_add, map_sub]
  right_inv x := by
    by_cases hx : residue n x = 0 <;> simp [hx, map_add, map_sub]

def redBaseMatching : Perm (V n) where
  toFun x := if residue n x = 0 then x + (n : V n) else x
  invFun x := if residue n x = 0 then x - (n : V n) else x
  left_inv x := by
    by_cases hx : residue n x = 0 <;> simp [hx, map_add, map_sub]
  right_inv x := by
    by_cases hx : residue n x = 0 <;> simp [hx, map_add, map_sub]

noncomputable def matchRed0 : Perm (V n) := redBaseMatching n * markShift n 1

def redBase : Perm (V n) := (matchRed1 n)⁻¹ * redBaseMatching n

noncomputable def red : Perm (V n) := redBase n * markShift n 1

noncomputable def matchBlue0 : Perm (V n) := Equiv.addRight (1 : V n) * rho n

def matchBlue1 : Perm (V n) := Equiv.addRight (2 * (n : V n))

noncomputable def blue : Perm (V n) :=
  Equiv.addRight (1 - 2 * (n : V n)) * rho n

lemma red_successor : (matchRed1 n)⁻¹ * matchRed0 n = red n := by
  simp [matchRed0, red, redBase, mul_assoc]

lemma blue_successor : (matchBlue1 n)⁻¹ * matchBlue0 n = blue n := by
  ext x
  simp [matchBlue1, matchBlue0, blue, sub_eq_add_neg, add_assoc]

end Erdos585.HaarComposite
