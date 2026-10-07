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
import Openmath.Proofs.HaarCompositeDefs
import Openmath.Proofs.HaarCompositeBlue
import Openmath.Proofs.HaarPair

/-! # Two Hamilton cycles in the composite cyclic Haar family

The primary parameter is every odd `n ≥ 3`; the index group is `ZMod (n*n)`
and the four colors are `0,n,2*n,1`. The construction is explicit.
-/

namespace Erdos585.HaarComposite

open Equiv Equiv.Perm

variable (n : ℕ) [NeZero n]

omit [NeZero n] in
lemma redBase_apply (x : V n) :
    redBase n x = if residue n x = 0 then x + (n : V n) else x - (n : V n) := by
  by_cases hx : residue n x = 0 <;>
    simp [redBase, matchRed1, redBaseMatching, mul_apply, hx]

omit [NeZero n] in
@[simp] lemma residue_redBase (x : V n) : residue n (redBase n x) = residue n x := by
  rw [redBase_apply]
  split <;> simp

omit [NeZero n] in
lemma redBase_pow (k : ℕ) (x : V n) :
    (redBase n ^ k) x =
      if residue n x = 0 then x + (k : V n) * (n : V n)
      else x - (k : V n) * (n : V n) := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, mul_apply, ih]
    simp only [residue_redBase]
    rw [redBase_apply]
    split <;> simp only [Nat.cast_add, Nat.cast_one] <;> ring

omit [NeZero n] in
@[simp] lemma residue_redBase_pow (k : ℕ) (x : V n) :
    residue n ((redBase n ^ k) x) = residue n x := by
  induction k with
  | zero => simp
  | succ k ih => simpa [pow_succ', mul_apply] using ih

lemma residue_val (x : V n) : (residue n x).val = x.val % n := by
  change (ZMod.cast x : ZMod n).val = _
  rw [ZMod.cast_eq_val, ZMod.val_natCast]

lemma quotient_coordinates (x : V n) :
    mark n (residue n x) + (x.val / n : V n) * (n : V n) = x := by
  rw [mark, residue_val, ← Nat.cast_mul, ← Nat.cast_add]
  simpa [Nat.mul_comm] using congrArg (fun k : ℕ => (k : V n)) (Nat.mod_add_div x.val n)

lemma redBase_cover (x : V n) : ∃ r, (redBase n).SameCycle x (mark n r) := by
  refine ⟨residue n x, ?_⟩
  have hc := quotient_coordinates n x
  by_cases hx : residue n x = 0
  · have he : (redBase n ^ (x.val / n)) (mark n (residue n x)) = x := by
      rw [redBase_pow, residue_mark, if_pos hx]
      exact hc
    simpa only [he] using
      ((SameCycle.refl (redBase n) (mark n (residue n x))).pow_left
        (n := x.val / n))
  · have he : (redBase n ^ (x.val / n)) x = mark n (residue n x) := by
      rw [redBase_pow, if_neg hx]
      exact sub_eq_iff_eq_add.mpr (by simpa [add_comm] using hc.symm)
    rw [← he]
    exact (SameCycle.refl _ _).pow_right

lemma redBase_unique (r s : ZMod n)
    (h : (redBase n).SameCycle (mark n r) (mark n s)) : r = s := by
  obtain ⟨k, hk⟩ := h.exists_nat_pow_eq
  have hh := congrArg (residue n) hk
  simpa using hh

omit [NeZero n] in
lemma addRight_one_pow (k : ℕ) (r : ZMod n) :
    (Equiv.addRight (1 : ZMod n) ^ k) r = r + (k : ZMod n) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_apply]
    simp [add_assoc]

lemma addRight_one_isCycleOn : (Equiv.addRight (1 : ZMod n)).IsCycleOn Set.univ := by
  refine ⟨(Equiv.addRight (1 : ZMod n)).bijOn (fun _ => Iff.rfl), ?_⟩
  intro r _ s _
  have he : (Equiv.addRight (1 : ZMod n) ^ (s-r).val) r = s := by
    rw [addRight_one_pow, ZMod.natCast_zmod_val]
    abel
  rw [← he]
  exact (SameCycle.refl _ _).pow_right

theorem red_isCycleOn : (red n).IsCycleOn Set.univ := by
  apply HaarCycle.splice_isCycleOn (redBase n) (red n)
    (Equiv.addRight (1 : ZMod n)) (mark n)
  · exact redBase_cover n
  · exact redBase_unique n
  · intro x hx
    have hm : x ∉ Set.range (mark n) := by
      rintro ⟨r, rfl⟩
      exact hx r rfl
    simp [red, mul_apply, markShift_fixed n 1 x hm]
  · intro r
    simp [red, mul_apply]
  · exact addRight_one_isCycleOn n

lemma redBaseMatching_mark_succ (r : ZMod n) :
    redBaseMatching n (mark n (r + 1)) = mark n r + 1 := by
  have hcast : ((r.val + 1 : ℕ) : ZMod n) = r + 1 := by simp
  by_cases he : r.val + 1 = n
  · have hz : r + 1 = 0 := by rw [← hcast, he]; exact ZMod.natCast_self n
    have hc : mark n r + 1 = (n : V n) := by
      rw [mark, ← Nat.cast_one, ← Nat.cast_add, he]
    rw [hc, hz]
    simp [redBaseMatching, mark]
  · have hlt : r.val + 1 < n := by have := r.val_lt; omega
    have hv : (r + 1).val = r.val + 1 := by
      rw [← hcast, ZMod.val_natCast_of_lt hlt]
    have hz : r + 1 ≠ 0 := by
      intro hh
      have := congrArg ZMod.val hh
      rw [hv, ZMod.val_zero] at this
      omega
    simp only [redBaseMatching, Equiv.coe_fn_mk, residue_mark, if_neg hz]
    simp [mark, hv]

@[simp] lemma matchRed0_mark (r : ZMod n) :
    matchRed0 n (mark n r) = mark n r + 1 := by
  simp only [matchRed0, mul_apply, markShift_mark]
  exact redBaseMatching_mark_succ n r

@[simp] lemma matchBlue0_mark (r : ZMod n) :
    matchBlue0 n (mark n r) = redBaseMatching n (mark n r) := by
  have hh := redBaseMatching_mark_succ n (r - 1)
  simpa [matchBlue0, mul_apply] using hh.symm

lemma matchRed0_fixed (x : V n) (hx : x ∉ Set.range (mark n)) :
    matchRed0 n x = redBaseMatching n x := by
  simp [matchRed0, mul_apply, markShift_fixed n 1 x hx]

lemma matchBlue0_fixed (x : V n) (hx : x ∉ Set.range (mark n)) :
    matchBlue0 n x = x + 1 := by
  simp [matchBlue0, mul_apply, rho_fixed n x hx]

omit [NeZero n] in
lemma color_distinct (hn : 3 ≤ n) :
    (0 : V n) ≠ 1 ∧ (0 : V n) ≠ (n : V n) ∧
    (0 : V n) ≠ 2 * (n : V n) ∧
    (1 : V n) ≠ (n : V n) ∧ (1 : V n) ≠ 2 * (n : V n) ∧
    (n : V n) ≠ 2 * (n : V n) := by
  have h0 : (0 : ℕ) < n * n := by positivity
  have h1 : (1 : ℕ) < n * n := by nlinarith
  have hn' : n < n * n := by nlinarith
  have h2 : 2 * n < n * n := by nlinarith
  have hcast : ∀ a b : ℕ, a < n*n → b < n*n → a ≠ b →
      (a : V n) ≠ (b : V n) := by
    intro a b ha hb hab hh
    apply hab
    have hv := congrArg ZMod.val hh
    simpa only [ZMod.val_natCast_of_lt ha, ZMod.val_natCast_of_lt hb] using hv
  have h01 := hcast 0 1 h0 h1 (by omega)
  have h0n := hcast 0 n h0 hn' (by omega)
  have h02 := hcast 0 (2*n) h0 h2 (by omega)
  have h1n := hcast 1 n h1 hn' (by omega)
  have h12 := hcast 1 (2*n) h1 h2 (by omega)
  have hn2 := hcast n (2*n) hn' h2 (by omega)
  simpa only [Nat.cast_zero, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat]
    using And.intro h01 (And.intro h0n (And.intro h02 (And.intro h1n (And.intro h12 hn2))))

lemma matching_facts (hn : 3 ≤ n) (x : V n) :
    (matchRed0 n x - x ∈ colors n ∧ matchRed1 n x - x ∈ colors n ∧
      matchBlue0 n x - x ∈ colors n ∧ matchBlue1 n x - x ∈ colors n) ∧
    (matchRed0 n x ≠ matchRed1 n x ∧ matchBlue0 n x ≠ matchBlue1 n x ∧
      matchRed0 n x ≠ matchBlue0 n x ∧ matchRed0 n x ≠ matchBlue1 n x ∧
      matchRed1 n x ≠ matchBlue0 n x ∧ matchRed1 n x ≠ matchBlue1 n x) := by
  obtain ⟨h01, h0n, h02, h1n, h12, hn2⟩ := color_distinct n hn
  by_cases hx : x ∈ Set.range (mark n)
  · obtain ⟨r, rfl⟩ := hx
    rw [matchRed0_mark, matchBlue0_mark]
    by_cases hr : r = 0
    · subst r
      simp [matchRed1, redBaseMatching,
        matchBlue1, mark, colors, h01, h0n, h02, h1n, h12, hn2,
        h01.symm, h0n.symm, h02.symm, h1n.symm, h12.symm, hn2.symm]
    · simp [matchRed1, redBaseMatching,
        matchBlue1, hr, colors, h01, h0n, h02, h1n, h12, hn2,
        h01.symm, h0n.symm, h02.symm, h1n.symm, h12.symm, hn2.symm]
  · rw [matchRed0_fixed n x hx, matchBlue0_fixed n x hx]
    by_cases hr : residue n x = 0
    · simp [matchRed1, redBaseMatching, matchBlue1, hr, colors,
        h01, h0n, h02, h1n, h12, hn2,
        h01.symm, h0n.symm, h02.symm, h1n.symm, h12.symm, hn2.symm]
    · simp [matchRed1, redBaseMatching, matchBlue1, hr, colors,
        h01, h0n, h02, h1n, h12, hn2,
        h01.symm, h0n.symm, h02.symm, h1n.symm, h12.symm, hn2.symm]

omit [NeZero n] in
/-- Every odd parameter at least three gives two actual edge-disjoint simple
cycles with the same vertex set in the specified composite cyclic Haar graph. -/
theorem hasPair (hn : 3 ≤ n) (ho : Odd n) : HasPairF (Haar.graph (colors n)) := by
  let : NeZero n := ⟨by omega⟩
  refine HaarPair.hasPair_of_matching_permutations (Haar.graph (colors n))
    (matchRed0 n) (matchRed1 n) (matchBlue0 n) (matchBlue1 n)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (0 : V n)
  · intro x
    exact (Haar.graph_cross _ _ _).mpr (matching_facts n hn x).1.1
  · intro x
    exact (Haar.graph_cross _ _ _).mpr (matching_facts n hn x).1.2.1
  · intro x
    exact (Haar.graph_cross _ _ _).mpr (matching_facts n hn x).1.2.2.1
  · intro x
    exact (Haar.graph_cross _ _ _).mpr (matching_facts n hn x).1.2.2.2
  · intro x
    exact (matching_facts n hn x).2.1
  · intro x
    exact (matching_facts n hn x).2.2.1
  · intro x
    exact (matching_facts n hn x).2.2.2
  · rw [red_successor]
    exact red_isCycleOn n
  · rw [blue_successor]
    exact blue_isCycleOn n hn ho

omit [NeZero n] in
/-- The same uniform construction in the upstream predicate, retaining
actual simple walks, support equality, and edge disjointness. -/
theorem hasTwoEdgeDisjointCyclesSameVertexSet (hn : 3 ≤ n) (ho : Odd n) :
    HasTwoEdgeDisjointCyclesSameVertexSet (Haar.graph (colors n)) :=
  (hasPairF_iff _).mp (hasPair n hn ho)

end Erdos585.HaarComposite
