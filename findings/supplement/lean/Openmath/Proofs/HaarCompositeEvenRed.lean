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
import Openmath.Proofs.HaarCompositeEvenDefs
import Openmath.Proofs.MatchingCutPaths

/-!
# The surviving red B-to-D path in the even composite Haar exchange

The base matching path is localized to its actual residue class. Every one
of its edges survives the red deletions; no connectivity of the final factor
is assumed here.
-/

namespace Erdos585.HaarCompositeEvenRed

open SimpleGraph Equiv Equiv.Perm HaarComposite HaarCompositeEven

variable (n : ℕ) [NeZero n]

private def z : V n := cutIndex n + 1
private def base : SimpleGraph (W n) :=
  MatchingCutPaths.cutFactor (Equiv.refl (V n)) (Equiv.addRight (n : V n)) (z n) (z n)

omit [NeZero n] in
private lemma z_nat (hn : 4 ≤ n) : z n = ((n / 2 : ℕ) : V n) := by
  have hh : n / 2 - 1 + 1 = n / 2 := by omega
  simpa [z, cutIndex] using congrArg (fun j : ℕ => (j : V n)) hh

omit [NeZero n] in
private lemma z_mark (hn : 4 ≤ n) : mark n ((n / 2 : ℕ) : ZMod n) = z n := by
  have hh : n / 2 < n := by omega
  rw [z_nat n hn]
  simp [mark, ZMod.val_natCast_of_lt hh]

omit [NeZero n] in
private lemma residue_z (hn : 4 ≤ n) : residue n (z n) = ((n / 2 : ℕ) : ZMod n) := by
  rw [z_nat n hn]
  exact map_natCast _ _

omit [NeZero n] in
private lemma residue_z_ne_zero (hn : 4 ≤ n) : residue n (z n) ≠ 0 := by
  intro hh
  have hv := congrArg ZMod.val hh
  rw [residue_z n hn, ZMod.val_natCast_of_lt (by omega : n / 2 < n), ZMod.val_zero] at hv
  omega

omit [NeZero n] in
private lemma residue_cut_ne_z (hn : 4 ≤ n) : residue n (cutIndex n) ≠ residue n (z n) := by
  intro hh
  have hv := congrArg ZMod.val hh
  have hr : residue n (cutIndex n) = ((n / 2 - 1 : ℕ) : ZMod n) := map_natCast _ _
  rw [hr, residue_z n hn,
    ZMod.val_natCast_of_lt (by omega : n / 2 - 1 < n),
    ZMod.val_natCast_of_lt (by omega : n / 2 < n)] at hv
  omega

omit [NeZero n] in
private lemma base_factor {u v : W n} (h : (base n).Adj u v) :
    (HaarPair.matchingFactor (Equiv.refl (V n)) (Equiv.addRight (n : V n))).Adj u v :=
  h.1

omit [NeZero n] in
private lemma base_residue {u v : W n} (h : (base n).Adj u v) :
    residue n u.1 = residue n v.1 := by
  obtain ⟨x, bx⟩ := u
  obtain ⟨y, by_⟩ := v
  have hf := base_factor n h
  cases bx <;> cases by_
  · exact (HaarPair.factor_same _ _ x y false hf).elim
  · rcases (HaarPair.factor_cross _ _ x y).mp hf with hy | hy
    · simpa using congrArg (residue n) hy.symm
    · simpa [map_add] using congrArg (residue n) hy.symm
  · rcases (HaarPair.factor_cross _ _ y x).mp hf.symm with hx | hx
    · simpa using congrArg (residue n) hx
    · simpa [map_add] using congrArg (residue n) hx
  · exact (HaarPair.factor_same _ _ x y true hf).elim

omit [NeZero n] in
private lemma base_cross_left_ne (x y : V n) (h : (base n).Adj (x, false) (y, true)) :
    x ≠ z n := by
  intro hx
  subst x
  have hf := (HaarPair.factor_cross _ _ _ _).mp (base_factor n h)
  have hnot := h.2
  apply hnot
  rcases hf with hf | hf
  · apply Or.inl
    simp [edge_adj, hf]
  · apply Or.inr
    simp [edge_adj, hf]

private lemma base_cross_red (hn : 4 ≤ n) (x y : V n)
    (h : (base n).Adj (x, false) (y, true))
    (hres : residue n x = residue n (z n)) :
    (HaarCompositeEven.red n).Adj (x, false) (y, true) := by
  have hxz := base_cross_left_ne n x y h
  have hxn : x ∉ Set.range (mark n) := by
    rintro ⟨j, hj⟩
    have hjr : j = ((n / 2 : ℕ) : ZMod n) := by
      have hr := congrArg (residue n) hj
      rw [residue_mark, hres, residue_z n hn] at hr
      exact hr
    apply hxz
    rw [← hj, hjr, z_mark n hn]
  have hx0 : residue n x ≠ 0 := by rw [hres]; exact residue_z_ne_zero n hn
  have hxcut : x ≠ cutIndex n := by
    intro heq
    exact residue_cut_ne_z n hn (by simpa [heq] using hres)
  have hxe : x ≠ cutIndex n + (n : V n) := by
    intro heq
    exact residue_cut_ne_z n hn (by simpa [heq, map_add] using hres)
  have hm0 : matchRed0 n x = x := by
    rw [matchRed0_fixed n x hxn]
    simp [redBaseMatching, hx0]
  have hm1 : matchRed1 n x = x + (n : V n) := by
    simp [matchRed1, hx0]
  have hf := (HaarPair.factor_cross _ _ x y).mp (base_factor n h)
  have hold : (oldRed n).Adj (x, false) (y, true) := by
    apply (HaarPair.factor_cross _ _ x y).mpr
    simpa [hm0, hm1] using hf
  have hcuts : ¬ (redCuts n).Adj (x, false) (y, true) := by
    have hxz' : x ≠ cutIndex n + 1 := hxz
    simp [redCuts, edge_adj, a, HaarCompositeEven.b, c, d, e, f, hxcut, hxe, hxz']
  exact Or.inl ⟨hold, hcuts⟩

private lemma base_edge_red (hn : 4 ≤ n) {u v : W n}
    (h : (base n).Adj u v) (hu : residue n u.1 = residue n (z n)) :
    (HaarCompositeEven.red n).Adj u v := by
  obtain ⟨x, bx⟩ := u
  obtain ⟨y, by_⟩ := v
  cases bx <;> cases by_
  · exact (HaarPair.factor_same _ _ x y false (base_factor n h)).elim
  · exact base_cross_red n hn x y h hu
  · apply Adj.symm
    exact base_cross_red n hn y x h.symm ((base_residue n h).symm.trans hu)
  · exact (HaarPair.factor_same _ _ x y true (base_factor n h)).elim

private lemma base_walk_red (hn : 4 ≤ n) {u v : W n} (p : (base n).Walk u v)
    (hu : residue n u.1 = residue n (z n)) :
    (HaarCompositeEven.red n).Reachable u v := by
  induction p with
  | nil => exact Reachable.refl _
  | @cons u v w huv p ih =>
    have hv : residue n v.1 = residue n (z n) := (base_residue n huv).symm.trans hu
    exact (base_edge_red n hn huv hu).reachable.trans (ih hv)

/-- The B-to-D segment survives in the actual exchanged red factor. -/
theorem b_reachable_d (hn : 4 ≤ n) (_he : Even n) :
    (HaarCompositeEven.red n).Reachable (b n) (d n) := by
  have hn0 : (n : V n) ≠ 0 := (color_distinct n (by omega)).2.1.symm
  have hne : ∀ x : V n, Equiv.refl (V n) x ≠ Equiv.addRight (n : V n) x := by
    intro x hh
    apply hn0
    change x = x + (n : V n) at hh
    linear_combination -hh
  have hc : ((Equiv.addRight (n : V n))⁻¹ * Equiv.refl (V n)).SameCycle (z n) (z n) :=
    SameCycle.refl _ _
  have hp := MatchingCutPaths.right_reachable (Equiv.refl (V n))
    (Equiv.addRight (n : V n)) hne (z n) (z n) hc
  obtain ⟨p⟩ := hp
  have hr := base_walk_red n hn p rfl
  exact hr

end Erdos585.HaarCompositeEvenRed
