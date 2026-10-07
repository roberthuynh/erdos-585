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
import Openmath.Proofs.HaarCompositeBlue

/-!
# The two actual blue orbits for the even composite cyclic Haar construction

The translation is followed between marked cuts. Its even marked order gives
one orbit of all nonzero marks and one separate orbit containing zero.
-/

namespace Erdos585.HaarCompositeEvenBlue

open Equiv Equiv.Perm HaarComposite

variable (n : ℕ) [NeZero n]

private def step : V n := 1 - 2 * (n : V n)
private def rankStep : V n := 1 + 2 * (n : V n)
private def half : ℕ := n / 2
private def pos (r : ZMod n) : ℕ :=
  if r.val < half n then (2 * n + 1) * r.val
  else (2 * n + 1) * (r.val - half n) + half n
private def unrank (t : ℕ) : V n := (t : V n) * step n

omit [NeZero n] in
private lemma two_half (he : Even n) : 2 * half n = n := by
  obtain ⟨a, ha⟩ := he
  dsimp [half]
  omega

omit [NeZero n] in
private lemma nn_zero : (n : V n) * (n : V n) = 0 := by
  rw [← Nat.cast_mul]
  exact ZMod.natCast_self _

omit [NeZero n] in
private lemma step_rank : step n * rankStep n = 1 := by
  calc
    step n * rankStep n = 1 - 4 * ((n : V n) * (n : V n)) := by
      dsimp [step, rankStep]
      ring
    _ = 1 := by rw [nn_zero]; ring

private lemma pos_lt (he : Even n) (r : ZMod n) : pos n r < n * n := by
  have hh := two_half n he
  have hn := NeZero.pos n
  have hr := r.val_lt
  dsimp [pos]
  split_ifs with h
  · have : r.val + 1 ≤ half n := by omega
    nlinarith
  · have hs : r.val - half n + half n = r.val := by omega
    have : r.val - half n + 1 ≤ half n := by omega
    nlinarith

omit [NeZero n] in
private lemma rank_mark (he : Even n) (r : ZMod n) :
    rankStep n * mark n r = (pos n r : V n) := by
  dsimp [pos]
  split_ifs with h
  · simp only [rankStep, mark, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
    ring
  · have hh := two_half n he
    have hs : r.val - half n + half n = r.val := by omega
    have heq : (2 * n + 1) * (r.val - half n) + half n + n * n =
        (2 * n + 1) * r.val := by nlinarith
    have hc := congrArg (fun a : ℕ => (a : V n)) heq
    simp only [Nat.cast_add, ZMod.natCast_self, add_zero] at hc
    rw [Nat.cast_add, hc]
    simp only [rankStep, mark, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
    ring

omit [NeZero n] in
private lemma unrank_pos (he : Even n) (r : ZMod n) :
    unrank n (pos n r) = mark n r := by
  dsimp [unrank]
  rw [← rank_mark n he]
  calc
    rankStep n * mark n r * step n = mark n r * (step n * rankStep n) := by ring
    _ = mark n r := by rw [step_rank]; simp

omit [NeZero n] in
private lemma unrank_succ (t : ℕ) :
    unrank n (t + 1) = unrank n t + step n := by
  simp [unrank, add_mul]

omit [NeZero n] in
private lemma unrank_inj {a b : ℕ} (ha : a < n * n) (hb : b < n * n)
    (he : unrank n a = unrank n b) : a = b := by
  have hh := congrArg (fun x : V n => x * rankStep n) he
  have hc : (a : V n) = (b : V n) := by
    simpa only [unrank, mul_assoc, step_rank, mul_one] using hh
  have hv := congrArg ZMod.val hc
  simpa [ZMod.val_natCast_of_lt ha, ZMod.val_natCast_of_lt hb] using hv

private lemma blue_unmarked (x : V n) (hx : x ∉ Set.range (mark n)) :
    blue n x = x + step n := by
  simp [blue, mul_apply, rho_fixed n x hx, step]

private lemma no_mark_between (he : Even n) (a : ZMod n) (b : ℕ)
    (hb : b ≤ n * n)
    (hgap : ∀ r : ZMod n, ¬ (pos n a < pos n r ∧ pos n r < b))
    {t : ℕ} (ha : pos n a < t) (ht : t < b) :
    unrank n t ∉ Set.range (mark n) := by
  rintro ⟨r, hr⟩
  have ht' : t < n * n := lt_of_lt_of_le ht hb
  have htr : t = pos n r := by
    apply unrank_inj n ht' (pos_lt n he r)
    rw [unrank_pos n he]
    exact hr.symm
  exact hgap r (by omega)

private lemma return_connection (he : Even n) (a b : ZMod n) (t : ℕ)
    (hat : pos n a < t) (ht : t ≤ n * n) (hend : unrank n t = mark n b)
    (hgap : ∀ r : ZMod n, ¬ (pos n a < pos n r ∧ pos n r < t)) :
    (blue n).SameCycle (mark n (a + 1)) (mark n b) := by
  have hfirst : blue n (mark n (a + 1)) = unrank n (pos n a + 1) := by
    rw [unrank_succ, unrank_pos n he]
    simp [blue, mul_apply, rho_mark, step]
  have hs : (blue n).SameCycle (mark n (a + 1)) (unrank n (pos n a + 1)) := by
    rw [← hfirst]
    exact (SameCycle.refl (blue n) _).apply_right
  have hp : (blue n).SameCycle (unrank n (pos n a + 1)) (unrank n t) := by
    apply sameCycle_interval (blue n) (unrank n) (by omega)
    intro j hj hjt
    rw [blue_unmarked n _ (no_mark_between n he a t ht hgap (by omega) hjt)]
    exact (unrank_succ n j).symm
  rw [hend] at hp
  exact hs.trans hp

private lemma pos_low (he : Even n) (a : ℕ) (ha : a < half n) :
    pos n (a : ZMod n) = (2 * n + 1) * a := by
  have hh := two_half n he
  have hn := NeZero.pos n
  have ha' : a < n := by omega
  simp only [pos, ZMod.val_natCast_of_lt ha', if_pos ha]

omit [NeZero n] in
private lemma pos_high (he : Even n) (a : ℕ) (ha : a < half n) :
    pos n ((a + half n : ℕ) : ZMod n) = (2 * n + 1) * a + half n := by
  have hh := two_half n he
  have ha' : a + half n < n := by omega
  have hnot : ¬ a + half n < half n := by omega
  simp only [pos, ZMod.val_natCast_of_lt ha', if_neg hnot, Nat.add_sub_cancel]

private lemma low_high (he : Even n) (a : ℕ) (ha : a < half n) :
    (blue n).SameCycle (mark n ((a + 1 : ℕ) : ZMod n))
      (mark n ((a + half n : ℕ) : ZMod n)) := by
  have hh := two_half n he
  have hn := NeZero.pos n
  have hp : pos n (a : ZMod n) < pos n ((a + half n : ℕ) : ZMod n) := by
    rw [pos_low n he a ha, pos_high n he a ha]
    omega
  have hg : ∀ q : ZMod n, ¬ (pos n (a : ZMod n) < pos n q ∧
      pos n q < pos n ((a + half n : ℕ) : ZMod n)) := by
    intro q
    rw [pos_low n he a ha, pos_high n he a ha]
    by_cases hq : q.val < half n
    · rw [pos, if_pos hq]
      intro h
      by_cases hqa : q.val ≤ a
      · have := Nat.mul_le_mul_left (2 * n + 1) hqa
        omega
      · have hqa' : a + 1 ≤ q.val := by omega
        have := Nat.mul_le_mul_left (2 * n + 1) hqa'
        nlinarith
    · rw [pos, if_neg hq]
      intro h
      by_cases hqa : a ≤ q.val - half n
      · have := Nat.mul_le_mul_left (2 * n + 1) hqa
        omega
      · have hqa' : q.val - half n + 1 ≤ a := by omega
        have := Nat.mul_le_mul_left (2 * n + 1) hqa'
        nlinarith
  have hc := return_connection n he (a : ZMod n) ((a + half n : ℕ) : ZMod n)
    (pos n ((a + half n : ℕ) : ZMod n)) hp (pos_lt n he _).le
    (unrank_pos n he _) hg
  simpa only [Nat.cast_add, Nat.cast_one] using hc

private lemma high_low (he : Even n) (a : ℕ) (ha : a + 1 < half n) :
    (blue n).SameCycle (mark n ((a + half n + 1 : ℕ) : ZMod n))
      (mark n ((a + 1 : ℕ) : ZMod n)) := by
  have hh := two_half n he
  have hn := NeZero.pos n
  have ha0 : a < half n := by omega
  have hp : pos n ((a + half n : ℕ) : ZMod n) < pos n ((a + 1 : ℕ) : ZMod n) := by
    rw [pos_high n he a ha0, pos_low n he (a + 1) ha]
    nlinarith
  have hg : ∀ q : ZMod n, ¬ (pos n ((a + half n : ℕ) : ZMod n) < pos n q ∧
      pos n q < pos n ((a + 1 : ℕ) : ZMod n)) := by
    intro q
    rw [pos_high n he a ha0, pos_low n he (a + 1) ha]
    by_cases hq : q.val < half n
    · rw [pos, if_pos hq]
      intro h
      by_cases hqa : q.val ≤ a
      · have := Nat.mul_le_mul_left (2 * n + 1) hqa
        omega
      · have hqa' : a + 1 ≤ q.val := by omega
        have := Nat.mul_le_mul_left (2 * n + 1) hqa'
        omega
    · rw [pos, if_neg hq]
      intro h
      by_cases hqa : q.val - half n ≤ a
      · have := Nat.mul_le_mul_left (2 * n + 1) hqa
        omega
      · have hqa' : a + 1 ≤ q.val - half n := by omega
        have := Nat.mul_le_mul_left (2 * n + 1) hqa'
        omega
  have hc := return_connection n he ((a + half n : ℕ) : ZMod n)
    ((a + 1 : ℕ) : ZMod n) (pos n ((a + 1 : ℕ) : ZMod n)) hp
    (pos_lt n he _).le (unrank_pos n he _) hg
  simpa only [Nat.cast_add, Nat.cast_one] using hc

private lemma high_connected (he : Even n) (a : ℕ) (ha : a < half n) :
    (blue n).SameCycle (mark n ((a + half n : ℕ) : ZMod n))
      (mark n ((half n : ℕ) : ZMod n)) := by
  induction a with
  | zero => simpa using SameCycle.refl (blue n) (mark n ((half n : ℕ) : ZMod n))
  | succ a ih =>
    have ha0 : a < half n := by omega
    have hc := (high_low n he a ha).trans ((low_high n he a ha0).trans (ih ha0))
    simpa only [Nat.succ_eq_add_one, Nat.add_right_comm] using hc

/-- Every nonzero marked point belongs to the actual blue orbit of mark one. -/
theorem blue_mark_one (hn : 4 ≤ n) (he : Even n) (r : ZMod n) (hr : r ≠ 0) :
    (blue n).SameCycle (mark n r) (mark n (1 : ZMod n)) := by
  have hh := two_half n he
  have hh0 : 0 < half n := by omega
  have hbase := (low_high n he 0 hh0).symm
  simp only [zero_add, Nat.cast_one] at hbase
  have hr0 : 0 < r.val := by
    by_contra h
    have hv : r.val = 0 := by omega
    apply hr
    apply ZMod.val_injective
    simpa using hv
  have hrv := r.val_lt
  by_cases hl : r.val < half n
  · have ha : r.val - 1 < half n := by omega
    have hs : r.val - 1 + 1 = r.val := by omega
    have hc := (low_high n he (r.val - 1) ha).trans
      ((high_connected n he (r.val - 1) ha).trans hbase)
    simpa only [hs, ZMod.natCast_zmod_val] using hc
  · have ha : r.val - half n < half n := by omega
    have hs : r.val - half n + half n = r.val := by omega
    have hc := (high_connected n he (r.val - half n) ha).trans hbase
    simpa only [hs, ZMod.natCast_zmod_val] using hc

omit [NeZero n] in
private lemma translation_pow (d : V n) (k : ℕ) (x : V n) :
    (Equiv.addRight d ^ k) x = x + (k : V n) * d := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_apply, ih]
    change x + (k : V n) * d + d = _
    simp [Nat.cast_add, Nat.cast_one, add_mul, add_assoc]

private lemma reaches_mark (x : V n) : ∃ r : ZMod n, (blue n).SameCycle x (mark n r) := by
  let t : V n := -x * rankStep n
  have ht : (Equiv.addRight (step n) ^ t.val) x = mark n (0 : ZMod n) := by
    rw [translation_pow]
    simp only [ZMod.natCast_zmod_val]
    dsimp [t]
    have hh : rankStep n * step n = 1 := by rw [mul_comm, step_rank]
    rw [mul_assoc, hh]
    simp [mark]
  apply reaches_some_mark (blue n) (Equiv.addRight (step n)) (mark n) _ t.val ⟨0, ht⟩
  intro y hy
  apply blue_unmarked n y
  rintro ⟨r, hr⟩
  exact hy r hr.symm

/-- Every point of the actual blue permutation is in one of its two marked orbits. -/
theorem blue_partition (hn : 4 ≤ n) (he : Even n) (x : V n) :
    (blue n).SameCycle x 0 ∨ (blue n).SameCycle x (mark n (1 : ZMod n)) := by
  obtain ⟨r, hr⟩ := reaches_mark n x
  by_cases hzero : r = 0
  · left
    simpa [hzero, mark] using hr
  · exact Or.inr (hr.trans (blue_mark_one n hn he r hzero))

private def lastMark : ZMod n := ((n - 1 : ℕ) : ZMod n)
private def lastPos : ℕ := pos n (lastMark n)
private def small (x : V n) : Prop :=
  x = 0 ∨ ∃ t : ℕ, lastPos n < t ∧ t < n * n ∧ unrank n t = x

private lemma lastMark_add_one : lastMark n + 1 = 0 := by
  have hn := NeZero.pos n
  have hh : n - 1 + 1 = n := by omega
  calc
    lastMark n + 1 = ((n - 1 + 1 : ℕ) : ZMod n) := by simp [lastMark]
    _ = 0 := by rw [hh]; exact ZMod.natCast_self n

omit [NeZero n] in
private lemma lastPos_eq (hn : 4 ≤ n) (he : Even n) :
    lastPos n = (2 * n + 1) * (half n - 1) + half n := by
  have hh := two_half n he
  have ha : half n - 1 < half n := by omega
  have hs : half n - 1 + half n = n - 1 := by omega
  dsimp [lastPos, lastMark]
  rw [← hs]
  exact pos_high n he (half n - 1) ha

omit [NeZero n] in
private lemma lastPos_add (hn : 4 ≤ n) (he : Even n) :
    lastPos n + n + 1 = n * n := by
  rw [lastPos_eq n hn he]
  have hh := two_half n he
  have hs : half n - 1 + 1 = half n := by omega
  nlinarith

private lemma pos_le_last (hn : 4 ≤ n) (he : Even n) (r : ZMod n) :
    pos n r ≤ lastPos n := by
  have hh := two_half n he
  have hr := r.val_lt
  rw [lastPos_eq n hn he]
  by_cases hl : r.val < half n
  · rw [pos, if_pos hl]
    have hle : r.val ≤ half n - 1 := by omega
    have := Nat.mul_le_mul_left (2 * n + 1) hle
    omega
  · rw [pos, if_neg hl]
    have hle : r.val - half n ≤ half n - 1 := by omega
    have := Nat.mul_le_mul_left (2 * n + 1) hle
    omega

private lemma tail_unmarked (hn : 4 ≤ n) (he : Even n) (t : ℕ)
    (hlt : lastPos n < t) (ht : t < n * n) :
    unrank n t ∉ Set.range (mark n) := by
  rintro ⟨r, hr⟩
  have heq : t = pos n r := by
    apply unrank_inj n ht (pos_lt n he r)
    rw [unrank_pos n he]
    exact hr.symm
  have := pos_le_last n hn he r
  omega

omit [NeZero n] in
private lemma unrank_full : unrank n (n * n) = 0 := by
  simp [unrank]

private lemma blue_zero (he : Even n) :
    blue n 0 = unrank n (lastPos n + 1) := by
  have hzero : mark n (lastMark n + 1) = 0 := by rw [lastMark_add_one]; simp [mark]
  rw [← hzero, unrank_succ, show lastPos n = pos n (lastMark n) from rfl, unrank_pos n he]
  simp [blue, mul_apply, rho_mark, step]

private lemma small_step (hn : 4 ≤ n) (he : Even n) {x : V n}
    (hx : small n x) : small n (blue n x) := by
  rcases hx with rfl | ⟨t, hlt, ht, rfl⟩
  · rw [blue_zero n he]
    right
    refine ⟨lastPos n + 1, by omega, ?_, rfl⟩
    have := lastPos_add n hn he
    omega
  · rw [blue_unmarked n _ (tail_unmarked n hn he t hlt ht), ← unrank_succ]
    by_cases hnext : t + 1 < n * n
    · exact Or.inr ⟨t + 1, by omega, hnext, rfl⟩
    · left
      have heq : t + 1 = n * n := by omega
      rw [heq, unrank_full]

private lemma mark_not_small (hn : 4 ≤ n) (he : Even n) (r : ZMod n) (hr : r ≠ 0) :
    ¬ small n (mark n r) := by
  rintro (hz | ⟨t, hlt, ht, htr⟩)
  · apply hr
    have hm : mark n r = mark n (0 : ZMod n) := by simpa [mark] using hz
    exact mark_injective n hm
  · exact tail_unmarked n hn he t hlt ht ⟨r, htr.symm⟩

/-- The zero orbit is distinct from the actual blue orbit of mark one. -/
theorem blue_zero_not_one (hn : 4 ≤ n) (he : Even n) :
    ¬ (blue n).SameCycle 0 (mark n (1 : ZMod n)) := by
  intro h
  obtain ⟨k, hk⟩ := h.exists_nat_pow_eq
  have hpow : ∀ j : ℕ, small n ((blue n ^ j) 0) := by
    intro j
    induction j with
    | zero => exact Or.inl (by simp)
    | succ j ih =>
      rw [pow_succ', mul_apply]
      exact small_step n hn he ih
  have hone : (1 : ZMod n) ≠ 0 := by
    intro hz
    have hv := congrArg ZMod.val hz
    rw [ZMod.val_one_eq_one_mod, ZMod.val_zero, Nat.mod_eq_of_lt (by omega : 1 < n)] at hv
    omega
  exact mark_not_small n hn he 1 hone (by simpa [hk] using hpow k)

private lemma tail_to_zero (hn : 4 ≤ n) (he : Even n) (t : ℕ)
    (hlt : lastPos n < t) (ht : t ≤ n * n) :
    (blue n).SameCycle (unrank n t) 0 := by
  have hp : (blue n).SameCycle (unrank n t) (unrank n (n * n)) := by
    apply sameCycle_interval (blue n) (unrank n) ht
    intro j hj hjn
    rw [blue_unmarked n _ (tail_unmarked n hn he j (by omega) hjn)]
    exact (unrank_succ n j).symm
  simpa only [unrank_full] using hp

omit [NeZero n] in
private lemma half_step (he : Even n) : (half n : V n) * step n = (half n : V n) := by
  have hc : (2 : V n) * (half n : V n) = (n : V n) := by
    simpa using congrArg (fun a : ℕ => (a : V n)) (two_half n he)
  calc
    (half n : V n) * step n = (half n : V n) - (n : V n) * (2 * (half n : V n)) := by
      dsimp [step]
      ring
    _ = (half n : V n) := by rw [hc, nn_zero]; simp

/-- The left index of the exchanged small-component edge lies in the zero orbit. -/
theorem blue_special_zero (hn : 4 ≤ n) (he : Even n) :
    (blue n).SameCycle (((n + n / 2 - 1 : ℕ) : V n)) 0 := by
  have hh := two_half n he
  have hl := lastPos_add n hn he
  have hp := tail_to_zero n hn he (lastPos n + half n) (by omega) (by omega)
  have hm : mark n (lastMark n) = ((n - 1 : ℕ) : V n) := by
    have hpred : n - 1 < n := by omega
    simp [mark, lastMark, ZMod.val_natCast_of_lt hpred]
  have hx : unrank n (lastPos n + half n) = ((n + half n - 1 : ℕ) : V n) := by
    calc
      unrank n (lastPos n + half n) =
          unrank n (lastPos n) + (half n : V n) * step n := by
        simp [unrank, add_mul]
      _ = ((n - 1 : ℕ) : V n) + (half n : V n) := by
        rw [show unrank n (lastPos n) = mark n (lastMark n) from unrank_pos n he _, hm,
          half_step n he]
      _ = ((n + half n - 1 : ℕ) : V n) := by
        rw [← Nat.cast_add]
        congr 1
        omega
  rw [hx] at hp
  simpa only [half] using hp

end Erdos585.HaarCompositeEvenBlue
