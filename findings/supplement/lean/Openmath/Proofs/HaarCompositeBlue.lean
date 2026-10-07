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
import Openmath.Proofs.HaarCompositeDefs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# The blue orbit in the composite cyclic Haar construction

This file proves the actual successor orbit by following the intervals
between marked cuts of a cyclic translation. It is a supporting
component of the odd composite cyclic Haar family.
-/

namespace Erdos585.HaarComposite

open Equiv Equiv.Perm

/-- A finite sequence of actual successor edges stays in one orbit. -/
lemma sameCycle_interval {A : Type*} (P : Perm A) (v : ℕ → A)
    {a b : ℕ} (hab : a ≤ b)
    (hstep : ∀ j, a ≤ j → j < b → P (v j) = v (j + 1)) :
    P.SameCycle (v a) (v b) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hab
  induction k with
  | zero => exact SameCycle.refl P _
  | succ k ih =>
    have hp : P.SameCycle (v a) (v (a + k)) :=
      ih (by omega) (fun j hj hjk => hstep j hj (by omega))
    have hs : P.SameCycle (v (a + k)) (v (a + k + 1)) := by
      rw [← hstep (a + k) (by omega) (by omega)]
      exact (SameCycle.refl P _).apply_right
    simpa [Nat.add_assoc] using hp.trans hs

/-- If a permutation follows a full cycle off the marked set, every
point reaches some mark in its own actual orbit. -/
lemma reaches_some_mark {A I : Type*} (P T : Perm A) (mark : I → A)
    (hfixed : ∀ x, (∀ i, x ≠ mark i) → P x = T x)
    {x : A} (m : ℕ) (hm : ∃ i, (T ^ m) x = mark i) :
    ∃ i, P.SameCycle x (mark i) := by
  induction m generalizing x with
  | zero =>
    obtain ⟨i, hi⟩ := hm
    exact ⟨i, (by simpa using hi : x = mark i).sameCycle P⟩
  | succ m ih =>
    classical
    by_cases hx : ∃ i, x = mark i
    · obtain ⟨i, rfl⟩ := hx
      exact ⟨i, SameCycle.refl P _⟩
    · have hn : ∃ i, (T ^ m) (T x) = mark i := by
        simpa [pow_succ, mul_apply] using hm
      obtain ⟨i, hi⟩ := ih hn
      have hs : P.SameCycle x (T x) := by
        rw [← hfixed x (by simpa only [not_exists] using hx)]
        exact (SameCycle.refl P x).apply_right
      exact ⟨i, hs.trans hi⟩

/-- Once the marks are connected, following a full old cycle away from
them connects the complete actual successor permutation. -/
lemma isCycleOn_of_mark_connection {A I : Type*} [Finite A]
    (P T : Perm A) (mark : I → A) (i₀ : I)
    (hT : T.IsCycleOn Set.univ)
    (hfixed : ∀ x, (∀ i, x ≠ mark i) → P x = T x)
    (hmarks : ∀ i j, P.SameCycle (mark i) (mark j)) :
    P.IsCycleOn Set.univ := by
  have hreach : ∀ x, ∃ i, P.SameCycle x (mark i) := by
    intro x
    obtain ⟨m, hm⟩ := (hT.2 (Set.mem_univ x) (Set.mem_univ (mark i₀))).exists_nat_pow_eq
    exact reaches_some_mark P T mark hfixed m ⟨i₀, hm⟩
  refine ⟨P.bijOn (fun _ => Iff.rfl), ?_⟩
  intro x _ y _
  obtain ⟨i, hi⟩ := hreach x
  obtain ⟨j, hj⟩ := hreach y
  exact hi.trans ((hmarks i j).trans hj.symm)

variable (n : ℕ) [NeZero n]

private def blueStep : V n := 1 - 2 * (n : V n)
private def blueRankStep : V n := 1 + 2 * (n : V n)
private def halfIndex : ℕ := (n + 1) / 2
private def orderedRoot (j : ZMod n) : ZMod n := (halfIndex n : ZMod n) * j
private def orderedMark (j : ZMod n) : V n := mark n (orderedRoot n j)
private def cutPos (j : ZMod n) : ℕ := j.val * n + (orderedRoot n j).val
private def unrank (t : ℕ) : V n := (t : V n) * blueStep n

omit [NeZero n] in
private lemma n_mul_n_zero : (n : V n) * (n : V n) = 0 := by
  calc
    (n : V n) * (n : V n) = ((n * n : ℕ) : V n) := (Nat.cast_mul n n).symm
    _ = 0 := ZMod.natCast_self (n * n)

omit [NeZero n] in
private lemma blueStep_rank : blueStep n * blueRankStep n = 1 := by
  calc
    blueStep n * blueRankStep n = 1 - 4 * ((n : V n) * (n : V n)) := by
      dsimp [blueStep, blueRankStep]
      ring
    _ = 1 := by rw [n_mul_n_zero]; ring

omit [NeZero n] in
private lemma two_half (ho : Odd n) : (2 : ZMod n) * (halfIndex n : ZMod n) = 1 := by
  have h : 2 * halfIndex n = n + 1 := by
    obtain ⟨a, ha⟩ := ho
    dsimp [halfIndex]
    omega
  have hc : (2 : ZMod n) * (halfIndex n : ZMod n) = (n : ZMod n) + 1 := by
    simpa using congrArg (fun a : ℕ => (a : ZMod n)) h
  simpa using hc

omit [NeZero n] in
private lemma two_orderedRoot (ho : Odd n) (j : ZMod n) :
    2 * orderedRoot n j = j := by
  simp only [orderedRoot, ← mul_assoc, two_half n ho, one_mul]

omit [NeZero n] in
private lemma orderedRoot_two (ho : Odd n) (j : ZMod n) :
    orderedRoot n (2 * j) = j := by
  dsimp [orderedRoot]
  calc
    (halfIndex n : ZMod n) * (2 * j) = (2 * (halfIndex n : ZMod n)) * j := by ring
    _ = j := by rw [two_half n ho, one_mul]

omit [NeZero n] in
private lemma orderedMark_cover (ho : Odd n) (r : ZMod n) :
    orderedMark n (2 * r) = mark n r := by
  simp [orderedMark, orderedRoot_two n ho]

private lemma cutPos_lt (j : ZMod n) : cutPos n j < n * n := by
  have hj := j.val_lt
  have hr := (orderedRoot n j).val_lt
  have hn := NeZero.pos n
  dsimp [cutPos]
  nlinarith

private lemma cutPos_mono {j k : ZMod n} (hjk : j.val ≤ k.val) :
    cutPos n j ≤ cutPos n k := by
  by_cases heq : j.val = k.val
  · have : j = k := ZMod.val_injective n heq
    subst k
    rfl
  · have hjk' : j.val + 1 ≤ k.val := by omega
    have hr := (orderedRoot n j).val_lt
    have hn := NeZero.pos n
    dsimp [cutPos]
    nlinarith

private lemma cutPos_strict {j k : ZMod n} (hjk : j.val < k.val) :
    cutPos n j < cutPos n k := by
  have hr := (orderedRoot n j).val_lt
  have hn := NeZero.pos n
  dsimp [cutPos]
  nlinarith

omit [NeZero n] in
private lemma n_mul_mod (a : ℕ) :
    (n : V n) * (a : V n) = (n : V n) * ((a % n : ℕ) : V n) := by
  have hh : ((a % n : ℕ) : V n) + (n : V n) * ((a / n : ℕ) : V n) = (a : V n) := by
    simpa using congrArg (fun t : ℕ => (t : V n)) (Nat.mod_add_div a n)
  calc
    (n : V n) * (a : V n) =
        (n : V n) * ((a % n : ℕ) : V n) +
          ((n : V n) * (n : V n)) * ((a / n : ℕ) : V n) := by rw [← hh]; ring
    _ = (n : V n) * ((a % n : ℕ) : V n) := by rw [n_mul_n_zero]; simp

private lemma rank_mark (ho : Odd n) (j : ZMod n) :
    blueRankStep n * orderedMark n j = (cutPos n j : V n) := by
  have he : ((2 * (orderedRoot n j).val : ℕ) : ZMod n) = j := by
    simpa using two_orderedRoot n ho j
  have hm : (2 * (orderedRoot n j).val) % n = j.val := by
    calc
      (2 * (orderedRoot n j).val) % n =
          (((2 * (orderedRoot n j).val : ℕ) : ZMod n)).val :=
        (ZMod.val_natCast n _).symm
      _ = j.val := congrArg ZMod.val he
  have hc := n_mul_mod n (2 * (orderedRoot n j).val)
  rw [hm] at hc
  dsimp [blueRankStep, orderedMark, mark, cutPos]
  push_cast at hc ⊢
  calc
    (1 + 2 * (n : V n)) * ((orderedRoot n j).val : V n) =
        ((orderedRoot n j).val : V n) +
          (n : V n) * (2 * ((orderedRoot n j).val : V n)) := by ring
    _ = _ := by rw [hc]; ring

private lemma unrank_cut (ho : Odd n) (j : ZMod n) :
    unrank n (cutPos n j) = orderedMark n j := by
  dsimp [unrank]
  rw [← rank_mark n ho j]
  calc
    blueRankStep n * orderedMark n j * blueStep n =
        orderedMark n j * (blueStep n * blueRankStep n) := by ring
    _ = orderedMark n j := by rw [blueStep_rank]; simp

omit [NeZero n] in
private lemma unrank_succ (t : ℕ) :
    unrank n (t + 1) = unrank n t + blueStep n := by
  simp [unrank, add_mul]

omit [NeZero n] in
private lemma unrank_inj {a b : ℕ} (ha : a < n * n) (hb : b < n * n)
    (he : unrank n a = unrank n b) : a = b := by
  have hh := congrArg (fun x : V n => x * blueRankStep n) he
  have he' : (a : V n) = (b : V n) := by
    simpa only [unrank, mul_assoc, blueStep_rank, mul_one] using hh
  have hv := congrArg ZMod.val he'
  simpa [ZMod.val_natCast_of_lt ha, ZMod.val_natCast_of_lt hb] using hv

private lemma next_val (j : ZMod n) (hj : j.val + 1 < n) :
    (j + 1).val = j.val + 1 := by
  have he : j + 1 = ((j.val + 1 : ℕ) : ZMod n) := by simp
  rw [he]
  exact ZMod.val_natCast_of_lt hj

private lemma next_zero (j : ZMod n) (hj : ¬ j.val + 1 < n) : j + 1 = 0 := by
  have hv := j.val_lt
  have he : j.val + 1 = n := by omega
  calc
    j + 1 = ((j.val + 1 : ℕ) : ZMod n) := by simp
    _ = (n : ZMod n) := by rw [he]
    _ = 0 := ZMod.natCast_self n

private def nextCut (j : ZMod n) : ℕ :=
  if j.val + 1 < n then cutPos n (j + 1) else n * n

private lemma cut_lt_next (j : ZMod n) : cutPos n j < nextCut n j := by
  by_cases hj : j.val + 1 < n
  · rw [nextCut, if_pos hj]
    apply cutPos_strict n
    rw [next_val n j hj]
    omega
  · simpa [nextCut, hj] using cutPos_lt n j

private lemma nextCut_le (j : ZMod n) : nextCut n j ≤ n * n := by
  by_cases hj : j.val + 1 < n
  · simpa [nextCut, hj] using (cutPos_lt n (j + 1)).le
  · simp [nextCut, hj]

private lemma unrank_nextCut (ho : Odd n) (j : ZMod n) :
    unrank n (nextCut n j) = orderedMark n (j + 1) := by
  by_cases hj : j.val + 1 < n
  · simpa [nextCut, hj] using unrank_cut n ho (j + 1)
  · simp [nextCut, hj, next_zero n j hj, orderedMark, orderedRoot, mark, unrank]

private lemma no_mark_between (ho : Odd n) (j : ZMod n) {t : ℕ}
    (hlt : cutPos n j < t) (hgt : t < nextCut n j) :
    unrank n t ∉ Set.range (mark n) := by
  rintro ⟨r, hr⟩
  let i : ZMod n := 2 * r
  have hi : orderedMark n i = unrank n t := by
    simpa [i, orderedMark_cover n ho] using hr
  have ht : t < n * n := lt_of_lt_of_le hgt (nextCut_le n j)
  have he : t = cutPos n i := by
    apply unrank_inj n ht (cutPos_lt n i)
    rw [unrank_cut n ho]
    exact hi.symm
  by_cases hj : j.val + 1 < n
  · have hg : t < cutPos n (j + 1) := by simpa [nextCut, hj] using hgt
    by_cases hij : i.val ≤ j.val
    · have hh := cutPos_mono n hij
      omega
    · have hjvi := next_val n j hj
      have hji : (j + 1).val ≤ i.val := by omega
      have hh := cutPos_mono n hji
      omega
  · have hjv := j.val_lt
    have hiv := i.val_lt
    have hij : i.val ≤ j.val := by omega
    have hh := cutPos_mono n hij
    omega

private lemma blue_unmarked (x : V n) (hx : x ∉ Set.range (mark n)) :
    blue n x = x + blueStep n := by
  simp [blue, mul_apply, rho_fixed n x hx, blueStep]

private lemma blue_ordered_mark (ho : Odd n) (j : ZMod n) :
    blue n (orderedMark n (j + 2)) = unrank n (cutPos n j + 1) := by
  have hh : (halfIndex n : ZMod n) * 2 = 1 := by
    rw [mul_comm, two_half n ho]
  have hr : orderedRoot n (j + 2) - 1 = orderedRoot n j := by
    simp [orderedRoot, mul_add, hh]
  rw [unrank_succ, unrank_cut n ho]
  simp [blue, mul_apply, orderedMark, rho_mark, hr, blueStep]

private lemma blue_cut_return (ho : Odd n) (j : ZMod n) :
    (blue n).SameCycle (orderedMark n (j + 2)) (orderedMark n (j + 1)) := by
  have hfirst : (blue n).SameCycle (orderedMark n (j + 2))
      (unrank n (cutPos n j + 1)) := by
    rw [← blue_ordered_mark n ho j]
    exact (SameCycle.refl (blue n) _).apply_right
  have hpath : (blue n).SameCycle (unrank n (cutPos n j + 1))
      (unrank n (nextCut n j)) := by
    apply sameCycle_interval (blue n) (unrank n) (by have := cut_lt_next n j; omega)
    intro t ht htn
    rw [blue_unmarked n _ (no_mark_between n ho j (by omega) htn)]
    exact (unrank_succ n t).symm
  rw [unrank_nextCut n ho] at hpath
  exact hfirst.trans hpath

private lemma blue_all_ordered_marks (ho : Odd n) (i j : ZMod n) :
    (blue n).SameCycle (orderedMark n i) (orderedMark n j) := by
  have hstep : ∀ a : ZMod n, (blue n).SameCycle (orderedMark n a)
      (orderedMark n (a + 1)) := by
    intro a
    have hh := (blue_cut_return n ho (a - 1)).symm
    convert hh using 1 <;> congr 1 <;> ring
  have hp : ∀ (m : ℕ) (a : ZMod n), (blue n).SameCycle
      (orderedMark n a) (orderedMark n (a + (m : ZMod n))) := by
    intro m
    induction m with
    | zero => intro a; simpa using SameCycle.refl (blue n) (orderedMark n a)
    | succ m ih =>
      intro a
      have hh := (ih a).trans (hstep (a + (m : ZMod n)))
      simpa [Nat.cast_add, Nat.cast_one, add_assoc] using hh
  have hh := hp (j - i).val i
  simpa using hh

omit [NeZero n] in
private lemma addRight_pow_blue (d : V n) (m : ℕ) (x : V n) :
    (Equiv.addRight d ^ m) x = x + (m : V n) * d := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', mul_apply, ih]
    change x + (m : V n) * d + d = _
    simp [Nat.cast_add, Nat.cast_one, add_mul, add_assoc]

private lemma translation_isCycleOn :
    (Equiv.addRight (blueStep n)).IsCycleOn Set.univ := by
  refine ⟨(Equiv.addRight (blueStep n)).bijOn (fun _ => Iff.rfl), ?_⟩
  intro x _ y _
  let t : V n := (y - x) * blueRankStep n
  have he : (Equiv.addRight (blueStep n) ^ t.val) x = y := by
    rw [addRight_pow_blue]
    simp only [ZMod.natCast_zmod_val]
    dsimp [t]
    have hh : blueRankStep n * blueStep n = 1 := by
      rw [mul_comm, blueStep_rank]
    rw [mul_assoc, hh]
    ring
  have hh := (SameCycle.refl (Equiv.addRight (blueStep n)) x).pow_right (n := t.val)
  rw [he] at hh
  exact hh

/-- The actual blue successor has one orbit for every odd n at least
three; no orbit or Hamiltonicity hypothesis is assumed. -/
theorem blue_isCycleOn (_hn : 3 ≤ n) (ho : Odd n) :
    (blue n).IsCycleOn Set.univ := by
  apply isCycleOn_of_mark_connection (blue n) (Equiv.addRight (blueStep n))
    (orderedMark n) 0 (translation_isCycleOn n)
  · intro x hx
    apply blue_unmarked n x
    rintro ⟨r, hr⟩
    exact hx (2 * r) ((orderedMark_cover n ho r).trans hr).symm
  · exact blue_all_ordered_marks n ho

end Erdos585.HaarComposite
