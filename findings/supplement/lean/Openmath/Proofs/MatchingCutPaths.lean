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
import Openmath.Proofs.HaarPair

/-!
# Surviving paths after opposite matching cuts

The least successor segment avoids the cut at its last left endpoint
and the cut entering its first left endpoint. Shore exchange gives
the complementary right-endpoint path as an actual graph reachability.
-/

namespace Erdos585.MatchingCutPaths

open SimpleGraph Equiv Equiv.Perm

variable {V : Type*}

/-- Delete one edge from each of two disjoint perfect matchings. -/
def cutFactor (f g : Perm V) (a c : V) : SimpleGraph (V × Bool) :=
  HaarPair.matchingFactor f g \
    (edge (c, false) (f c, true) ⊔ edge (a, false) (g a, true))

private lemma surviving_step (f g : Perm V) (hne : ∀ x, f x ≠ g x)
    (a c x : V) (hxc : x ≠ c) (hxa : (g⁻¹ * f) x ≠ a) :
    (cutFactor f g a c).Reachable (x, false) ((g⁻¹ * f) x, false) := by
  have h₁ : (cutFactor f g a c).Adj (x, false) (f x, true) := by
    simp only [cutFactor, sdiff_adj, sup_adj]
    refine ⟨(HaarPair.factor_cross f g x (f x)).mpr (Or.inl rfl), ?_⟩
    simp only [edge_adj, Prod.mk.injEq, Bool.false_eq_true, Bool.true_eq_false,
      and_false, and_true, or_false, hxc, false_and, false_or, not_and]
    rintro ⟨rfl, he⟩ _
    exact hne x he
  have h₂ : (cutFactor f g a c).Adj ((g⁻¹ * f) x, false) (f x, true) := by
    have hg : g ((g⁻¹ * f) x) = f x := by simp [mul_apply]
    simp only [cutFactor, sdiff_adj, sup_adj]
    refine ⟨(HaarPair.factor_cross f g _ _).mpr (Or.inr hg.symm), ?_⟩
    have hfc : (g⁻¹ * f) x = c → f x ≠ f c := by
      intro hh he
      apply hne c
      rw [← he, ← hg, hh]
    simp only [edge_adj, Prod.mk.injEq, Bool.false_eq_true, Bool.true_eq_false,
      and_false, and_true, or_false, not_or]
    exact ⟨fun h => hfc h.1.1 h.1.2, fun h => hxa h.1.1⟩
  exact h₁.reachable.trans h₂.symm.reachable

/-- The left endpoints remain connected after opposite matching edges are deleted. -/
theorem left_reachable [Finite V] (f g : Perm V) (hne : ∀ x, f x ≠ g x)
    (a c : V) (hcycle : (g⁻¹ * f).SameCycle a c) :
    (cutFactor f g a c).Reachable (a, false) (c, false) := by
  classical
  let P : Perm V := g⁻¹ * f
  have hex : ∃ N : ℕ, (P ^ N) a = c := hcycle.exists_nat_pow_eq
  let N := Nat.find hex
  have hN : (P ^ N) a = c := Nat.find_spec hex
  have hmin : ∀ j < N, (P ^ j) a ≠ c := by
    intro j hj
    exact Nat.find_min hex hj
  have hstep : ∀ j < N,
      (cutFactor f g a c).Reachable ((P ^ j) a, false) ((P ^ (j+1)) a, false) := by
    intro j hj
    have hreturn : (P ^ (j+1)) a ≠ a := by
      intro hh
      have hd : j+1 ≤ N := by omega
      have hsum : N - (j+1) + (j+1) = N := Nat.sub_add_cancel hd
      have heq : (P ^ (N-(j+1))) a = c := by
        calc
          (P ^ (N-(j+1))) a = (P ^ (N-(j+1))) ((P ^ (j+1)) a) := by rw [hh]
          _ = (P ^ N) a := by rw [← mul_apply, ← pow_add, hsum]
          _ = c := hN
      exact hmin (N-(j+1)) (by omega) heq
    have hh := surviving_step f g hne a c ((P ^ j) a) (hmin j hj)
    have he : (g⁻¹ * f) ((P ^ j) a) = (P ^ (j+1)) a := by
      simp [P, pow_succ', mul_apply]
    rw [he] at hh
    exact hh hreturn
  have hall : ∀ j, j ≤ N →
      (cutFactor f g a c).Reachable (a, false) ((P ^ j) a, false) := by
    intro j
    induction j with
    | zero =>
      intro _
      simp
    | succ j ih =>
      intro hj
      exact (ih (by omega)).trans (hstep j (by omega))
  simpa [hN] using hall N le_rfl

private def flipHom (f g : Perm V) (a c : V) :
    cutFactor g.symm f.symm (f c) (g a) →g cutFactor f g a c where
  toFun v := (v.1, !v.2)
  map_rel' := by
    rintro ⟨x, bx⟩ ⟨y, by_⟩ hh
    cases bx <;> cases by_ <;>
      simp [cutFactor, HaarPair.matchingFactor, SimpleGraph.fromRel_adj,
        edge_adj, Equiv.eq_symm_apply] at * <;> aesop

/-- The right endpoints have the complementary surviving path. -/
theorem right_reachable [Finite V] (f g : Perm V) (hne : ∀ x, f x ≠ g x)
    (a c : V) (hcycle : (g⁻¹ * f).SameCycle a c) :
    (cutFactor f g a c).Reachable (f c, true) (g a, true) := by
  have hne' : ∀ x, g.symm x ≠ f.symm x := by
    intro x hh
    apply hne (g.symm x)
    simpa using congrArg f hh
  have hc : (f * g⁻¹).SameCycle (f c) (g a) := by
    have hh := hcycle.symm.symm_apply_right.conj (g := f)
    have he : f ((g⁻¹ * f).symm a) = g a := by
      have hi := (g⁻¹ * f).apply_symm_apply a
      simpa [mul_apply] using congrArg g hi
    simpa [mul_assoc, he] using hh
  have hp := left_reachable g.symm f.symm hne' (f c) (g a) hc
  exact hp.map (flipHom f g a c)

end Erdos585.MatchingCutPaths
