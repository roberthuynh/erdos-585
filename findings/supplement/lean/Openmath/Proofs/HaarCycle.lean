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
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.Combinatorics.SimpleGraph.Matching
import FormalConjecturesUtil.Linters.ModuleDocstringLinter

/-!
# Joining permutation cycles at one marked point per orbit

This is the permutation interface of the complete paper argument in
Paper83. It is a supporting lemma, not the finite-field Haar theorem.
The second interface turns a full matching-successor orbit into an
actual simple graph cycle. No extremal conclusion is asserted here.
-/

namespace Erdos585.HaarCycle

open Equiv Equiv.Perm

variable {V I : Type*}

/-- Changing a successor only at the marked endpoint leaves an orbit path
from every old point to that endpoint. -/
lemma reaches_mark (P T : Perm V) (a : V)
    (hstep : ∀ x, P.SameCycle x a → x ≠ a → T x = P x)
    (n : ℕ) {x : V} (hn : (P ^ n) x = a) : T.SameCycle x a := by
  induction n generalizing x with
  | zero =>
    have : x = a := by simpa using hn
    exact this.sameCycle T
  | succ n ih =>
    by_cases hxa : x = a
    · exact hxa.sameCycle T
    have hPa : P.SameCycle x a := by
      rw [← hn]
      exact (SameCycle.refl P x).pow_right
    have hnext : (P ^ n) (P x) = a := by simpa [pow_succ, mul_apply] using hn
    have hrel : T.SameCycle x (P x) := by
      rw [← hstep x hPa hxa]
      exact (SameCycle.refl T x).apply_right
    exact hrel.trans (ih hnext)

/-- A finite successor splice joins all old cycles when the marked points
form a transversal and their new successor order is itself one cycle. -/
theorem splice_isCycleOn [Finite V] [Finite I]
    (P T : Perm V) (Q : Perm I) (mark : I → V)
    (hcover : ∀ x, ∃ i, P.SameCycle x (mark i))
    (hunique : ∀ i j, P.SameCycle (mark i) (mark j) → i = j)
    (hfixed : ∀ x, (∀ i, x ≠ mark i) → T x = P x)
    (hmarked : ∀ i, T (mark i) = P (mark (Q i)))
    (hQ : Q.IsCycleOn Set.univ) : T.IsCycleOn Set.univ := by
  have hreach : ∀ i x, P.SameCycle x (mark i) → T.SameCycle x (mark i) := by
    intro i x hx
    obtain ⟨n, hn⟩ := hx.exists_nat_pow_eq
    apply reaches_mark P T (mark i) ?_ n hn
    intro y hy hne
    apply hfixed y
    intro j heq
    have hij : j = i := hunique j i (heq ▸ hy)
    exact hne (heq.trans (congrArg mark hij))
  have hmark_step : ∀ i, T.SameCycle (mark i) (mark (Q i)) := by
    intro i
    have hfirst : T.SameCycle (mark i) (P (mark (Q i))) := by
      rw [← hmarked i]
      exact (SameCycle.refl T (mark i)).apply_right
    exact hfirst.trans (hreach (Q i) _ ((SameCycle.refl P _).apply_left))
  have hmark_pow : ∀ n i, T.SameCycle (mark i) (mark ((Q ^ n) i)) := by
    intro n
    induction n with
    | zero => intro i; exact SameCycle.refl T (mark i)
    | succ n ih =>
      intro i
      simpa [pow_succ', mul_apply] using (ih i).trans (hmark_step ((Q ^ n) i))
  refine ⟨T.bijOn (fun _ => Iff.rfl), ?_⟩
  intro x _ y _
  obtain ⟨i, hi⟩ := hcover x
  obtain ⟨j, hj⟩ := hcover y
  obtain ⟨n, hn⟩ := (hQ.2 (Set.mem_univ i) (Set.mem_univ j)).exists_nat_pow_eq
  have hmid : T.SameCycle (mark i) (mark j) := by
    simpa [hn] using hmark_pow n i
  exact (hreach i x hi).trans (hmid.trans (hreach j y hj).symm)

open SimpleGraph

/-- Two disjoint matchings with one full successor orbit give an actual
simple cycle spanning both shores. This bridge retains actual walks. -/
theorem cycle_of_two_matchings [Finite V]
    (H : SimpleGraph (V × Bool)) (f g : Perm V)
    (hcross : ∀ x y, H.Adj (x, false) (y, true) ↔ y = f x ∨ y = g x)
    (hsame : ∀ x y b, ¬ H.Adj (x, b) (y, b))
    (hne : ∀ x, f x ≠ g x)
    (horbit : (g⁻¹ * f).IsCycleOn Set.univ) (x₀ : V) :
    ∃ p : H.Walk (x₀, false) (x₀, false), p.IsCycle ∧ ∀ v, v ∈ p.support := by
  classical
  have hleft : ∀ x, H.neighborSet (x, false) = {(f x, true), (g x, true)} := by
    intro x
    ext ⟨y, b⟩
    cases b
    · simp [hsame]
    · simpa using hcross x y
  have hright : ∀ y, H.neighborSet (y, true) = {(f.symm y, false), (g.symm y, false)} := by
    intro y
    ext ⟨x, b⟩
    cases b
    · simp only [mem_neighborSet, Set.mem_insert_iff, Set.mem_singleton_iff,
        Prod.mk.injEq, and_true]
      rw [SimpleGraph.adj_comm, hcross]
      simp only [Equiv.eq_symm_apply, eq_comm]
    · simp [hsame]
  have hcycs : H.IsCycles := by
    intro ⟨x, b⟩ _
    cases b
    · rw [hleft]
      have hd : (f x, true) ≠ (g x, true) := fun h => hne x (congrArg Prod.fst h)
      simp [hd]
    · rw [hright]
      have hi : f.symm x ≠ g.symm x := by
        intro hh
        apply hne (f.symm x)
        rw [f.apply_symm_apply, hh, g.apply_symm_apply]
      have hd : (f.symm x, false) ≠ (g.symm x, false) := fun h => hi (congrArg Prod.fst h)
      simp [hd]
  let P : Perm V := g⁻¹ * f
  have hstep : ∀ x, H.Reachable (x, false) (P x, false) := by
    intro x
    have h₁ : H.Adj (x, false) (f x, true) := (hcross _ _).mpr (Or.inl rfl)
    have h₂ : H.Adj (P x, false) (f x, true) := by
      apply (hcross _ _).mpr
      right
      simp [P, mul_apply]
    exact h₁.reachable.trans h₂.symm.reachable
  have hpowers : ∀ n x, H.Reachable (x, false) ((P ^ n) x, false) := by
    intro n
    induction n with
    | zero => intro x; exact SimpleGraph.Reachable.refl _
    | succ n ih =>
      intro x
      simpa [pow_succ', mul_apply] using (ih x).trans (hstep ((P ^ n) x))
  have hzero : ∀ x y, H.Reachable (x, false) (y, false) := by
    intro x y
    obtain ⟨n, hn⟩ := (horbit.2 (Set.mem_univ x) (Set.mem_univ y)).exists_nat_pow_eq
    simpa [P, hn] using hpowers n x
  have hall : ∀ v, H.Reachable (x₀, false) v := by
    rintro ⟨y, b⟩
    cases b
    · exact hzero x₀ y
    · have he : H.Adj (f.symm y, false) (y, true) := by
        apply (hcross _ _).mpr
        left
        simp
      exact (hzero x₀ (f.symm y)).trans he.reachable
  let c := H.connectedComponentMk (x₀, false)
  have hc : ∀ v, v ∈ c.supp := by
    intro v
    exact ConnectedComponent.sound (hall v).symm
  have hn : (H.neighborSet (x₀, false)).Nonempty := by
    rw [hleft]
    exact ⟨(f x₀, true), by simp⟩
  obtain ⟨p, hp, hs⟩ :=
    hcycs.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp (hc (x₀, false)) hn
  refine ⟨p, hp, ?_⟩
  intro v
  apply p.mem_verts_toSubgraph.mp
  rw [hs]
  exact hc v

end Erdos585.HaarCycle
