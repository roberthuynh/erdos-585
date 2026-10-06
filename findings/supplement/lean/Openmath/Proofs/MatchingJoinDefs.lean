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
import Openmath.Proofs.RegularFive

/-! # Shared actual graphs and terminal contract for arbitrary matching joins -/

open SimpleGraph Finset

namespace Erdos585.MatchingJoin

/-- The two actual sixteen-vertex halves of the checked quintic graph. -/
def embed : Bool → Fin 16 → Fin 32
  | false, x => ⟨x.val, by omega⟩
  | true, x => ⟨x.val + 16, by omega⟩

def A : Finset (Fin 16) := {1,3,4,5,6,7}
def D : Finset (Fin 16) := {9,10,11,12,13,14,15}

/-- Exactly the ordered half-terminal states with explicit path certificates. -/
def Admitted (x y : Fin 16) : Prop :=
  x ≠ y ∧ ((x ∈ A ∧ y ∈ A) ∨ (x ∈ D ∧ y ∈ D) ∨ (x ∈ D ∧ y ∈ A))

instance (x y : Fin 16) : Decidable (Admitted x y) := by
  unfold Admitted
  infer_instance

theorem embed_injective (s : Bool) : Function.Injective (embed s) := by
  intro x y h
  apply Fin.ext
  have hh := congrArg Fin.val h
  cases s <;> simp only [embed] at hh <;> omega

theorem embed_ne_other (s : Bool) (x y : Fin 16) : embed s x ≠ embed (!s) y := by
  intro h
  have hh := congrArg Fin.val h
  cases s <;> simp only [embed, Bool.not_false, Bool.not_true] at hh <;> omega

/-- Two actual old copies, with an unrestricted bijection as the new matching. -/
def graph (f : Equiv.Perm (Fin 32)) : SimpleGraph (Fin 32 × Bool) where
  Adj x y :=
    (x.2 = y.2 ∧ RegularFive.graph.Adj x.1 y.1) ∨
    (x.2 = false ∧ y.2 = true ∧ f x.1 = y.1) ∨
    (x.2 = true ∧ y.2 = false ∧ f y.1 = x.1)
  symm := ⟨by
    intro x y h
    rcases h with h | h | h
    · exact Or.inl ⟨h.1.symm, h.2.symm⟩
    · exact Or.inr (Or.inr ⟨h.2.1, h.1, h.2.2⟩)
    · exact Or.inr (Or.inl ⟨h.2.1, h.1, h.2.2⟩)⟩
  loopless := ⟨by
    intro x h
    rcases h with h | h | h
    · exact RegularFive.graph.loopless.irrefl x.1 h.2
    · exact Bool.false_ne_true (h.1.symm.trans h.2.1)
    · exact Bool.false_ne_true (h.2.1.symm.trans h.1)⟩

instance (f : Equiv.Perm (Fin 32)) : DecidableRel (graph f).Adj := by
  intro x y
  unfold graph
  infer_instance

/-- Pure terminal-selection data; no path or cycle existence is assumed here. -/
structure Selection (f : Equiv.Perm (Fin 32)) where
  x0 : Fin 16
  y0 : Fin 16
  x1 : Fin 16
  y1 : Fin 16
  a0 : Fin 16
  b0 : Fin 16
  a1 : Fin 16
  b1 : Fin 16
  s : Bool
  h0 : Admitted x0 y0
  h1 : Admitted x1 y1
  k0 : Admitted a0 b0
  k1 : Admitted a1 b1
  fx0 : f (embed false x0) = embed s a0
  fy0 : f (embed false y0) = embed s b0
  fx1 : f (embed true x1) = embed (!s) a1
  fy1 : f (embed true y1) = embed (!s) b1

end Erdos585.MatchingJoin
