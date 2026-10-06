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
import Openmath.Proofs.DensityCore

/-!
# Four-slot cut completion

The abstract uncrossing step for completing a bipartite critical core. This
file proves a cut-function lemma, not the full graph reduction or a cycle pair.
-/
open Finset
namespace Erdos585.PortCompletion
variable {V : Type*} [Fintype V] [DecidableEq V]
def slot (S : Finset V) (v : V) : ℕ := if v ∈ S then 1 else 0
def ports (S : Finset V) (a b c d : V) : ℕ :=
  slot S a + slot S b + slot S c + slot S d
def cross (S : Finset V) (u v : V) : ℕ :=
  if (u ∈ S ↔ v ∈ S) then 0 else 1
lemma ports_compl (S : Finset V) (a b c d : V) :
    ports S a b c d + ports (univ \ S) a b c d = 4 := by
  unfold ports slot
  by_cases ha : a ∈ S <;> by_cases hb : b ∈ S <;>
    by_cases hc : c ∈ S <;> by_cases hd : d ∈ S <;> simp [ha,hb,hc,hd]
lemma bad_pattern (S : Finset V) (a b c d : V) (k : ℕ)
    (hlo : 6 ≤ k + ports S a b c d)
    (hhi : 6 ≤ k + ports (univ \ S) a b c d)
    (heven : (k + ports S a b c d) % 2 = 0)
    (hbad : k + cross S a c + cross S b d < 6) :
    k = 4 ∧ (a ∈ S ↔ c ∈ S) ∧ (b ∈ S ↔ d ∈ S) ∧
      (a ∈ S ↔ b ∉ S) := by
  unfold ports slot cross at *
  by_cases ha : a ∈ S <;> by_cases hb : b ∈ S <;>
    by_cases hc : c ∈ S <;> by_cases hd : d ∈ S <;>
    simp [ha,hb,hc,hd] at * <;> omega
lemma compl_nonempty (U : Finset V) (hU : U ≠ univ) : (univ \ U).Nonempty := by
  apply sdiff_nonempty.mpr
  intro h
  exact hU (Subset.antisymm (subset_univ U) h)
lemma compl_proper (U : Finset V) (hU : U.Nonempty) : univ \ U ≠ univ := by
  obtain ⟨v,hv⟩ := hU
  intro h
  have : v ∈ univ \ U := h.symm ▸ mem_univ v
  exact (mem_sdiff.mp this).2 hv
lemma orient_bad (f : Finset V → ℕ) (a b c d : V) (S : Finset V)
    (hsymm : ∀ U, f (univ \ U) = f U)
    (hp : f S = 4 ∧ (a ∈ S ↔ c ∈ S) ∧ (b ∈ S ↔ d ∈ S) ∧
      (a ∈ S ↔ b ∉ S)) :
    ∃ U, f U = 4 ∧ a ∈ U ∧ b ∉ U ∧ c ∈ U ∧ d ∉ U := by
  by_cases ha : a ∈ S
  · refine ⟨S,hp.1,ha,?_,?_,?_⟩ <;> tauto
  · refine ⟨univ \ S,?_,?_,?_,?_,?_⟩
    · rw [hsymm]; exact hp.1
    all_goals simp only [mem_sdiff,mem_univ,true_and]; tauto

/-- One of the two bipartite pairings raises every proper nonempty cut to six.
Slots may repeat; cut symmetry, submodularity, deficit and parity are explicit. -/
theorem exists_good_pairing (f : Finset V → ℕ) (a b c d : V)
    (hsymm : ∀ S, f (univ \ S) = f S)
    (hsub : ∀ S T, f (S ∩ T) + f (S ∪ T) ≤ f S + f T)
    (hbound : ∀ S, S.Nonempty → S ≠ univ → 6 ≤ f S + ports S a b c d)
    (hparity : ∀ S, (f S + ports S a b c d) % 2 = 0) :
    (∀ S, S.Nonempty → S ≠ univ → 6 ≤ f S + cross S a c + cross S b d) ∨
    (∀ S, S.Nonempty → S ≠ univ → 6 ≤ f S + cross S a d + cross S b c) := by
  classical
  by_contra hn
  push Not at hn
  obtain ⟨⟨S,hSne,hSp,hSbad⟩,⟨T,hTne,hTp,hTbad⟩⟩ := hn
  have hpS := bad_pattern S a b c d (f S) (hbound S hSne hSp)
    (by simpa [hsymm] using hbound (univ \ S) (compl_nonempty S hSp) (compl_proper S hSne)) (hparity S) hSbad
  have swapports (U : Finset V) : ports U a b d c = ports U a b c d := by
    simp only [ports]; omega
  have hpT := bad_pattern T a b d c (f T) (by simpa [swapports] using hbound T hTne hTp)
    (by simpa [hsymm,swapports] using hbound (univ \ T) (compl_nonempty T hTp) (compl_proper T hTne)) (by simpa [swapports] using hparity T) hTbad
  obtain ⟨U,hU,haU,hbU,hcU,hdU⟩ := orient_bad f a b c d S hsymm hpS
  obtain ⟨W,hW,haW,hbW,hdW,hcW⟩ := orient_bad f a b d c T hsymm hpT
  have hi_ne : (U ∩ W).Nonempty := ⟨a,mem_inter.mpr ⟨haU,haW⟩⟩
  have hu_ne : (U ∪ W).Nonempty := ⟨a,mem_union_left _ haU⟩
  have hi_p : U ∩ W ≠ univ := by
    intro h
    have : b ∈ U ∩ W := h.symm ▸ mem_univ b
    exact hbU (mem_inter.mp this).1
  have hu_p : U ∪ W ≠ univ := by
    intro h
    have : b ∈ U ∪ W := h.symm ▸ mem_univ b
    exact (mem_union.mp this).elim hbU hbW
  have hi_ports : ports (U ∩ W) a b c d = 1 := by
    simp [ports,slot,haU,hbU,hcU,hdU,haW,hbW,hcW,hdW]
  have hu_ports : ports (U ∪ W) a b c d = 3 := by
    simp [ports,slot,haU,hbU,hcU,hdU,haW,hbW,hcW,hdW]
  have hi := hbound (U ∩ W) hi_ne hi_p
  have hu := hbound (univ \ (U ∪ W)) (compl_nonempty _ hu_p) (compl_proper _ hu_ne)
  have hp := ports_compl (U ∪ W) a b c d
  have hh := hsub U W
  rw [hsymm] at hu
  rw [hi_ports] at hi
  rw [hu_ports] at hp
  rw [hU,hW] at hh
  omega
end Erdos585.PortCompletion
