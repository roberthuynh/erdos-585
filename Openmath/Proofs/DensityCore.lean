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
import Openmath.Proofs.SmallExact

/-!
# A density-critical core

A smallest nonempty vertex set spanning at least three times its order minus two
edges has every nontrivial edge cut of size at least four.
-/

open SimpleGraph Finset
namespace Erdos585.DensityCore

variable {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Ambient edges with both endpoints in the specified set. -/
def inside (s : Finset V) : Finset (Sym2 V) := G.edgeFinset ∩ s.sym2

/-- Edges of `s` joining `t` to its complement in `s`. -/
def crossing (s t : Finset V) : Finset (Sym2 V) :=
  inside G s \ (inside G t ∪ inside G (s \ t))

lemma mem_crossing_iff {s t : Finset V} (a b : V) :
    s(a,b) ∈ crossing G s t ↔ G.Adj a b ∧ a ∈ s ∧ b ∈ s ∧
      ((a ∈ t ∧ b ∉ t) ∨ (a ∉ t ∧ b ∈ t)) := by
  simp only [crossing, inside, mem_sdiff, mem_union, mem_inter, mem_edgeFinset,
    mk_mem_sym2_iff]
  tauto

lemma inside_mono {s t : Finset V} (h : s ⊆ t) : inside G s ⊆ inside G t := by
  intro e he
  exact mem_inter.mpr ⟨(mem_inter.mp he).1, sym2_mono h (mem_inter.mp he).2⟩

lemma inside_disjoint {s t : Finset V} (h : Disjoint s t) :
    Disjoint (inside G s) (inside G t) := by
  apply Finset.disjoint_left.mpr
  intro e he hf
  induction e using Sym2.inductionOn with | _ a b => ?_
  have ha := (mk_mem_sym2_iff.mp (mem_inter.mp he).2).1
  have hb := (mk_mem_sym2_iff.mp (mem_inter.mp hf).2).1
  exact Finset.disjoint_left.mp h ha hb

lemma partition_count {s t : Finset V} (h : t ⊆ s) :
    (inside G s).card = (inside G t).card + (inside G (s \ t)).card +
      (crossing G s t).card := by
  have hs : inside G t ∪ inside G (s \ t) ⊆ inside G s :=
    union_subset (inside_mono G h) (inside_mono G sdiff_subset)
  have hd := inside_disjoint G (disjoint_sdiff_self_right : Disjoint t (s \ t))
  have hc := card_sdiff_add_card_eq_card hs
  rw [card_union_of_disjoint hd] at hc
  simpa only [crossing, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hc.symm

lemma inside_card_induce (s : Finset V) :
    (inside G s).card = (G.induce (↑s : Set V)).edgeFinset.card := by
  rw [← G.card_filter_edgeFinset_toFinset_subset s, G.filter_edgeFinset_toFinset_subset]
  rfl

lemma inside_univ : inside G univ = G.edgeFinset := by
  ext e
  induction e using Sym2.inductionOn with | _ a b => simp [inside]

lemma degree_induce_le (s : Finset V) (v : (↑s : Set V)) :
    (G.induce (↑s : Set V)).degree v ≤ G.degree v.1 := by
  have h := congrArg Finset.card (G.map_neighborFinset_induce v)
  rw [card_map] at h
  have hle := h.trans_le (card_le_card inter_subset_left)
  simp only [card_neighborFinset_eq_degree] at hle
  simpa only [← card_neighborSet_eq_degree, Fintype.card_eq_nat_card] using hle

/-- Minimality is with respect to nonempty proper vertex subsets. -/
def Critical (s : Finset V) : Prop :=
  s.Nonempty ∧ 3 * s.card ≤ (inside G s).card + 2 ∧
  ∀ t, t.Nonempty → t ⊂ s → (inside G t).card + 2 < 3 * t.card

theorem exists_critical (h : ∃ s : Finset V, s.Nonempty ∧
    3 * s.card ≤ (inside G s).card + 2) : ∃ s, Critical G s := by
  classical
  let candidates := univ.filter fun s : Finset V =>
    s.Nonempty ∧ 3 * s.card ≤ (inside G s).card + 2
  have hn : candidates.Nonempty := by
    obtain ⟨s, hs⟩ := h
    exact ⟨s, by simpa [candidates] using hs⟩
  obtain ⟨s, hs, hmin⟩ := exists_min_image candidates Finset.card hn
  have hs' : s.Nonempty ∧ 3 * s.card ≤ (inside G s).card + 2 := by
    simpa [candidates] using hs
  refine ⟨s, hs'.1, hs'.2, ?_⟩
  intro t ht hts
  by_contra hc
  have htmem : t ∈ candidates := by simp [candidates, ht, show 3 * t.card ≤
      (inside G t).card + 2 by omega]
  have hle := hmin t htmem
  have hlt := card_lt_card hts
  omega

/-- Every nontrivial cut of a density-critical core has at least four edges. -/
theorem four_le_crossing {s t : Finset V} (hs : Critical G s)
    (ht : t.Nonempty) (hts : t ⊂ s) : 4 ≤ (crossing G s t).card := by
  have hsub := (Finset.ssubset_iff_subset_ne.mp hts).1
  have hu : (s \ t).Nonempty := by
    apply sdiff_nonempty.mpr
    intro hh
    exact (Finset.ssubset_iff_subset_ne.mp hts).2 (Subset.antisymm hsub hh)
  have hus : s \ t ⊂ s := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨sdiff_subset, ?_⟩
    intro heq
    obtain ⟨v, hv⟩ := ht
    have hx : v ∈ s \ t := heq.symm ▸ hsub hv
    exact (mem_sdiff.mp hx).2 hv
  have ha := hs.2.2 t ht hts
  have hb := hs.2.2 (s \ t) hu hus
  have hc := partition_count G hsub
  have hv := card_sdiff_add_card_eq_card hsub
  have hd := hs.2.1
  omega

/-- In a host of maximum degree six, the core has at most four missing incidences. -/
theorem deficit_le_four (hmax : ∀ v, G.degree v ≤ 6) {s : Finset V}
    (hs : Critical G s) :
    ∑ v : (↑s : Set V), (6 - (G.induce (↑s : Set V)).degree v) ≤ 4 := by
  let H := G.induce (↑s : Set V)
  have hd : ∀ v, H.degree v ≤ 6 := fun v => (degree_induce_le G s v).trans (hmax v.1)
  have hsum : (∑ v, (6 - H.degree v)) + (∑ v, H.degree v) = 6 * s.card := by
    rw [← sum_add_distrib]
    calc
      ∑ v, (6 - H.degree v + H.degree v) = ∑ _v : (↑s : Set V), 6 := by
        apply sum_congr rfl
        intro v _
        exact Nat.sub_add_cancel (hd v)
      _ = 6 * s.card := by simp [Nat.mul_comm]
  have hdeg := H.sum_degrees_eq_twice_card_edges
  have hc := hs.2.1
  rw [inside_card_induce] at hc
  change 3 * s.card ≤ H.edgeFinset.card + 2 at hc
  change (∑ v, (6 - H.degree v)) ≤ 4
  omega

/-- A six-regular pair-free graph yields a pair-free density-critical induced core.
The displayed cut count is an ambient representation of the induced edge cut. -/
theorem regular_six_core [Nonempty V] (hreg : ∀ v, G.degree v = 6)
    (hfree : ¬ HasPairF G) : ∃ s : Finset V,
      Critical G s ∧ ¬ HasPairF (G.induce (↑s : Set V)) ∧
      (∀ v : (↑s : Set V), (G.induce (↑s : Set V)).degree v ≤ 6) ∧
      (∑ v : (↑s : Set V), (6 - (G.induce (↑s : Set V)).degree v) ≤ 4) ∧
      ∀ t, t.Nonempty → t ⊂ s → 4 ≤ (crossing G s t).card := by
  have hdeg := G.sum_degrees_eq_twice_card_edges
  simp only [hreg, sum_const, card_univ, smul_eq_mul] at hdeg
  obtain ⟨s, hs⟩ := exists_critical G ⟨univ, univ_nonempty, by
    rw [inside_univ, card_univ]
    omega⟩
  exact ⟨s, hs, not_hasPairF_induce hfree _,
    fun v => (degree_induce_le G s v).trans (hreg v.1).le,
    deficit_le_four G (fun v => (hreg v).le) hs,
    fun t ht hts => four_le_crossing G hs ht hts⟩

/-- A concrete check: deleting two edges sharing an endpoint in K₇ makes the cut bound sharp. -/
def sharpGraph : SimpleGraph (Fin 7) where
  Adj a b := a ≠ b ∧ s(a,b) ≠ s(0,1) ∧ s(a,b) ≠ s(0,2)
  symm := ⟨by intro a b; simp only [Sym2.eq_swap]; exact fun h => ⟨h.1.symm, h.2⟩⟩
  loopless := ⟨by intro a h; exact h.1 rfl⟩

instance : DecidableRel sharpGraph.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _ ∧ _))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
example : Critical sharpGraph univ ∧ (crossing sharpGraph univ {0}).card = 4 := by
  unfold Critical
  decide

end Erdos585.DensityCore
