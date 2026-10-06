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
import Openmath.Proofs.HaarComposite

/-! # Actual graphs in the even composite Haar six-edge exchange

These definitions retain the actual host and its actual old matching
factors. The exchange is a symmetric graph-edge replacement, not an
assumed permutation orbit. Connectivity is a separate obligation.
-/

namespace Erdos585.HaarCompositeEven

open SimpleGraph Equiv Equiv.Perm
open HaarComposite

abbrev W (n : ℕ) := V n × Bool

def cutIndex (n : ℕ) : V n := ((n / 2 - 1 : ℕ) : V n)

def a (n : ℕ) : W n := (cutIndex n, false)
def b (n : ℕ) : W n := (cutIndex n + 1, true)
def c (n : ℕ) : W n := (cutIndex n + 1, false)
def d (n : ℕ) : W n := (cutIndex n + 1 + (n : V n), true)
def e (n : ℕ) : W n := (cutIndex n + (n : V n), false)
def f (n : ℕ) : W n := (cutIndex n + 2 * (n : V n), true)

noncomputable def oldRed (n : ℕ) [NeZero n] : SimpleGraph (W n) :=
  HaarPair.matchingFactor (matchRed0 n) (matchRed1 n)

noncomputable def oldBlue (n : ℕ) [NeZero n] : SimpleGraph (W n) :=
  HaarPair.matchingFactor (matchBlue0 n) (matchBlue1 n)

def redCuts (n : ℕ) : SimpleGraph (W n) :=
  edge (a n) (b n) ⊔ edge (c n) (d n) ⊔ edge (e n) (f n)

def blueCuts (n : ℕ) : SimpleGraph (W n) :=
  edge (b n) (c n) ⊔ edge (d n) (e n) ⊔ edge (f n) (a n)

noncomputable def red (n : ℕ) [NeZero n] : SimpleGraph (W n) :=
  (oldRed n \ redCuts n) ⊔ blueCuts n

noncomputable def blue (n : ℕ) [NeZero n] : SimpleGraph (W n) :=
  (oldBlue n \ blueCuts n) ⊔ redCuts n

variable (n : ℕ) [NeZero n]

lemma oldRed_le (hn : 3 ≤ n) : oldRed n ≤ Haar.graph (colors n) := by
  apply HaarPair.factor_le
  · intro x
    exact (Haar.graph_cross _ _ _).mpr (matching_facts n hn x).1.1
  · intro x
    exact (Haar.graph_cross _ _ _).mpr (matching_facts n hn x).1.2.1

lemma oldBlue_le (hn : 3 ≤ n) : oldBlue n ≤ Haar.graph (colors n) := by
  apply HaarPair.factor_le
  · intro x
    exact (Haar.graph_cross _ _ _).mpr (matching_facts n hn x).1.2.2.1
  · intro x
    exact (Haar.graph_cross _ _ _).mpr (matching_facts n hn x).1.2.2.2

lemma old_disjoint (hn : 3 ≤ n) :
    Disjoint (oldRed n).edgeSet (oldBlue n).edgeSet := by
  apply HaarPair.factors_edge_disjoint
  intro x
  exact (matching_facts n hn x).2.2.2

/-- Edge replacement cannot leave the actual host when both cut graphs
are contained in the corresponding old factors. -/
lemma exchanged_le (hn : 3 ≤ n)
    (hr : redCuts n ≤ oldRed n) (hb : blueCuts n ≤ oldBlue n) :
    red n ≤ Haar.graph (colors n) ∧ blue n ≤ Haar.graph (colors n) := by
  constructor
  · exact sup_le (le_trans sdiff_le (oldRed_le n hn)) (le_trans hb (oldBlue_le n hn))
  · exact sup_le (le_trans sdiff_le (oldBlue_le n hn)) (le_trans hr (oldRed_le n hn))

/-- The actual old disjoint factors stay edge-disjoint after exchanging
subgraphs contained in their respective edge sets. -/
lemma exchanged_disjoint (hn : 3 ≤ n)
    (hr : redCuts n ≤ oldRed n) (hb : blueCuts n ≤ oldBlue n) :
    Disjoint (red n).edgeSet (blue n).edgeSet := by
  apply Set.disjoint_left.mpr
  intro z hzR hzB
  induction z using Sym2.inductionOn with
  | _ u v =>
    change (red n).Adj u v at hzR
    change (blue n).Adj u v at hzB
    have hdis : ¬ ((oldRed n).Adj u v ∧ (oldBlue n).Adj u v) := by
      rintro ⟨hR, hB⟩
      have heR : s(u, v) ∈ (oldRed n).edgeSet := hR
      have heB : s(u, v) ∈ (oldBlue n).edgeSet := hB
      exact Set.disjoint_left.mp (old_disjoint n hn) heR heB
    simp only [red, blue, sup_adj, sdiff_adj] at hzR hzB
    rcases hzR with ⟨hR, hnR⟩ | hCB <;> rcases hzB with ⟨hB, hnB⟩ | hCR
    · exact hdis ⟨hR, hB⟩
    · exact hnR hCR
    · exact hnB hCB
    · exact hdis ⟨hr hCR, hb hCB⟩

omit [NeZero n] in
private lemma mark_nat (j : ℕ) (hj : j < n) :
    mark n (j : ZMod n) = (j : V n) := by
  simp [mark, ZMod.val_natCast_of_lt hj]

omit [NeZero n] in
private lemma residue_natCast_ne_zero (j : ℕ) (hj : 0 < j) (hjn : j < n) :
    residue n (j : V n) ≠ 0 := by
  intro hh
  have hv := congrArg ZMod.val hh
  have hr : residue n (j : V n) = (j : ZMod n) := map_natCast _ _
  rw [hr, ZMod.val_natCast_of_lt hjn, ZMod.val_zero] at hv
  omega

lemma cut_edges (hn : 4 ≤ n) :
    (oldRed n).Adj (a n) (b n) ∧
    (oldRed n).Adj (c n) (d n) ∧
    (oldRed n).Adj (e n) (f n) ∧
    (oldBlue n).Adj (b n) (c n) ∧
    (oldBlue n).Adj (d n) (e n) ∧
    (oldBlue n).Adj (f n) (a n) := by
  let r := n / 2 - 1
  have hr : 0 < r := by dsimp [r]; omega
  have hrn : r + 1 < n := by dsimp [r]; omega
  have hrn' : r < n := by omega
  have hrV : cutIndex n = (r : V n) := rfl
  have hm : mark n (r : ZMod n) = cutIndex n := by
    exact mark_nat n r hrn'
  have hm' : mark n ((r + 1 : ℕ) : ZMod n) = cutIndex n + 1 := by
    rw [mark_nat n (r + 1) hrn, Nat.cast_add, Nat.cast_one, ← hrV]
  have hz : residue n (cutIndex n) ≠ 0 := by
    rw [hrV]
    exact residue_natCast_ne_zero n r hr hrn'
  have hz' : residue n (cutIndex n + 1) ≠ 0 := by
    rw [hrV, ← Nat.cast_one, ← Nat.cast_add]
    exact residue_natCast_ne_zero n (r + 1) (by omega) hrn
  have hmark0 : matchRed0 n (cutIndex n) = cutIndex n + 1 := by
    simpa only [hm] using matchRed0_mark n (r : ZMod n)
  have hmark1 : matchBlue0 n (cutIndex n + 1) = cutIndex n + 1 := by
    rw [← hm', matchBlue0_mark]
    rw [hm']
    change (if residue n (cutIndex n + 1) = 0 then _ else _) = _
    rw [if_neg hz']
  have hout : cutIndex n + (n : V n) ∉ Set.range (mark n) := by
    rw [mem_range_mark_iff_val_lt]
    have hlt : r + n < n * n := by dsimp [r] at *; nlinarith
    rw [hrV, ← Nat.cast_add, ZMod.val_natCast_of_lt hlt]
    omega
  have hblue : matchBlue0 n (cutIndex n + (n : V n)) =
      cutIndex n + 1 + (n : V n) := by
    rw [matchBlue0_fixed n _ hout]
    abel
  constructor
  · apply (HaarPair.factor_cross _ _ _ _).mpr
    exact Or.inl hmark0.symm
  constructor
  · apply (HaarPair.factor_cross _ _ _ _).mpr
    right
    change cutIndex n + 1 + (n : V n) =
      if residue n (cutIndex n + 1) = 0 then _ else _
    rw [if_neg hz']
  constructor
  · apply (HaarPair.factor_cross _ _ _ _).mpr
    right
    simp only [matchRed1, Equiv.coe_fn_mk, map_add, residue_nat, add_zero, hz,
      ↓reduceIte]
    ring
  constructor
  · apply SimpleGraph.Adj.symm
    apply (HaarPair.factor_cross _ _ _ _).mpr
    exact Or.inl hmark1.symm
  constructor
  · apply SimpleGraph.Adj.symm
    apply (HaarPair.factor_cross _ _ _ _).mpr
    exact Or.inl hblue.symm
  · apply SimpleGraph.Adj.symm
    apply (HaarPair.factor_cross _ _ _ _).mpr
    right
    rfl

lemma redCuts_le_old (hn : 4 ≤ n) : redCuts n ≤ oldRed n := by
  obtain ⟨hab, hcd, hef, _⟩ := cut_edges n hn
  exact sup_le (sup_le ((edge_le_iff _).mpr (Or.inr hab))
    ((edge_le_iff _).mpr (Or.inr hcd))) ((edge_le_iff _).mpr (Or.inr hef))

lemma blueCuts_le_old (hn : 4 ≤ n) : blueCuts n ≤ oldBlue n := by
  obtain ⟨_, _, _, hbc, hde, hfa⟩ := cut_edges n hn
  exact sup_le (sup_le ((edge_le_iff _).mpr (Or.inr hbc))
    ((edge_le_iff _).mpr (Or.inr hde))) ((edge_le_iff _).mpr (Or.inr hfa))

lemma red_le (hn : 4 ≤ n) : red n ≤ Haar.graph (colors n) :=
  (exchanged_le n (by omega) (redCuts_le_old n hn) (blueCuts_le_old n hn)).1

lemma blue_le (hn : 4 ≤ n) : blue n ≤ Haar.graph (colors n) :=
  (exchanged_le n (by omega) (redCuts_le_old n hn) (blueCuts_le_old n hn)).2

lemma red_blue_disjoint (hn : 4 ≤ n) :
    Disjoint (red n).edgeSet (blue n).edgeSet :=
  exchanged_disjoint n (by omega) (redCuts_le_old n hn) (blueCuts_le_old n hn)

def points (n : ℕ) : Fin 6 → W n := ![a n, b n, c n, d n, e n, f n]

omit [NeZero n] in
lemma points_injective (hn : 4 ≤ n) : Function.Injective (points n) := by
  obtain ⟨h01, h0n, h02, h1n, h12, hn2⟩ := color_distinct n (by omega)
  have h1nn : (1 : V n) + (n : V n) ≠ 2 * (n : V n) := by
    intro hh
    apply h1n
    linear_combination hh
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [points, a, b, c, d, e, f, add_assoc]

lemma factor_neighbor_ncard {U : Type*} [Finite U] (p q : Perm U)
    (hne : ∀ x, p x ≠ q x) (v : U × Bool) :
    ((HaarPair.matchingFactor p q).neighborSet v).ncard = 2 := by
  classical
  rcases v with ⟨x, b⟩
  cases b
  · have he : (HaarPair.matchingFactor p q).neighborSet (x, false) =
        {(p x, true), (q x, true)} := by
      ext ⟨y, b⟩
      cases b
      · simp [HaarPair.factor_same]
      · simpa using HaarPair.factor_cross p q x y
    rw [he]
    have hd : (p x, true) ≠ (q x, true) := fun h => hne x (congrArg Prod.fst h)
    simp [hd]
  · have he : (HaarPair.matchingFactor p q).neighborSet (x, true) =
        {(p.symm x, false), (q.symm x, false)} := by
      ext ⟨y, b⟩
      cases b
      · simp only [mem_neighborSet, Set.mem_insert_iff, Set.mem_singleton_iff,
          Prod.mk.injEq, and_true]
        rw [SimpleGraph.adj_comm, HaarPair.factor_cross]
        simp only [Equiv.eq_symm_apply, eq_comm]
      · simp [HaarPair.factor_same]
    rw [he]
    have hi : p.symm x ≠ q.symm x := by
      intro hh
      apply hne (p.symm x)
      rw [p.apply_symm_apply, hh, q.apply_symm_apply]
    have hd : (p.symm x, false) ≠ (q.symm x, false) :=
      fun h => hi (congrArg Prod.fst h)
    simp [hd]

lemma oldRed_neighbor_ncard (hn : 3 ≤ n) (v : W n) :
    ((oldRed n).neighborSet v).ncard = 2 :=
  factor_neighbor_ncard _ _ (fun x => (matching_facts n hn x).2.1) v

lemma oldBlue_neighbor_ncard (hn : 3 ≤ n) (v : W n) :
    ((oldBlue n).neighborSet v).ncard = 2 :=
  factor_neighbor_ncard _ _ (fun x => (matching_facts n hn x).2.2.1) v

end Erdos585.HaarCompositeEven
