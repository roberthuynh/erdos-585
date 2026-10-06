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
import Openmath.Proofs.CycleFactors
import Openmath.Proofs.HaarCompositeEvenBlue
import Openmath.Proofs.MatchingCutPaths
import Openmath.Proofs.MatchingComponents
import Openmath.Proofs.HaarCompositeEvenRed

/-! # The even composite Haar exchange

The target is the actual faithful pair for every even parameter at least
four. The concrete exchanged factors are fixed by EvenDefs. Supporting
degree and connectivity facts are proved here without changing the host.
-/

namespace Erdos585.HaarCompositeEven

open SimpleGraph Equiv Equiv.Perm
open HaarComposite

variable (n : ℕ) [NeZero n]

omit [NeZero n] in
set_option maxHeartbeats 2000000 in
lemma cut_neighbor_profile (hn : 4 ≤ n) (v : W n) :
    ((redCuts n).neighborSet v = ∅ ∧ (blueCuts n).neighborSet v = ∅) ∨
    ∃ u w, (redCuts n).neighborSet v = {u} ∧ (blueCuts n).neighborSet v = {w} := by
  classical
  obtain ⟨h01, h0n, h02, h1n, h12, hn2⟩ := color_distinct n (by omega)
  have h1nn : (1 : V n) + (n : V n) ≠ 2 * (n : V n) := by
    intro hh
    apply h1n
    linear_combination hh
  have h10 := Ne.symm h01
  have hn0 := Ne.symm h0n
  have h20 := Ne.symm h02
  have hn1 := Ne.symm h1n
  have h21 := Ne.symm h12
  have h2n := Ne.symm hn2
  have h2nn := Ne.symm h1nn
  by_cases hm : ∃ i, points n i = v
  · obtain ⟨i, rfl⟩ := hm
    refine Or.inr ⟨![b n, a n, d n, c n, f n, e n] i,
      ![f n, c n, b n, e n, d n, a n] i, ?_, ?_⟩
    all_goals
      fin_cases i
      all_goals
        ext w
        rcases w with ⟨x, t⟩
        cases t <;>
          simp_all [points, redCuts, blueCuts, mem_neighborSet, edge_adj,
            a, b, c, d, e, f, add_assoc]
  · have hp : ∀ i, v ≠ points n i := by
      intro i hv
      exact hm ⟨i, hv.symm⟩
    have ha := hp 0
    have hb := hp 1
    have hc := hp 2
    have hd := hp 3
    have he := hp 4
    have hf := hp 5
    left
    constructor <;> ext w <;>
      simp_all [redCuts, blueCuts, mem_neighborSet, edge_adj, points]

lemma exchange_ncard {U : Type*} [Finite U] (G D A : SimpleGraph U)
    (hG : ∀ v, (G.neighborSet v).ncard = 2) (hD : D ≤ G)
    (hA : ∀ v w, A.Adj v w → ¬ G.Adj v w)
    (hprofile : ∀ v,
      (D.neighborSet v = ∅ ∧ A.neighborSet v = ∅) ∨
      ∃ u w, D.neighborSet v = {u} ∧ A.neighborSet v = {w}) (v : U) :
    (((G \ D) ⊔ A).neighborSet v).ncard = 2 := by
  classical
  rw [neighborSet_sup, neighborSet_sdiff]
  rcases hprofile v with ⟨hD0, hA0⟩ | ⟨u, w, hD1, hA1⟩
  · simp [hD0, hA0, hG v]
  · have huD : D.Adj v u := by
      change u ∈ D.neighborSet v
      rw [hD1]
      simp
    have hwA : A.Adj v w := by
      change w ∈ A.neighborSet v
      rw [hA1]
      simp
    have hu : u ∈ G.neighborSet v := hD huD
    have hw : w ∉ G.neighborSet v \ {u} := fun h => hA v w hwA h.1
    rw [hD1, hA1, Set.union_singleton, Set.ncard_insert_of_notMem hw,
      Set.ncard_sdiff_singleton_of_mem hu, hG v]

lemma red_neighbor_ncard (hn : 4 ≤ n) (v : W n) :
    ((red n).neighborSet v).ncard = 2 := by
  apply exchange_ncard _ _ _ (oldRed_neighbor_ncard n (by omega))
    (redCuts_le_old n hn) ?_ (cut_neighbor_profile n hn) v
  intro x y hB hR
  have hB' : s(x, y) ∈ (oldBlue n).edgeSet := blueCuts_le_old n hn hB
  have hR' : s(x, y) ∈ (oldRed n).edgeSet := hR
  exact Set.disjoint_left.mp (old_disjoint n (by omega)) hR' hB'

lemma blue_neighbor_ncard (hn : 4 ≤ n) (v : W n) :
    ((blue n).neighborSet v).ncard = 2 := by
  apply exchange_ncard _ _ _ (oldBlue_neighbor_ncard n (by omega))
    (blueCuts_le_old n hn) ?_ ?_ v
  · intro x y hR hB
    have hR' : s(x, y) ∈ (oldRed n).edgeSet := redCuts_le_old n hn hR
    have hB' : s(x, y) ∈ (oldBlue n).edgeSet := hB
    exact Set.disjoint_left.mp (old_disjoint n (by omega)) hR' hB'
  · intro x
    rcases cut_neighbor_profile n hn x with h | ⟨u, w, hD, hA⟩
    · exact Or.inl h.symm
    · exact Or.inr ⟨w, u, hA, hD⟩

lemma red_isCycles (hn : 4 ≤ n) : (red n).IsCycles :=
  fun {_} _ => red_neighbor_ncard n hn _

lemma blue_isCycles (hn : 4 ≤ n) : (blue n).IsCycles :=
  fun {_} _ => blue_neighbor_ncard n hn _


/-- Transfer a walk using replacement paths, only on its original component. -/
lemma reachable_transfer {U : Type*} {G H : SimpleGraph U} {a b : U}
    (hr : G.Reachable a b)
    (hs : ∀ x y, G.Reachable a x → G.Adj x y → H.Reachable x y) :
    H.Reachable a b := by
  rw [reachable_iff_reflTransGen] at hr
  induction hr with
  | refl => exact Reachable.refl _
  | @tail y z hxy hyz ih =>
    exact ih.trans (hs y z ((reachable_iff_reflTransGen _ _).mpr hxy) hyz)

/-- If all cut endpoints are joined, replacing the cuts preserves each old component. -/
lemma exchange_reachable {U : Type*} (G D A : SimpleGraph U) (p : Fin 6 → U)
    (hcut : ∀ x y, D.Adj x y → (∃ i, p i = x) ∧ (∃ j, p j = y))
    (hjoin : ∀ i j, ((G \ D) ⊔ A).Reachable (p i) (p j))
    {x y : U} (hxy : G.Reachable x y) : ((G \ D) ⊔ A).Reachable x y := by
  apply reachable_transfer hxy
  intro u v _ huv
  by_cases hc : D.Adj u v
  · obtain ⟨⟨i, rfl⟩, ⟨j, rfl⟩⟩ := hcut u v hc
    exact hjoin i j
  · exact (show ((G \ D) ⊔ A).Adj u v from Or.inl ⟨huv, hc⟩).reachable

omit [NeZero n] in
lemma cuts_supported (v w : W n) :
    ((redCuts n).Adj v w ∨ (blueCuts n).Adj v w) →
      (∃ i, points n i = v) ∧ (∃ j, points n j = w) := by
  intro hh
  simp only [redCuts, blueCuts, sup_adj, edge_adj] at hh
  have hmem : ∀ x, x = a n ∨ x = b n ∨ x = c n ∨ x = d n ∨ x = e n ∨ x = f n →
      ∃ i, points n i = x := by
    intro x hx
    rcases hx with h | h | h | h | h | h
    · exact ⟨0, by simpa [points] using h.symm⟩
    · exact ⟨1, by simpa [points] using h.symm⟩
    · exact ⟨2, by simpa [points] using h.symm⟩
    · exact ⟨3, by simpa [points] using h.symm⟩
    · exact ⟨4, by simpa [points] using h.symm⟩
    · exact ⟨5, by simpa [points] using h.symm⟩
  exact ⟨hmem v (by aesop), hmem w (by aesop)⟩

lemma e_reachable_a (hn : 4 ≤ n) : (red n).Reachable (e n) (a n) := by
  classical
  let z : W n := (cutIndex n + (n : V n), true)
  let r := n / 2 - 1
  have hr : 0 < r := by dsimp [r]; omega
  have hrn : r < n := by dsimp [r]; omega
  have hrV : cutIndex n = (r : V n) := rfl
  have hz : residue n (cutIndex n) ≠ 0 := by
    rw [hrV, map_natCast]
    intro hh
    have hv := congrArg ZMod.val hh
    rw [ZMod.val_natCast_of_lt hrn, ZMod.val_zero] at hv
    omega
  have hout : cutIndex n + (n : V n) ∉ Set.range (mark n) := by
    rw [mem_range_mark_iff_val_lt]
    have hlt : r + n < n * n := by dsimp [r] at *; nlinarith
    rw [hrV, ← Nat.cast_add, ZMod.val_natCast_of_lt hlt]
    omega
  have h0 : matchRed0 n (cutIndex n + (n : V n)) = cutIndex n + (n : V n) := by
    rw [matchRed0_fixed n _ hout]
    change (if residue n (cutIndex n + (n : V n)) = 0 then _ else _) = _
    simp only [map_add, residue_nat, add_zero, hz, ↓reduceIte]
  have h1 : matchRed1 n (cutIndex n) = cutIndex n + (n : V n) := by
    change (if residue n (cutIndex n) = 0 then _ else _) = _
    rw [if_neg hz]
  have hez : (oldRed n).Adj (e n) z :=
    (HaarPair.factor_cross _ _ _ _).mpr (Or.inl h0.symm)
  have haz : (oldRed n).Adj (a n) z :=
    (HaarPair.factor_cross _ _ _ _).mpr (Or.inr h1.symm)
  obtain ⟨h01, h0n, h02, h1n, h12, hn2⟩ := color_distinct n (by omega)
  have h10 := Ne.symm h01
  have hn0 := Ne.symm h0n
  have hn1 := Ne.symm h1n
  have h2n := Ne.symm hn2
  have hez' : (red n).Adj (e n) z := by
    apply Or.inl
    refine ⟨hez, ?_⟩
    simp_all [redCuts, edge_adj, e, z, a, b, c, d, f, add_assoc]
  have haz' : (red n).Adj (a n) z := by
    apply Or.inl
    refine ⟨haz, ?_⟩
    simp_all [redCuts, edge_adj, e, z, a, b, c, d, f, add_assoc]
  exact hez'.reachable.trans haz'.symm.reachable


lemma red_points_joined (hn : 4 ≤ n) (hbd : (red n).Reachable (b n) (d n)) :
    ∀ i j, (red n).Reachable (points n i) (points n j) := by
  have hbc : (red n).Adj (b n) (c n) := by
    simp [red, blueCuts, edge_adj, b, c]
  have hde : (red n).Adj (d n) (e n) := by
    simp [red, blueCuts, edge_adj, d, e]
  have hfa : (red n).Adj (f n) (a n) := by
    simp [red, blueCuts, edge_adj, f, a]
  have hae := (e_reachable_a n hn).symm
  have had := hae.trans hde.symm.reachable
  have hab := had.trans hbd.symm
  have hall : ∀ i, (red n).Reachable (a n) (points n i) := by
    intro i
    fin_cases i
    · exact Reachable.refl _
    · exact hab
    · exact hab.trans hbc.reachable
    · exact had
    · exact hae
    · exact hfa.symm.reachable
  exact fun i j => (hall i).symm.trans (hall j)

lemma blue_points_joined
    (hac : (blue n).Reachable (a n) (c n))
    (hbf : (blue n).Reachable (b n) (f n)) :
    ∀ i j, (blue n).Reachable (points n i) (points n j) := by
  have hab : (blue n).Adj (a n) (b n) := by
    simp [blue, redCuts, edge_adj, a, b]
  have hcd : (blue n).Adj (c n) (d n) := by
    simp [blue, redCuts, edge_adj, c, d]
  have hef : (blue n).Adj (e n) (f n) := by
    simp [blue, redCuts, edge_adj, e, f]
  have haf := hab.reachable.trans hbf
  have hall : ∀ i, (blue n).Reachable (a n) (points n i) := by
    intro i
    fin_cases i
    · exact Reachable.refl _
    · exact hab.reachable
    · exact hac
    · exact hac.trans hcd.reachable
    · exact haf.trans hef.symm.reachable
    · exact haf
  exact fun i j => (hall i).symm.trans (hall j)

lemma blue_cut_orbits (hn : 4 ≤ n) (he : Even n) :
    (HaarComposite.blue n).SameCycle (cutIndex n) (mark n (1 : ZMod n)) ∧
    (HaarComposite.blue n).SameCycle (cutIndex n + 1) (mark n (1 : ZMod n)) ∧
    (HaarComposite.blue n).SameCycle (cutIndex n + (n : V n)) 0 := by
  let r := n / 2 - 1
  have hr : 0 < r := by dsimp [r]; omega
  have hr1 : r + 1 < n := by dsimp [r]; omega
  have hrn : r < n := by omega
  have hm : mark n (r : ZMod n) = cutIndex n := by
    simp [mark, ZMod.val_natCast_of_lt hrn, cutIndex, r]
  have hm1 : mark n ((r+1 : ℕ) : ZMod n) = cutIndex n + 1 := by
    rw [mark, ZMod.val_natCast_of_lt hr1, Nat.cast_add, Nat.cast_one]
    rfl
  have hpos : (r : ZMod n) ≠ 0 := by
    intro hh
    have hv := congrArg ZMod.val hh
    rw [ZMod.val_natCast_of_lt hrn, ZMod.val_zero] at hv
    omega
  have hpos1 : ((r+1 : ℕ) : ZMod n) ≠ 0 := by
    intro hh
    have hv := congrArg ZMod.val hh
    rw [ZMod.val_natCast_of_lt hr1, ZMod.val_zero] at hv
    omega
  refine ⟨?_, ?_, ?_⟩
  · simpa [hm] using HaarCompositeEvenBlue.blue_mark_one n hn he (r : ZMod n) hpos
  · simpa only [hm1] using HaarCompositeEvenBlue.blue_mark_one n hn he
      ((r+1 : ℕ) : ZMod n) hpos1
  · have hnat : n + n/2 - 1 = r + n := by dsimp [r]; omega
    simpa [hnat, Nat.cast_add, cutIndex, r] using
      HaarCompositeEvenBlue.blue_special_zero n hn he

/-- Removing one edge outside the starting component does not affect its paths. -/
lemma reachable_avoid_edge {U : Type*} {F G : SimpleGraph U} {a b d e : U}
    (hFG : F ≤ G) (hde : G.Adj d e) (hnot : ¬ G.Reachable a e)
    (hab : F.Reachable a b) : (F \ edge d e).Reachable a b := by
  apply reachable_transfer hab
  intro x y hax hxy
  apply Adj.reachable
  refine ⟨hxy, ?_⟩
  intro hexy
  have hx : G.Reachable a x := hax.mono hFG
  simp only [edge_adj] at hexy
  rcases hexy with ⟨⟨rfl, rfl⟩, _⟩ | ⟨⟨rfl, rfl⟩, _⟩
  · exact hnot (hx.trans hde.reachable)
  · exact hnot hx


lemma blue_cut_matching_value (hn : 4 ≤ n) :
    matchBlue0 n (cutIndex n + 1) = cutIndex n + 1 := by
  let r := n/2-1
  have hr1 : r + 1 < n := by dsimp [r]; omega
  have hm : mark n ((r+1 : ℕ) : ZMod n) = cutIndex n + 1 := by
    rw [mark, ZMod.val_natCast_of_lt hr1, Nat.cast_add, Nat.cast_one]
    rfl
  have hz : residue n (cutIndex n + 1) ≠ 0 := by
    change residue n ((r : V n) + 1) ≠ 0
    rw [← Nat.cast_one, ← Nat.cast_add, map_natCast]
    intro hh
    have hv := congrArg ZMod.val hh
    rw [ZMod.val_natCast_of_lt hr1, ZMod.val_zero] at hv
    omega
  rw [← hm, matchBlue0_mark, hm]
  change (if residue n (cutIndex n + 1) = 0 then _ else _) = _
  rw [if_neg hz]

lemma blue_surviving_paths (hn : 4 ≤ n) (he : Even n) :
    (blue n).Reachable (a n) (c n) ∧ (blue n).Reachable (b n) (f n) := by
  let P := matchBlue0 n
  let Q := matchBlue1 n
  let F := MatchingCutPaths.cutFactor P Q (cutIndex n) (cutIndex n + 1)
  obtain ⟨ha, hc, he0⟩ := blue_cut_orbits n hn he
  have hne : ∀ x, P x ≠ Q x := fun x => (matching_facts n (by omega) x).2.2.1
  have hcycle : (Q⁻¹ * P).SameCycle (cutIndex n) (cutIndex n + 1) := by
    rw [blue_successor]
    exact ha.trans hc.symm
  have hP : P (cutIndex n + 1) = cutIndex n + 1 := blue_cut_matching_value n hn
  have hQ : Q (cutIndex n) = cutIndex n + 2 * (n : V n) := rfl
  have hF : F ≤ oldBlue n := fun _ _ h => h.1
  have hno : ∀ x, (HaarComposite.blue n).SameCycle x (mark n (1 : ZMod n)) →
      ¬ (oldBlue n).Reachable (x, false) (e n) := by
    intro x hx hxe
    have hh := MatchingComponents.sameCycle_of_reachable P Q hxe
    change (Q⁻¹ * P).SameCycle x (cutIndex n + (n : V n)) at hh
    rw [blue_successor] at hh
    exact HaarCompositeEvenBlue.blue_zero_not_one n hn he
      (he0.symm.trans (hh.symm.trans hx))
  have haE : ¬ (oldBlue n).Reachable (a n) (e n) := hno _ ha
  have hcE : ¬ (oldBlue n).Reachable (c n) (e n) := hno _ hc
  have hbE : ¬ (oldBlue n).Reachable (b n) (e n) := by
    intro hh
    exact hcE ((cut_edges n hn).2.2.2.1.symm.reachable.trans hh)
  have hde : (oldBlue n).Adj (d n) (e n) := (cut_edges n hn).2.2.2.2.1
  have hsub : F \ edge (d n) (e n) ≤ blue n := by
    intro x y hxy
    have hgood := hxy.1.1
    have hcut := hxy.1.2
    change ¬ (edge (cutIndex n + 1, false) (P (cutIndex n + 1), true) ⊔
      edge (cutIndex n, false) (Q (cutIndex n), true)).Adj x y at hcut
    rw [hP, hQ] at hcut
    change ¬ (edge (c n) (b n) ⊔ edge (a n) (f n)).Adj x y at hcut
    apply Or.inl
    refine ⟨hgood, ?_⟩
    intro hbad
    simp only [blueCuts, sup_adj] at hbad
    rcases hbad with (hbc | hde') | hfa
    · apply hcut
      left
      rwa [edge_comm]
    · exact hxy.2 hde'
    · apply hcut
      right
      rwa [edge_comm]
  have hacF : F.Reachable (a n) (c n) :=
    MatchingCutPaths.left_reachable P Q hne _ _ hcycle
  have hbfF : F.Reachable (b n) (f n) := by
    have hh := MatchingCutPaths.right_reachable P Q hne _ _ hcycle
    simpa only [hP, hQ, F, b, f] using hh
  exact ⟨(reachable_avoid_edge hF hde haE hacF).mono hsub,
    (reachable_avoid_edge hF hde hbE hbfF).mono hsub⟩

lemma red_connected (hn : 4 ≤ n) (he : Even n) (v : W n) :
    (red n).Reachable (a n) v := by
  have hjoin := red_points_joined n hn
    (HaarCompositeEvenRed.b_reachable_d n hn he)
  apply exchange_reachable (oldRed n) (redCuts n) (blueCuts n) (points n)
    (fun x y h => cuts_supported n x y (Or.inl h)) hjoin
  apply (MatchingComponents.reachable_iff_sameCycle
    (matchRed0 n) (matchRed1 n) _ _).mpr
  rw [red_successor]
  exact (red_isCycleOn n).2 (Set.mem_univ _) (Set.mem_univ _)

lemma blue_connected (hn : 4 ≤ n) (he : Even n) (v : W n) :
    (blue n).Reachable (a n) v := by
  obtain ⟨hac, hbf⟩ := blue_surviving_paths n hn he
  have hjoin := blue_points_joined n hac hbf
  have htransfer : ∀ {x y}, (oldBlue n).Reachable x y → (blue n).Reachable x y :=
    fun h => exchange_reachable (oldBlue n) (blueCuts n) (redCuts n) (points n)
      (fun x y h => cuts_supported n x y (Or.inr h)) hjoin h
  let z := MatchingComponents.label (matchBlue0 n) v
  have ha1 := (blue_cut_orbits n hn he).1
  have he0 := (blue_cut_orbits n hn he).2.2
  rcases HaarCompositeEvenBlue.blue_partition n hn he z with hz | hz
  · have hev : (oldBlue n).Reachable (e n) v := by
      apply (MatchingComponents.reachable_iff_sameCycle _ _ _ _).mpr
      change ((matchBlue1 n)⁻¹ * matchBlue0 n).SameCycle
        (cutIndex n + (n : V n)) z
      rw [blue_successor]
      exact he0.trans hz.symm
    exact (hjoin 0 4).trans (htransfer hev)
  · have hav : (oldBlue n).Reachable (a n) v := by
      apply (MatchingComponents.reachable_iff_sameCycle _ _ _ _).mpr
      change ((matchBlue1 n)⁻¹ * matchBlue0 n).SameCycle (cutIndex n) z
      rw [blue_successor]
      exact ha1.trans hz.symm
    exact htransfer hav

/-- Every even composite parameter at least four has a faithful pair of actual cycles. -/
theorem hasPair (hn : 4 ≤ n) (he : Even n) : HasPairF (Haar.graph (colors n)) := by
  apply CycleFactors.hasPair_of_connected_factors (Haar.graph (colors n))
    (red n) (blue n) (a n) (red_isCycles n hn) (blue_isCycles n hn)
    ?_ ?_ (red_connected n hn he) (blue_connected n hn he)
    (red_le n hn) (blue_le n hn) (red_blue_disjoint n hn)
  · exact Set.nonempty_of_ncard_ne_zero (by rw [red_neighbor_ncard n hn]; decide)
  · exact Set.nonempty_of_ncard_ne_zero (by rw [blue_neighbor_ncard n hn]; decide)

omit [NeZero n] in
/-- The odd and even constructions together cover every parameter at least three. -/
theorem hasPair_all (hn : 3 ≤ n) : HasPairF (Haar.graph (colors n)) := by
  let : NeZero n := ⟨by omega⟩
  rcases Nat.even_or_odd n with he | ho
  · have hn4 : 4 ≤ n := by
      obtain ⟨k, hk⟩ := he
      omega
    exact hasPair n hn4 he
  · exact HaarComposite.hasPair n hn ho

omit [NeZero n] in
/-- The all-parameter theorem in the original upstream cycle predicate. -/
theorem hasTwoEdgeDisjointCyclesSameVertexSet_all (hn : 3 ≤ n) :
    HasTwoEdgeDisjointCyclesSameVertexSet (Haar.graph (colors n)) :=
  (hasPairF_iff _).mp (hasPair_all n hn)

end Erdos585.HaarCompositeEven
