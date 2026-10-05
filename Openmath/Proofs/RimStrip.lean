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
import Openmath.Proofs.RimDensity

/-! # An explicit rim strip for the two-hub construction -/
open SimpleGraph Finset
namespace Erdos585.RimStrip

def forward (a b : ℕ) : Prop :=
  a + 1 = b ∨ (b % 2 = 0 ∧ a + 4 = b) ∨
    (b % 2 = 1 ∧ a + 8 = b) ∨ (a = 0 ∧ b = 5) ∨ (a = 2 ∧ b = 7)

def graph : SimpleGraph ℕ where
  Adj a b := forward a b ∨ forward b a
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by intro a h; simp only [forward] at h; omega⟩

instance : DecidableRel graph.Adj := by
  intro a b
  unfold graph forward
  infer_instance

def back (n : ℕ) : ℕ := if n % 2 = 0 then n - 4 else n - 8

lemma earlier_neighbors {n x : ℕ} (hn : 8 ≤ n) (hx : x < n) :
    graph.Adj x n ↔ x = n - 1 ∨ x = back n := by
  simp only [graph, forward, back]
  split_ifs <;> omega

/-- Every new rim vertex joins two distinct old vertices at distance at least three. -/
theorem far_ear {n : ℕ} (hn : 8 ≤ n) :
    n - 1 < n ∧ back n < n ∧ n - 1 ≠ back n ∧
    ¬ graph.Adj (n - 1) (back n) ∧
    ∀ x < n, ¬ (graph.Adj (n - 1) x ∧ graph.Adj (back n) x) := by
  have h1 : n - 1 < n := by omega
  have h2 : back n < n := by unfold back; split_ifs <;> omega
  have h3 : n - 1 ≠ back n := by unfold back; split_ifs <;> omega
  refine ⟨h1, h2, h3, ?_, ?_⟩
  · intro ha
    simp only [graph, forward, back] at ha
    split_ifs at ha <;> omega
  · intro x hx ⟨hax, hbx⟩
    simp only [graph, forward, back] at hax hbx
    split_ifs at hbx <;> omega

lemma no_square_at_max {a b x y : ℕ} (ha : 8 ≤ a) (hb : b < a)
    (hx : x < a) (hy : y < a) (hxy : x ≠ y)
    (hax : graph.Adj a x) (hay : graph.Adj a y)
    (hbx : graph.Adj b x) (hby : graph.Adj b y) : False := by
  have hx' := (earlier_neighbors ha hx).mp hax.symm
  have hy' := (earlier_neighbors ha hy).mp hay.symm
  have hf := (far_ear ha).2.2.2.2
  rcases hx' with rfl | rfl <;> rcases hy' with rfl | rfl
  · exact hxy rfl
  · exact hf b hb ⟨hbx.symm,hby.symm⟩
  · exact hf b hb ⟨hby.symm,hbx.symm⟩
  · exact hxy rfl

set_option synthInstance.maxSize 2048 in
set_option maxRecDepth 32768 in
lemma small_no_square : ∀ a b x y : Fin 8, a ≠ b → x ≠ y →
    graph.Adj a.val x.val → graph.Adj a.val y.val →
    graph.Adj b.val x.val → graph.Adj b.val y.val → False := by decide

/-- The whole infinite strip has no four-cycle. -/
theorem no_square : RimDensity.NoSquare graph := by
  intro a b x y hab hxy hax hay hbx hby
  have hax' := graph.ne_of_adj hax
  have hay' := graph.ne_of_adj hay
  have hbx' := graph.ne_of_adj hbx
  have hby' := graph.ne_of_adj hby
  by_cases ha : a < 8 ∧ b < 8 ∧ x < 8 ∧ y < 8
  · exact small_no_square ⟨a,ha.1⟩ ⟨b,ha.2.1⟩ ⟨x,ha.2.2.1⟩ ⟨y,ha.2.2.2⟩
      (fun h => hab (congrArg Fin.val h)) (fun h => hxy (congrArg Fin.val h))
      hax hay hbx hby
  by_cases ham : b < a ∧ x < a ∧ y < a
  · exact no_square_at_max (by omega) ham.1 ham.2.1 ham.2.2 hxy hax hay hbx hby
  by_cases hbm : a < b ∧ x < b ∧ y < b
  · exact no_square_at_max (by omega) hbm.1 hbm.2.1 hbm.2.2 hxy hbx hby hax hay
  by_cases hxm : a < x ∧ b < x ∧ y < x
  · exact no_square_at_max (by omega) hxm.2.2 hxm.1 hxm.2.1 hab
      hax.symm hbx.symm hay.symm hby.symm
  · exact no_square_at_max (by omega) (by omega) (by omega) (by omega) hab
      hay.symm hby.symm hax.symm hbx.symm

set_option maxRecDepth 32768 in
lemma seed_sparse : ∀ S ∈ (range 8).powerset, 5 ≤ S.card →
    (RimDensity.edges graph S).card + 5 ≤ 2 * S.card := by decide

/-- Every rim set of at least five vertices has at most twice its order minus five edges. -/
theorem sparse (S : Finset ℕ) (hS : 5 ≤ S.card) :
    (RimDensity.edges graph S).card + 5 ≤ 2 * S.card := by
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    have hn : S.Nonempty := card_pos.mp (by omega)
    let v := S.max' hn
    have hv : v ∈ S := max'_mem _ _
    have hmax : ∀ x ∈ S, x ≤ v := fun x hx => le_max' _ _ hx
    by_cases hv8 : v < 8
    · apply seed_sparse S (mem_powerset.mpr ?_) hS
      intro x hx
      exact mem_range.mpr ((hmax x hx).trans_lt hv8)
    have hv8' : 8 ≤ v := by omega
    let T := S.erase v
    let N := T.filter (graph.Adj v)
    have hvT : v ∉ T := by simp [T]
    have hTs : T ⊂ S := erase_ssubset hv
    have hcT : T.card + 1 = S.card := card_erase_add_one hv
    have hTlt : ∀ x ∈ T, x < v := by
      intro x hx
      have hh := mem_erase.mp hx
      have hm := hmax x hh.2
      omega
    have hNsub : N ⊆ {v - 1,back v} := by
      intro x hx
      have hxt := (mem_filter.mp hx).1
      have ha := (mem_filter.mp hx).2
      have hh := (earlier_neighbors hv8' (hTlt x hxt)).mp ha.symm
      simpa using hh
    have hN : N.card ≤ 2 := (card_le_card hNsub).trans (card_le_two)
    have hcount : (RimDensity.edges graph S).card =
        (RimDensity.edges graph T).card + N.card := by
      have he : insert v T = S := insert_erase hv
      rw [← he]
      exact RimDensity.edges_insert_card graph T v hvT
    by_cases hT5 : 5 ≤ T.card
    · have ht := ih T hTs hT5
      omega
    have hT4 : T.card = 4 := by omega
    have ht4 := (RimDensity.four_bounds graph hT4).1 no_square
    by_cases hn1 : N.card ≤ 1
    · omega
    have hN2 : N.card = 2 := by omega
    have hf := far_ear hv8'
    have hne := hf.2.2.1
    have hNeq : N = {v - 1,back v} := eq_of_subset_of_card_le hNsub (by simp [hne,hN2])
    have haT : v - 1 ∈ T := (mem_filter.mp (show v - 1 ∈ N by rw [hNeq]; simp)).1
    have hbT : back v ∈ T := (mem_filter.mp (show back v ∈ N by rw [hNeq]; simp)).1
    have ht3 := (RimDensity.four_bounds graph hT4).2 (v-1) haT (back v) hbT
      hne hf.2.2.2.1 (fun x hx => hf.2.2.2.2 x (hTlt x hx))
    omega

lemma earlier_neighbor_set {n : ℕ} (hn : 8 ≤ n) :
    (range n).filter (graph.Adj n) = {n-1,back n} := by
  ext x
  have hf := far_ear hn
  constructor
  · intro hx
    have h := (earlier_neighbors hn (mem_range.mp (mem_filter.mp hx).1)).mp
      (mem_filter.mp hx).2.symm
    simpa using h
  · intro hx
    have hx' : x = n-1 ∨ x = back n := by simpa using hx
    have hxn : x < n := hx'.elim (fun h => h ▸ hf.1) (fun h => h ▸ hf.2.1)
    exact mem_filter.mpr ⟨mem_range.mpr hxn, ((earlier_neighbors hn hxn).mpr hx').symm⟩

/-- The strip has exactly two edges per vertex beyond its eight-vertex seed. -/
theorem edge_count (n : ℕ) (hn : 8 ≤ n) :
    (RimDensity.edges graph (range n)).card + 5 = 2 * n := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    rw [range_add_one, RimDensity.edges_insert_card graph _ _ (by simp),
      earlier_neighbor_set hn]
    have hne := (far_ear hn).2.2.1
    simp only [card_pair hne]
    omega

end Erdos585.RimStrip
