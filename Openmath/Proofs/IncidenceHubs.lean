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
import Openmath.Proofs.TwoHubFamily

/-! # A square-free incidence obstruction with two exceptional vertices -/
open SimpleGraph Finset
namespace Erdos585.IncidenceHubs

/-- In a square-free incidence relation, right degree four and left degree at most
three force at least three more selected left vertices than selected right vertices. -/
theorem incidence_gap {L P : Type*} [DecidableEq L] [DecidableEq P]
    (r : L → P → Prop) [DecidableRel r] (A : Finset L) (B : Finset P)
    (hb : B.Nonempty)
    (hfour : ∀ y ∈ B, (A.filter fun x => r x y).card = 4)
    (hthree : ∀ x ∈ A, (B.filter (r x)).card ≤ 3)
    (hsq : ∀ y ∈ B, ∀ z ∈ B, y ≠ z → ∀ a ∈ A, ∀ b ∈ A,
      r a y → r a z → r b y → r b z → a = b) :
    B.card + 3 ≤ A.card := by
  obtain ⟨y,hy⟩ := hb
  let D := A.filter fun x => r x y
  let C := A \ D
  have hD : D.card = 4 := hfour y hy
  have hDA : D ⊆ A := filter_subset _ _
  have hC : C.card + D.card = A.card := card_sdiff_add_card_eq_card hDA
  have hlow : ∀ z ∈ B.erase y, 3 ≤ (C.filter fun x => r x z).card := by
    intro z hz
    have hzy := (mem_erase.mp hz).1
    have hzB := (mem_erase.mp hz).2
    have hone : (D.filter fun x => r x z).card ≤ 1 := by
      apply card_le_one.mpr
      intro a ha b hb
      obtain ⟨haD,haz⟩ := mem_filter.mp ha
      obtain ⟨hbD,hbz⟩ := mem_filter.mp hb
      obtain ⟨haA,hay⟩ := mem_filter.mp haD
      obtain ⟨hbA,hby⟩ := mem_filter.mp hbD
      exact hsq y hy z hzB hzy.symm a haA b hbA hay haz hby hbz
    have he : A.filter (fun x => r x z) =
        C.filter (fun x => r x z) ∪ D.filter (fun x => r x z) := by
      ext x
      simp only [C, mem_filter, mem_sdiff, mem_union]
      by_cases hx : x ∈ D
      · have hxA := hDA hx
        simp_all
      · simp_all
    have hh := card_union_le (C.filter fun x => r x z) (D.filter fun x => r x z)
    rw [← he, hfour z hzB] at hh
    omega
  have hupper : ∀ x ∈ C, ((B.erase y).filter (r x)).card ≤ 3 := by
    intro x hx
    exact (card_le_card (filter_subset_filter _ (erase_subset _ _))).trans
      (hthree x (mem_sdiff.mp hx).1)
  have hl : 3 * (B.erase y).card ≤ ∑ z ∈ B.erase y, (C.filter fun x => r x z).card := by
    calc
      _ = ∑ _z ∈ B.erase y, 3 := by simp [mul_comm]
      _ ≤ _ := sum_le_sum hlow
  have hu : (∑ x ∈ C, ((B.erase y).filter (r x)).card) ≤ 3 * C.card := by
    calc
      _ ≤ ∑ _x ∈ C, 3 := sum_le_sum hupper
      _ = _ := by simp [mul_comm]
  have he := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (s := C) (t := B.erase y) r
  change (∑ x ∈ C, ((B.erase y).filter (r x)).card) =
    ∑ z ∈ B.erase y, (C.filter fun x => r x z).card at he
  have hB := card_erase_add_one hy
  omega


open BipartiteBalance

variable {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A bipartite graph with two exceptional right vertices, left degree at most
three outside them, and no four-cycle outside them has no forbidden pair. -/
theorem not_hasPair (c : V → Bool) (K : Finset V)
    (hbi : ∀ a b, G.Adj a b → c a ≠ c b)
    (hcap : K.card ≤ 2)
    (hthree : ∀ x, c x = true → (univ.filter fun y => G.Adj x y ∧ y ∉ K).card ≤ 3)
    (hsq : ∀ a, a ∉ K → ∀ b, b ∉ K → a ≠ b →
      ∀ x y, c x = true → c y = true →
        G.Adj x a → G.Adj x b → G.Adj y a → G.Adj y b → x = y) :
    ¬ HasPairF G := by
  classical
  rintro ⟨u,v,p,q,hp,hq,hS,hE⟩
  let S := p.support.toFinset
  let A := S.filter fun x => c x = true
  let R := S.filter fun x => c x = false
  let B := R \ K
  let U := p.edges.toFinset ∪ q.edges.toFinset
  have hind : ∀ a b, G.Adj a b → c a = true ∨ c b = true := by
    intro a b ha
    have hh := hbi a b ha
    cases ca : c a <;> cases cb : c b <;> simp_all
  have hweight : (∑ x ∈ S, (if c x then (1 : ℤ) else -1)) =
      (A.card : ℤ) - (R.card : ℤ) := by
    simp [A, R, sum_ite, ← Bool.not_eq_true, sub_eq_add_neg]
  have hempty : p.edges.toFinset.filter (sameTrue c) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro e he
    obtain ⟨he,ht⟩ := mem_filter.mp he
    have ha := p.edges_subset_edgeSet (List.mem_toFinset.mp he)
    induction e using Sym2.inductionOn with | _ a b => ?_
    have hab := hbi a b (G.mem_edgeSet.mp ha)
    exact hab ((ht a (by simp)).trans (ht b (by simp)).symm)
  have hw := walk_true_weight c hind p
  rw [hempty, card_empty, cycle_weight_sum _ hp] at hw
  change 2 * (0 : ℤ) = 2 * (∑ x ∈ S, _) at hw
  rw [hweight] at hw
  have hbal : A.card = R.card := by omega
  have hpart : A ∪ R = S := by ext x; cases hx : c x <;> simp [A,R,hx]
  have hbig : 5 ≤ S.card := five_le_card_support hp hq hS hE
  have hcardS : S.card ≤ A.card + R.card := by rw [← hpart]; exact card_union_le _ _
  have hB : B.Nonempty := by
    by_contra hn
    have he : B = ∅ := not_nonempty_iff_eq_empty.mp hn
    have hsub : R ⊆ K := sdiff_eq_empty_iff_subset.mp he
    have hh := (card_le_card hsub).trans hcap
    omega
  have hdegree : ∀ x ∈ S, (S.filter fun w => s(x,w) ∈ U).card = 4 := by
    intro x hx
    exact card_neighbors_of_pair hp hq hS hE (List.mem_toFinset.mp hx)
  have hadj : ∀ x y, s(x,y) ∈ U → G.Adj x y := by
    intro x y he
    exact (mem_support_and_adj_of_mem_union_edges hS he).2
  have hfour : ∀ y ∈ B, (A.filter fun x => s(x,y) ∈ U).card = 4 := by
    intro y hy
    have hyR := (mem_sdiff.mp hy).1
    obtain ⟨hyS,hyc⟩ := mem_filter.mp hyR
    have he : A.filter (fun x => s(x,y) ∈ U) = S.filter (fun x => s(y,x) ∈ U) := by
      ext x
      simp only [A, mem_filter]
      constructor
      · rintro ⟨⟨hx,hc⟩,hu⟩
        exact ⟨hx, Sym2.eq_swap ▸ hu⟩
      · rintro ⟨hx,hu⟩
        have hc : c x = true := by
          have hh := hbi y x (hadj y x hu)
          cases he : c x <;> simp_all
        exact ⟨⟨hx,hc⟩, Sym2.eq_swap ▸ hu⟩
    rw [he]
    exact hdegree y hyS
  have hlow : ∀ x ∈ A, (B.filter fun y => s(x,y) ∈ U).card ≤ 3 := by
    intro x hx
    apply (card_le_card ?_).trans (hthree x (mem_filter.mp hx).2)
    intro y hy
    obtain ⟨hyB,hu⟩ := mem_filter.mp hy
    exact mem_filter.mpr ⟨mem_univ _, hadj x y hu, (mem_sdiff.mp hyB).2⟩
  have hgap := incidence_gap (fun x y => s(x,y) ∈ U) A B hB hfour hlow (by
    intro a ha b hb hab x hx y hy hxa hxb hya hyb
    exact hsq a (mem_sdiff.mp ha).2 b (mem_sdiff.mp hb).2 hab x y (mem_filter.mp hx).2 (mem_filter.mp hy).2
      (hadj x a hxa) (hadj x b hxb) (hadj y a hya) (hadj y b hyb))
  have hR : R.card ≤ B.card + K.card := by
    have he : R ⊆ B ∪ K := by
      intro x hx
      by_cases hk : x ∈ K
      · exact mem_union_right _ hk
      · exact mem_union_left _ (mem_sdiff.mpr ⟨hx,hk⟩)
    exact (card_le_card he).trans (card_union_le _ _)
  omega

end Erdos585.IncidenceHubs

