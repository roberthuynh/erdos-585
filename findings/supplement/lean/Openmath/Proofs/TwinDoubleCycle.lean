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
import Openmath.Proofs.HaarCompositeEven
import Openmath.Proofs.TwinComponentCount
import Mathlib.Order.Preorder.Finite

/-! # Actual cycles from a selected two-clone incidence graph -/

namespace Erdos585.TwinDoubleCycle

open SimpleGraph

variable {I R : Type*}

/-- Replace each left incidence vertex by two actual vertices with the same neighbors. -/
def twinGraph (J : Finset (I × R)) : SimpleGraph ((I × Bool) ⊕ R) where
  Adj x y := match x, y with
    | .inl (i, _), .inr r => (i, r) ∈ J
    | .inr r, .inl (i, _) => (i, r) ∈ J
    | _, _ => False
  symm := ⟨by rintro (⟨i, b⟩ | r) (⟨j, c⟩ | s) <;> simp_all⟩
  loopless := ⟨by rintro (⟨i, b⟩ | r) <;> simp⟩

@[simp] lemma twinGraph_adj_left_right (J : Finset (I × R)) (i : I) (b : Bool) (r : R) :
    (twinGraph J).Adj (.inl (i, b)) (.inr r) ↔ (i, r) ∈ J := Iff.rfl

@[simp] lemma twinGraph_adj_right_left (J : Finset (I × R)) (i : I) (b : Bool) (r : R) :
    (twinGraph J).Adj (.inr r) (.inl (i, b)) ↔ (i, r) ∈ J := Iff.rfl

@[simp] lemma twinGraph_not_adj_left (J : Finset (I × R)) (x y : I × Bool) :
    ¬ (twinGraph J).Adj (.inl x) (.inl y) := by cases x; cases y; exact id

@[simp] lemma twinGraph_not_adj_right (J : Finset (I × R)) (x y : R) :
    ¬ (twinGraph J).Adj (.inr x) (.inr y) := id

theorem twinGraph_mono {J K : Finset (I × R)} (h : J ⊆ K) : twinGraph J ≤ twinGraph K := by
  rintro (⟨i, b⟩ | r) (⟨j, c⟩ | s) <;> simp_all [twinGraph]
  all_goals exact fun hmem => h hmem

/-- The involution swapping the two clones and fixing the right shore. -/
def swap : ((I × Bool) ⊕ R) ≃ ((I × Bool) ⊕ R) where
  toFun := fun x => match x with
    | .inl (i, b) => .inl (i, !b)
    | .inr r => .inr r
  invFun := fun x => match x with
    | .inl (i, b) => .inl (i, !b)
    | .inr r => .inr r
  left_inv := by rintro (⟨i, b⟩ | r) <;> simp
  right_inv := by rintro (⟨i, b⟩ | r) <;> simp

@[simp] lemma swap_left (i : I) (b : Bool) : swap (.inl (i, b) : (I × Bool) ⊕ R) = .inl (i, !b) := rfl
@[simp] lemma swap_right (r : R) : swap (.inr r : (I × Bool) ⊕ R) = .inr r := rfl
@[simp] lemma swap_swap (v : (I × Bool) ⊕ R) : swap (swap v) = v := by
  cases v with
  | inl x => rcases x with ⟨i, b⟩; simp
  | inr r => simp

section Exchange

variable {V : Type*} [Finite V]

private def switched (F : SimpleGraph V) (u a v b : V) : SimpleGraph V :=
  (F \ (edge u a ⊔ edge v b)) ⊔ (edge u b ⊔ edge v a)

/-- The two-cut switch merges the cut components without losing any old reachability. -/
private lemma switched_reachable (F : SimpleGraph V) (hF : F.IsCycles)
    {u a v b : V} (hua : F.Adj u a) (hvb : F.Adj v b)
    (huv : ¬ F.Reachable u v) :
    (∀ x y, F.Reachable x y → (switched F u a v b).Reachable x y) ∧
      (switched F u a v b).Reachable u v := by
  classical
  let D := edge u a ⊔ edge v b
  let A := edge u b ⊔ edge v a
  let H := (F \ D) ⊔ A
  have hub : ¬ F.Reachable u b := fun h => huv (h.trans hvb.symm.reachable)
  have hva : ¬ F.Reachable v a := fun h => huv (hua.reachable.trans h.symm)
  have hdelete : ∀ {x y : V}, F.Adj x y → (F \ edge x y).Reachable x y := by
    intro x y hxy
    have heq : fromEdgeSet {s(x, y)} = edge x y := by
      ext z w
      simp only [fromEdgeSet_adj, Set.mem_singleton_iff, edge_adj]
      simp only [Sym2.eq_iff]
    simpa only [deleteEdges, heq] using hF.reachable_deleteEdges hxy
  have hua' : (F \ D).Reachable u a := by
    have h := HaarCompositeEven.reachable_avoid_edge (sdiff_le : F \ edge u a ≤ F)
      hvb hub (hdelete hua)
    have heq : (F \ edge u a) \ edge v b = F \ D := by
      ext x y
      simp only [D, sdiff_adj, sup_adj]
      tauto
    simpa only [heq] using h
  have hvb' : (F \ D).Reachable v b := by
    have h := HaarCompositeEven.reachable_avoid_edge (sdiff_le : F \ edge v b ≤ F)
      hua hva (hdelete hvb)
    have heq : (F \ edge v b) \ edge u a = F \ D := by
      ext x y
      simp only [D, sdiff_adj, sup_adj]
      tauto
    simpa only [heq] using h
  have huaH : H.Reachable u a := hua'.mono le_sup_left
  have hvbH : H.Reachable v b := hvb'.mono le_sup_left
  have hubH : H.Adj u b := by
    apply Or.inr
    apply Or.inl
    simp only [edge_adj]
    exact ⟨Or.inl ⟨trivial, trivial⟩, fun he => hub (he ▸ Reachable.refl u)⟩
  have huvH : H.Reachable u v := hubH.reachable.trans hvbH.symm
  have hreplace : ∀ x y, F.Adj x y → H.Reachable x y := by
    intro x y hxy
    by_cases hd : D.Adj x y
    · simp only [D, sup_adj, edge_adj] at hd
      rcases hd with ⟨(⟨rfl, rfl⟩ | ⟨rfl, rfl⟩), _⟩ |
        ⟨(⟨rfl, rfl⟩ | ⟨rfl, rfl⟩), _⟩
      · exact huaH
      · exact huaH.symm
      · exact hvbH
      · exact hvbH.symm
    · exact (show H.Adj x y from Or.inl ⟨hxy, hd⟩).reachable
  exact ⟨fun x y h => HaarCompositeEven.reachable_transfer h (fun z w _ hzw => hreplace z w hzw), huvH⟩

private lemma exchange_preserves_ncard (F D A : SimpleGraph V)
    (hD : D ≤ F) (hA : ∀ x y, A.Adj x y → ¬ F.Adj x y)
    (hp : ∀ x, (D.neighborSet x = ∅ ∧ A.neighborSet x = ∅) ∨
      ∃ y z, D.neighborSet x = {y} ∧ A.neighborSet x = {z}) (x : V) :
    (((F \ D) ⊔ A).neighborSet x).ncard = (F.neighborSet x).ncard := by
  classical
  rw [neighborSet_sup, neighborSet_sdiff]
  rcases hp x with ⟨hd, ha⟩ | ⟨y, z, hd, ha⟩
  · simp [hd, ha]
  · have hyD : D.Adj x y := by change y ∈ D.neighborSet x; rw [hd]; simp
    have hzA : A.Adj x z := by change z ∈ A.neighborSet x; rw [ha]; simp
    have hy : y ∈ F.neighborSet x := hD hyD
    have hz : z ∉ F.neighborSet x \ {y} := fun h => hA x z hzA h.1
    rw [hd, ha, Set.union_singleton, Set.ncard_insert_of_notMem hz,
      Set.ncard_sdiff_singleton_of_mem hy]
    exact Nat.sub_add_cancel ((Set.ncard_pos (Set.toFinite _)).mpr ⟨y, hy⟩)

private lemma switched_ncard (F : SimpleGraph V)
    {u a v b : V} (hua : F.Adj u a) (hvb : F.Adj v b)
    (huv : ¬ F.Reachable u v) (x : V) :
    ((switched F u a v b).neighborSet x).ncard = (F.neighborSet x).ncard := by
  have huaN := hua.ne
  have hvbN := hvb.ne
  have huvN : u ≠ v := fun h => huv (h ▸ Reachable.refl u)
  have hubN : u ≠ b := fun h => huv (h ▸ hvb.symm.reachable)
  have havN : a ≠ v := fun h => huv (h ▸ hua.reachable)
  have habN : a ≠ b := fun h => huv (hua.reachable.trans (h ▸ hvb.symm.reachable))
  apply exchange_preserves_ncard
  · intro z w h
    simp only [sup_adj, edge_adj] at h
    rcases h with ⟨(⟨rfl, rfl⟩ | ⟨rfl, rfl⟩), _⟩ |
      ⟨(⟨rfl, rfl⟩ | ⟨rfl, rfl⟩), _⟩
    · exact hua
    · exact hua.symm
    · exact hvb
    · exact hvb.symm
  · intro z w h hzw
    simp only [sup_adj, edge_adj] at h
    rcases h with ⟨(⟨rfl, rfl⟩ | ⟨rfl, rfl⟩), _⟩ |
      ⟨(⟨rfl, rfl⟩ | ⟨rfl, rfl⟩), _⟩
    · exact huv (hzw.reachable.trans hvb.symm.reachable)
    · exact huv (hzw.symm.reachable.trans hvb.symm.reachable)
    · exact huv (hua.reachable.trans hzw.symm.reachable)
    · exact huv (hua.reachable.trans hzw.reachable)
  · intro z
    by_cases hzu : z = u
    · subst z
      right; refine ⟨a, b, ?_, ?_⟩ <;> ext w <;>
        simp_all [mem_neighborSet, edge_adj]
    by_cases hza : z = a
    · subst z
      right; refine ⟨u, v, ?_, ?_⟩ <;> ext w <;>
        simp_all [mem_neighborSet, edge_adj]
    by_cases hzv : z = v
    · subst z
      right; refine ⟨b, a, ?_, ?_⟩ <;> ext w <;>
        simp_all [mem_neighborSet, edge_adj]
    by_cases hzb : z = b
    · subst z
      right; refine ⟨v, u, ?_, ?_⟩ <;> ext w <;>
        simp_all [mem_neighborSet, edge_adj]
    left; constructor <;> ext w <;>
      simp_all [mem_neighborSet, edge_adj]

end Exchange

section Assignment

variable [Fintype I] [Fintype R] [DecidableEq I] [DecidableEq R]

private def leftFiber (J : Finset (I × R)) (i : I) : Finset R :=
  Finset.univ.filter fun r => (i, r) ∈ J

private def rightFiber (J : Finset (I × R)) (r : R) : Finset I :=
  Finset.univ.filter fun i => (i, r) ∈ J

private def assignmentGraph (J : Finset (I × R)) (c : I → R → Bool) :
    SimpleGraph ((I × Bool) ⊕ R) where
  Adj x y := match x, y with
    | .inl (i, b), .inr r => (i, r) ∈ J ∧ c i r = b
    | .inr r, .inl (i, b) => (i, r) ∈ J ∧ c i r = b
    | _, _ => False
  symm := ⟨by rintro (⟨i, b⟩ | r) (⟨j, d⟩ | s) <;> simp_all⟩
  loopless := ⟨by rintro (⟨i, b⟩ | r) <;> simp⟩

omit [Fintype I] in
private lemma assignment_left_ncard (J : Finset (I × R)) (c : I → R → Bool)
    (i : I) (b : Bool) :
    ((assignmentGraph J c).neighborSet (.inl (i, b))).ncard =
      (Finset.univ.filter fun r => (i, r) ∈ J ∧ c i r = b).card := by
  classical
  have heq : (assignmentGraph J c).neighborSet (.inl (i, b)) =
      Sum.inr '' (↑(Finset.univ.filter fun r => (i, r) ∈ J ∧ c i r = b) : Set R) := by
    ext x
    rcases x with ⟨j, d⟩ | r <;>
      simp [assignmentGraph, mem_neighborSet]
  rw [heq, Set.ncard_image_of_injective _ Sum.inr_injective, Set.ncard_coe_finset]

omit [Fintype R] in
private lemma assignment_right_ncard (J : Finset (I × R)) (c : I → R → Bool)
    (r : R) :
    ((assignmentGraph J c).neighborSet (.inr r)).ncard = (rightFiber J r).card := by
  classical
  let f : I → (I × Bool) ⊕ R := fun i => .inl (i, c i r)
  have hf : Function.Injective f := by
    intro i j h
    exact congrArg Prod.fst (Sum.inl.inj h)
  have heq : (assignmentGraph J c).neighborSet (.inr r) =
      f '' (↑(rightFiber J r) : Set I) := by
    ext x
    rcases x with ⟨j, d⟩ | s <;>
      simp [assignmentGraph, mem_neighborSet, f, rightFiber]
  rw [heq, Set.ncard_image_of_injective _ hf, Set.ncard_coe_finset]

/-- An actual split of every incidence, with two neighbors at each active clone. -/
private structure Selected (J : Finset (I × R)) (F : SimpleGraph ((I × Bool) ⊕ R)) : Prop where
  le_host : F ≤ twinGraph J
  cycles : F.IsCycles
  cover : ∀ i r, (i, r) ∈ J ↔
    F.Adj (.inl (i, false)) (.inr r) ∨ F.Adj (.inl (i, true)) (.inr r)
  separate : ∀ i r, ¬ (F.Adj (.inl (i, false)) (.inr r) ∧
    F.Adj (.inl (i, true)) (.inr r))
  active : ∀ i b, (∃ r, (i, r) ∈ J) → (F.neighborSet (.inl (i, b))).Nonempty

private lemma exists_selected (J : Finset (I × R))
    (hl : ∀ i, (leftFiber J i).card = 0 ∨ (leftFiber J i).card = 4)
    (hr : ∀ r, (rightFiber J r).card = 0 ∨ (rightFiber J r).card = 2) :
    ∃ F, Selected J F := by
  classical
  have hpick : ∀ i, ∃ A : Finset R, A ⊆ leftFiber J i ∧
      ((leftFiber J i).Nonempty → A.card = 2 ∧ (leftFiber J i \ A).card = 2) := by
    intro i
    rcases hl i with hzero | hfour
    · refine ⟨∅, Finset.empty_subset _, ?_⟩
      intro hn
      have := Finset.card_pos.mpr hn
      omega
    · obtain ⟨A, hA, hcard⟩ := Finset.exists_subset_card_eq
        (show 2 ≤ (leftFiber J i).card by omega)
      exact ⟨A, hA, fun _ => ⟨hcard, by rw [Finset.card_sdiff_of_subset hA, hfour, hcard]⟩⟩
  choose A hA hAc using hpick
  let c : I → R → Bool := fun i r => if r ∈ A i then false else true
  let F := assignmentGraph J c
  have hleft : ∀ i b, (∃ r, (i, r) ∈ J) → (F.neighborSet (.inl (i, b))).ncard = 2 := by
    intro i b hi
    have hi' : (leftFiber J i).Nonempty := by
      obtain ⟨r, hr⟩ := hi
      exact ⟨r, by simp [leftFiber, hr]⟩
    obtain ⟨hcardA, hcardB⟩ := hAc i hi'
    rw [assignment_left_ncard]
    cases b
    · have heq : (Finset.univ.filter fun r => (i, r) ∈ J ∧ c i r = false) = A i := by
        ext r
        have hm : r ∈ A i → (i, r) ∈ J := by
          intro h
          have := hA i h
          simpa [leftFiber] using this
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, c, ite_eq_left_iff]
        aesop
      rw [heq, hcardA]
    · have heq : (Finset.univ.filter fun r => (i, r) ∈ J ∧ c i r = true) = leftFiber J i \ A i := by
        ext r
        simp [c, leftFiber]
      rw [heq, hcardB]
  refine ⟨F, ?_⟩
  constructor
  · rintro (⟨i, b⟩ | r) (⟨j, d⟩ | s) <;>
      simp_all [F, assignmentGraph, twinGraph]
  · rintro (⟨i, b⟩ | r) hn
    · obtain ⟨w, hw⟩ := hn
      rcases w with ⟨j, d⟩ | s
      · exact False.elim hw
      · exact hleft i b ⟨s, hw.1⟩
    · rw [assignment_right_ncard]
      rcases hr r with hzero | htwo
      · have hncard := (Set.ncard_pos (Set.toFinite _)).mpr hn
        rw [assignment_right_ncard, hzero] at hncard
        omega
      · exact htwo
  · intro i r
    change (i, r) ∈ J ↔ ((i, r) ∈ J ∧ c i r = false) ∨ ((i, r) ∈ J ∧ c i r = true)
    cases hc : c i r <;> simp
  · intro i r
    change ¬ (((i, r) ∈ J ∧ c i r = false) ∧ ((i, r) ∈ J ∧ c i r = true))
    simp +contextual
  · intro i b hi
    apply Set.nonempty_of_ncard_ne_zero
    rw [hleft i b hi]
    decide

private lemma selected_switch (J : Finset (I × R))
    (F : SimpleGraph ((I × Bool) ⊕ R)) (hF : Selected J F)
    {i : I} {a b : R}
    (hua : F.Adj (.inl (i, false)) (.inr a))
    (hvb : F.Adj (.inl (i, true)) (.inr b))
    (huv : ¬ F.Reachable (.inl (i, false)) (.inl (i, true))) :
    Selected J (switched F (.inl (i, false)) (.inr a) (.inl (i, true)) (.inr b)) := by
  classical
  let H := switched F (.inl (i, false)) (.inr a) (.inl (i, true)) (.inr b)
  have hab : a ≠ b := by
    intro he
    subst b
    exact huv (hua.reachable.trans hvb.symm.reachable)
  have hia : (i, a) ∈ J := hF.le_host hua
  have hib : (i, b) ∈ J := hF.le_host hvb
  have hna : ¬ F.Adj (.inl (i, true)) (.inr a) := fun h => hF.separate i a ⟨hua, h⟩
  have hnb : ¬ F.Adj (.inl (i, false)) (.inr b) := fun h => hF.separate i b ⟨h, hvb⟩
  have hcard := switched_ncard F hua hvb huv
  constructor
  · intro x y hxy
    change (F.Adj x y ∧ ¬ (edge (.inl (i, false)) (.inr a) ⊔
      edge (.inl (i, true)) (.inr b)).Adj x y) ∨
      (edge (.inl (i, false)) (.inr b) ⊔ edge (.inl (i, true)) (.inr a)).Adj x y at hxy
    rcases hxy with hxy | hxy
    · exact hF.le_host hxy.1
    · simp only [sup_adj, edge_adj] at hxy
      rcases hxy with ⟨(⟨rfl, rfl⟩ | ⟨rfl, rfl⟩), _⟩ |
        ⟨(⟨rfl, rfl⟩ | ⟨rfl, rfl⟩), _⟩
      · exact hib
      · exact hib
      · exact hia
      · exact hia
  · intro x hn
    rw [hcard]
    apply hF.cycles
    apply Set.nonempty_of_ncard_ne_zero
    rw [← hcard]
    exact ((Set.ncard_pos (Set.toFinite _)).mpr hn).ne'
  · intro j r
    by_cases hji : j = i
    · subst j
      by_cases hra : r = a
      · subst r
        simp [switched, edge_adj, hia, hua, hna, hab]
      by_cases hrb : r = b
      · subst r
        simp [switched, edge_adj, hib, hvb, hnb, Ne.symm hab]
      simpa [switched, edge_adj, hra, hrb] using hF.cover i r
    · simpa [switched, edge_adj, hji] using hF.cover j r
  · intro j r
    by_cases hji : j = i
    · subst j
      by_cases hra : r = a
      · subst r
        simp [switched, edge_adj, hua, hna, hab]
      by_cases hrb : r = b
      · subst r
        simp [switched, edge_adj, hvb, hnb, Ne.symm hab]
      simpa [switched, edge_adj, hra, hrb] using hF.separate i r
    · simpa [switched, edge_adj, hji] using hF.separate j r
  · intro j d hj
    apply Set.nonempty_of_ncard_ne_zero
    rw [hcard, hF.cycles (hF.active j d hj)]
    decide

private lemma exists_selected_joined (J : Finset (I × R))
    (hl : ∀ i, (leftFiber J i).card = 0 ∨ (leftFiber J i).card = 4)
    (hr : ∀ r, (rightFiber J r).card = 0 ∨ (rightFiber J r).card = 2) :
    ∃ F, Selected J F ∧ ∀ i, (∃ r, (i, r) ∈ J) →
      F.Reachable (.inl (i, false)) (.inl (i, true)) := by
  classical
  let : Fintype (SimpleGraph ((I × Bool) ⊕ R)) := Fintype.ofFinite _
  let S : Finset (SimpleGraph ((I × Bool) ⊕ R)) := Finset.univ.filter (Selected J)
  obtain ⟨F₀, hF₀⟩ := exists_selected J hl hr
  have hs : S.Nonempty := ⟨F₀, by simp [S, hF₀]⟩
  obtain ⟨F, hFS, hmin⟩ := Finset.exists_min_image S
    (fun G => Nat.card G.ConnectedComponent) hs
  have hF : Selected J F := (Finset.mem_filter.mp hFS).2
  refine ⟨F, hF, ?_⟩
  intro i hi
  by_contra hn
  obtain ⟨a, ha⟩ := hF.active i false hi
  obtain ⟨b, hb⟩ := hF.active i true hi
  rcases a with ⟨j, d⟩ | a
  · exact twinGraph_not_adj_left J _ _ (hF.le_host ha)
  rcases b with ⟨j, d⟩ | b
  · exact twinGraph_not_adj_left J _ _ (hF.le_host hb)
  let H := switched F (.inl (i, false)) (.inr a) (.inl (i, true)) (.inr b)
  have hH : Selected J H := selected_switch J F hF ha hb hn
  have hHS : H ∈ S := by simp [S, hH]
  have hle := hmin H hHS
  obtain ⟨hpres, hnew⟩ := switched_reachable F hF.cycles ha hb hn
  have hlt := TwinComponentCount.card_lt_of_reachable_merge F H hpres hn hnew
  omega

omit [Fintype I] [Fintype R] [DecidableEq I] [DecidableEq R] in
private lemma selected_disjoint_swap (J : Finset (I × R))
    (F : SimpleGraph ((I × Bool) ⊕ R)) (hF : Selected J F) :
    ∀ x y, F.Adj x y → ¬ F.Adj (swap x) (swap y) := by
  rintro (⟨i, b⟩ | r) (⟨j, d⟩ | s) h h'
  · exact twinGraph_not_adj_left J _ _ (hF.le_host h)
  · cases b
    · exact hF.separate i s ⟨h, h'⟩
    · exact hF.separate i s ⟨h', h⟩
  · cases d
    · exact hF.separate j r ⟨h.symm, h'.symm⟩
    · exact hF.separate j r ⟨h'.symm, h.symm⟩
  · exact twinGraph_not_adj_right J _ _ (hF.le_host h)

/-- A nonempty actual incidence set with left degrees zero or four and right degrees
zero or two forces two edge-disjoint simple cycles on exactly the same vertex set
after every left vertex is replaced by two twins. -/
theorem hasPair_of_selected_incidence (J : Finset (I × R)) (hJ : J.Nonempty)
    (hleft : ∀ i, (Finset.univ.filter (fun r => (i, r) ∈ J)).card = 0 ∨
      (Finset.univ.filter (fun r => (i, r) ∈ J)).card = 4)
    (hright : ∀ r, (Finset.univ.filter (fun i => (i, r) ∈ J)).card = 0 ∨
      (Finset.univ.filter (fun i => (i, r) ∈ J)).card = 2) :
    HasTwoEdgeDisjointCyclesSameVertexSet (twinGraph J) := by
  classical
  obtain ⟨F, hF, hjoin⟩ := exists_selected_joined J hleft hright
  obtain ⟨⟨i, r⟩, hir⟩ := hJ
  let x : (I × Bool) ⊕ R := .inl (i, false)
  obtain ⟨p, hp, hverts⟩ :=
    hF.cycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
      (c := F.connectedComponentMk x) rfl (hF.active i false ⟨r, hir⟩)
  let g : F →g twinGraph J := {
    toFun := swap
    map_rel' := by
      rintro (⟨j, b⟩ | s) (⟨k, d⟩ | t) h
      · exact False.elim (twinGraph_not_adj_left J _ _ (hF.le_host h))
      · change (j, t) ∈ J
        exact hF.le_host h
      · change (k, s) ∈ J
        exact hF.le_host h
      · exact False.elim (twinGraph_not_adj_right J _ _ (hF.le_host h)) }
  have hclosed : ∀ v, v ∈ p.support → swap v ∈ p.support := by
    intro v hv
    have hvs : v ∈ (F.connectedComponentMk x).supp := by
      rw [← hverts, Walk.mem_verts_toSubgraph]
      exact hv
    have hreach : F.Reachable v (swap v) := by
      rcases v with ⟨j, b⟩ | s
      · obtain ⟨w, _, hw⟩ := adj_of_mem_walk_support p hp.not_nil hv
        have hj : ∃ t, (j, t) ∈ J := by
          rcases w with ⟨k, d⟩ | t
          · exact False.elim (twinGraph_not_adj_left J _ _ (hF.le_host hw))
          · exact ⟨t, hF.le_host hw⟩
        cases b
        · exact hjoin j hj
        · exact (hjoin j hj).symm
      · exact Reachable.refl _
    rw [← Walk.mem_verts_toSubgraph, hverts]
    exact (ConnectedComponent.sound hreach.symm).trans hvs
  refine ⟨x, swap x, p.mapLe hF.le_host, p.map g, hp.mapLe hF.le_host,
    hp.map swap.injective, ?_, ?_⟩
  · ext v
    change v ∈ (p.mapLe hF.le_host).support ↔ v ∈ (p.map g).support
    rw [Walk.support_mapLe_eq_support, Walk.support_map]
    simp only [List.mem_map]
    constructor
    · intro hv
      exact ⟨swap v, hclosed v hv, swap_swap v⟩
    · rintro ⟨w, hw, rfl⟩
      exact hclosed w hw
  · rw [Walk.edges_mapLe_eq_edges, Walk.edges_map]
    intro e he hf
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hf
    have hde := p.edges_subset_edgeSet hd
    have hee := p.edges_subset_edgeSet he
    induction d using Sym2.inductionOn with
    | _ a b =>
      exact selected_disjoint_swap J F hF a b hde hee

end Assignment

end Erdos585.TwinDoubleCycle
