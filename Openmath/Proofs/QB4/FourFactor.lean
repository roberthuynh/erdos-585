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
import Mathlib.Combinatorics.Hall.Finite
import Openmath.Proofs.QB4.Core

/-!
# QB(4): the bipartite 4-factor criterion

This file proves the bipartite 4-factor criterion used for `Erdos585.qb4`, in the direction the
proof needs (it is the case of the bipartite f-factor criterion with every value 4): if a balanced
pair `(P, Q)` satisfies the cut condition
`4 |A| ≤ e(A, Q - C) + 4 |C|` for all `A ⊆ P` and `C ⊆ Q`, then the bipartite graph `G[P, Q]` has
a spanning subgraph in which every degree is exactly four (`exists_four_factor`).

The route is Hall's theorem (`Finset.all_card_le_biUnion_card_iff_existsInjective'`) applied to
Tutte's gadget. Write `deg_S v` for `dg G S v`, the number of neighbors of `v` in `S`. The index
set of the gadget is the set `E` of adjacent pairs of `P × Q` together
with `deg_P q - 4` slots for each `q ∈ Q`. An adjacent pair `e = (p, q)` is matched either to
itself (`e` is kept) or to one of the `deg_Q p - 4` slots of `p` (`e` is deleted). A slot of `q`
is matched to an adjacent pair at `q`, which is then deleted. Hall's condition reduces to the cut
condition, and a matching leaves every `p ∈ P` with at least four kept pairs and every `q ∈ Q` with
at most four, so a double count makes all of them exactly four.

The bridge to `sparse_core` is `hviol_of_not_quartic`: if `(U, W)` with `|W| = |U| + 1` has no
quartic subgraph, the cut condition fails for `(W - y, U)` at every `y ∈ W`, which is the
hypothesis `hviol` of `sparse_core`. `quartic_of_sparse` combines the two.
-/

open Finset Sum

namespace Erdos585.QB4

/-! ### Hall's theorem for a family indexed by a finset -/

/-- Hall's theorem for a family `t` indexed by the elements of a finset `L`: the matching is a
function that is injective on `L` and picks `g i ∈ t i` for every `i ∈ L`. -/
lemma exists_injOn_of_hall {ι α : Type*} [DecidableEq α] [Nonempty α] (L : Finset ι)
    (t : ι → Finset α) (h : ∀ S ⊆ L, #S ≤ #(S.biUnion t)) :
    ∃ g : ι → α, (∀ i ∈ L, ∀ j ∈ L, g i = g j → i = j) ∧ ∀ i ∈ L, g i ∈ t i := by
  classical
  obtain ⟨f, hf, hft⟩ := (all_card_le_biUnion_card_iff_existsInjective' fun i : L => t i).1
    fun s => by
      have hs := h (s.image Subtype.val) fun x hx => by
        obtain ⟨y, -, rfl⟩ := mem_image.1 hx
        exact y.2
      rwa [card_image_of_injective s Subtype.coe_injective, image_biUnion] at hs
  refine ⟨fun i => if hi : i ∈ L then f ⟨i, hi⟩ else Classical.arbitrary α, ?_, ?_⟩
  · intro i hi j hj hij
    simp only [dif_pos hi, dif_pos hj] at hij
    exact congrArg Subtype.val (hf hij)
  · intro i hi
    simp only [dif_pos hi]
    exact hft ⟨i, hi⟩

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ### Adjacent pairs and slots -/

variable (G) in
/-- The adjacent pairs of `A × B`. -/
def adjPairs (A B : Finset V) : Finset (V × V) := (A ×ˢ B).filter fun x => G.Adj x.1 x.2

/-- `d v` slots `(v, 0), …, (v, d v - 1)` for each vertex `v ∈ S`. -/
def slots (S : Finset V) (d : V → ℕ) : Finset (V × ℕ) := S.biUnion fun v => {v} ×ˢ range (d v)

lemma mem_slots {S : Finset V} {d : V → ℕ} {x : V × ℕ} : x ∈ slots S d ↔ x.1 ∈ S ∧ x.2 < d x.1 := by
  obtain ⟨v, j⟩ := x
  simp only [slots, mem_biUnion, mem_product, mem_singleton, mem_range]
  constructor
  · rintro ⟨w, hw, rfl, hj⟩
    exact ⟨hw, hj⟩
  · rintro ⟨hv, hj⟩
    exact ⟨v, hv, rfl, hj⟩

lemma card_slots (S : Finset V) (d : V → ℕ) : #(slots S d) = ∑ v ∈ S, d v := by
  unfold slots
  rw [card_biUnion]
  · simp
  · intro v _ w _ hvw
    exact disjoint_product.2 (Or.inl (disjoint_singleton.2 hvw))

omit [DecidableEq V] in
/-- The adjacent pairs of `A × B` number `e(A, B)`. -/
lemma card_adjPairs (A B : Finset V) : #(adjPairs G A B) = ec G A B := by
  unfold adjPairs ec dg
  rw [card_filter, sum_product]
  refine sum_congr rfl fun a _ => ?_
  rw [card_filter]

lemma adjPairs_filter_snd_mem {P Q C : Finset V} (hC : C ⊆ Q) :
    (adjPairs G P Q).filter (fun e => e.2 ∈ C) = adjPairs G P C := by
  ext ⟨a, b⟩
  simp only [adjPairs, mem_filter, mem_product]
  constructor
  · rintro ⟨⟨⟨ha, -⟩, hab⟩, hb⟩
    exact ⟨⟨ha, hb⟩, hab⟩
  · rintro ⟨⟨ha, hb⟩, hab⟩
    exact ⟨⟨⟨ha, hC hb⟩, hab⟩, hb⟩

/-- The adjacent pairs of `P × Q` at a vertex `p ∈ P` number `deg_Q p`. -/
lemma card_adjPairs_filter_fst {P Q : Finset V} {p : V} (hp : p ∈ P) :
    #((adjPairs G P Q).filter fun e => e.1 = p) = dg G Q p := by
  have h : (adjPairs G P Q).filter (fun e => e.1 = p) = adjPairs G {p} Q := by
    ext ⟨a, b⟩
    simp only [adjPairs, mem_filter, mem_product, mem_singleton]
    constructor
    · rintro ⟨⟨⟨-, hb⟩, hab⟩, rfl⟩
      exact ⟨⟨rfl, hb⟩, hab⟩
    · rintro ⟨⟨rfl, hb⟩, hab⟩
      exact ⟨⟨⟨hp, hb⟩, hab⟩, rfl⟩
  rw [h, card_adjPairs, ec, sum_singleton]

/-- The adjacent pairs of `P × Q` at a vertex `q ∈ Q` number `deg_P q`. -/
lemma card_adjPairs_filter_snd {P Q : Finset V} {q : V} (hq : q ∈ Q) :
    #((adjPairs G P Q).filter fun e => e.2 = q) = dg G P q := by
  have h : (adjPairs G P Q).filter (fun e => e.2 = q) = adjPairs G P {q} := by
    ext ⟨a, b⟩
    simp only [adjPairs, mem_filter, mem_product, mem_singleton]
    constructor
    · rintro ⟨⟨⟨ha, -⟩, hab⟩, rfl⟩
      exact ⟨⟨ha, rfl⟩, hab⟩
    · rintro ⟨⟨ha, rfl⟩, hab⟩
      exact ⟨⟨⟨ha, hq⟩, hab⟩, rfl⟩
  rw [h, card_adjPairs, ec_comm, ec, sum_singleton]

omit [DecidableEq V] in
/-- Truncated subtraction of four, summed over vertices of degree at least four. -/
lemma sum_sub_four_add {S : Finset V} {d : V → ℕ} (h : ∀ v ∈ S, 4 ≤ d v) :
    ∑ v ∈ S, (d v - 4) + 4 * #S = ∑ v ∈ S, d v := by
  rw [mul_comm, ← smul_eq_mul, ← sum_const, ← sum_add_distrib]
  exact sum_congr rfl fun v hv => Nat.sub_add_cancel (h v hv)

/-! ### Degrees from the cut condition -/

/-- The cut condition at `({p}, ∅)` gives `deg_Q p ≥ 4`. -/
lemma four_le_dg_left {P Q : Finset V}
    (hcut : ∀ A ⊆ P, ∀ C ⊆ Q, 4 * #A ≤ ec G A (Q \ C) + 4 * #C) {p : V} (hp : p ∈ P) :
    4 ≤ dg G Q p := by
  have h := hcut {p} (singleton_subset_iff.2 hp) ∅ (empty_subset _)
  rw [sdiff_empty, card_singleton, card_empty, ec, sum_singleton] at h
  omega

/-- The cut condition at `(P, Q - q)` gives `deg_P q ≥ 4` when `|P| = |Q|`. -/
lemma four_le_dg_right {P Q : Finset V} (hcard : #P = #Q)
    (hcut : ∀ A ⊆ P, ∀ C ⊆ Q, 4 * #A ≤ ec G A (Q \ C) + 4 * #C) {q : V} (hq : q ∈ Q) :
    4 ≤ dg G P q := by
  have h := hcut P Subset.rfl (Q.erase q) (erase_subset q Q)
  rw [sdiff_erase_self hq, card_erase_of_mem hq, ec_comm, ec, sum_singleton] at h
  have hQ := card_pos.2 ⟨q, hq⟩
  omega

/-! ### Tutte's gadget -/

variable (G) in
/-- The index set of the gadget for the pair `(P, Q)`: the adjacent pairs of `P × Q`, and
`deg_P q - 4` slots for each `q ∈ Q`. -/
def gadgetIndex (P Q : Finset V) : Finset ((V × V) ⊕ (V × ℕ)) :=
  (adjPairs G P Q).disjSum (slots Q fun q => dg G P q - 4)

variable (G) in
/-- Tutte's gadget for the pair `(P, Q)`. An adjacent pair `e` may be matched to itself or to a
slot of its first vertex `p`, of which there are `deg_Q p - 4`. A slot of `q` may be matched to an
adjacent pair whose second vertex is `q`. -/
def gadget (P Q : Finset V) : (V × V) ⊕ (V × ℕ) → Finset ((V × V) ⊕ (V × ℕ)) :=
  Sum.elim (fun e => ({e} : Finset (V × V)).disjSum (slots {e.1} fun p => dg G Q p - 4))
    (fun c => ((adjPairs G P Q).filter fun e => e.2 = c.1).disjSum ∅)

lemma inl_mem_gadgetIndex {P Q : Finset V} {e : V × V} :
    inl e ∈ gadgetIndex G P Q ↔ e ∈ adjPairs G P Q :=
  inl_mem_disjSum

lemma inr_mem_gadgetIndex {P Q : Finset V} {c : V × ℕ} :
    inr c ∈ gadgetIndex G P Q ↔ c.1 ∈ Q ∧ c.2 < dg G P c.1 - 4 := by
  rw [gadgetIndex, inr_mem_disjSum, mem_slots]

lemma inl_mem_gadget_inl {P Q : Finset V} {a e : V × V} :
    inl a ∈ gadget G P Q (inl e) ↔ a = e := by
  simp [gadget]

lemma inr_mem_gadget_inl {P Q : Finset V} {e : V × V} {s : V × ℕ} :
    inr s ∈ gadget G P Q (inl e) ↔ s.1 = e.1 ∧ s.2 < dg G Q s.1 - 4 := by
  rw [gadget, Sum.elim_inl, inr_mem_disjSum, mem_slots, mem_singleton]

lemma inl_mem_gadget_inr {P Q : Finset V} {a : V × V} {c : V × ℕ} :
    inl a ∈ gadget G P Q (inr c) ↔ a ∈ adjPairs G P Q ∧ a.2 = c.1 := by
  rw [gadget, Sum.elim_inr, inl_mem_disjSum, mem_filter]

lemma inr_notMem_gadget_inr {P Q : Finset V} {s c : V × ℕ} : inr s ∉ gadget G P Q (inr c) := by
  rw [gadget, Sum.elim_inr, inr_mem_disjSum]
  exact notMem_empty s

/-- **Hall's condition for the gadget** follows from the cut condition. For a set `S` of indices
with adjacent pairs `S_E` and slots `S_C`, put `A = fst S_E` and `C = fst S_C`. Then
`|S| ≤ |S_E| + Σ_{q ∈ C} (deg_P q - 4)`, while the neighborhood of `S` contains `S_E`, every
adjacent pair at `C`, and every slot of `A`. The overlap of `S_E` with the pairs at `C` is at most
`e(A, C)`, and the remaining inequality is the cut condition at `(A, C)`. -/
lemma gadget_hall {P Q : Finset V}
    (hcut : ∀ A ⊆ P, ∀ C ⊆ Q, 4 * #A ≤ ec G A (Q \ C) + 4 * #C)
    (hP4 : ∀ p ∈ P, 4 ≤ dg G Q p) (hQ4 : ∀ q ∈ Q, 4 ≤ dg G P q)
    (S : Finset ((V × V) ⊕ (V × ℕ))) (hS : S ⊆ gadgetIndex G P Q) :
    #S ≤ #(S.biUnion (gadget G P Q)) := by
  have hSE : S.toLeft ⊆ adjPairs G P Q := fun e he =>
    inl_mem_gadgetIndex.1 (hS (mem_toLeft.1 he))
  have hSC : ∀ c ∈ S.toRight, c.1 ∈ Q ∧ c.2 < dg G P c.1 - 4 := fun c hc =>
    inr_mem_gadgetIndex.1 (hS (mem_toRight.1 hc))
  have hAP : S.toLeft.image Prod.fst ⊆ P := by
    intro p hp
    obtain ⟨e, he, rfl⟩ := mem_image.1 hp
    exact (mem_product.1 (mem_filter.1 (hSE he)).1).1
  have hCQ : S.toRight.image Prod.fst ⊆ Q := by
    intro q hq
    obtain ⟨c, hc, rfl⟩ := mem_image.1 hq
    exact (hSC c hc).1
  set A := S.toLeft.image Prod.fst with hA
  set C := S.toRight.image Prod.fst with hC
  set EC := (adjPairs G P Q).filter fun e => e.2 ∈ C with hEC
  -- the slots in `S` lie over `C`
  have h2 : #S.toRight ≤ ∑ q ∈ C, (dg G P q - 4) := by
    rw [← card_slots]
    exact card_le_card fun c hc => mem_slots.2 ⟨mem_image_of_mem _ hc, (hSC c hc).2⟩
  -- the neighborhood of `S` in the gadget
  have h3 : #((S.toLeft ∪ EC).disjSum (slots A fun p => dg G Q p - 4)) ≤
      #(S.biUnion (gadget G P Q)) := by
    refine card_le_card fun x hx => mem_biUnion.2 ?_
    rcases x with e | s
    · rcases mem_union.1 (inl_mem_disjSum.1 hx) with he | he
      · exact ⟨inl e, mem_toLeft.1 he, inl_mem_gadget_inl.2 rfl⟩
      · obtain ⟨heE, heC⟩ := mem_filter.1 he
        obtain ⟨c, hc, hce⟩ := mem_image.1 heC
        exact ⟨inr c, mem_toRight.1 hc, inl_mem_gadget_inr.2 ⟨heE, hce.symm⟩⟩
    · obtain ⟨hsA, hs⟩ := mem_slots.1 (inr_mem_disjSum.1 hx)
      obtain ⟨e, he, hes⟩ := mem_image.1 hsA
      exact ⟨inl e, mem_toLeft.1 he, inr_mem_gadget_inl.2 ⟨hes.symm, hs⟩⟩
  rw [card_disjSum, card_slots] at h3
  have h1 := card_toLeft_add_card_toRight (u := S)
  have h4 := card_union_add_card_inter S.toLeft EC
  have h5 : #EC = ec G C P := by
    rw [hEC, adjPairs_filter_snd_mem hCQ, card_adjPairs, ec_comm]
  have h6 : #(S.toLeft ∩ EC) ≤ ec G A C := by
    rw [← card_adjPairs]
    refine card_le_card fun e he => ?_
    obtain ⟨heS, heC⟩ := mem_inter.1 he
    exact mem_filter.2 ⟨mem_product.2 ⟨mem_image_of_mem _ heS, (mem_filter.1 heC).2⟩,
      (mem_filter.1 (hSE heS)).2⟩
  have h7 : ∑ p ∈ A, (dg G Q p - 4) + 4 * #A = ec G A Q :=
    sum_sub_four_add fun p hp => hP4 p (hAP hp)
  have h8 : ∑ q ∈ C, (dg G P q - 4) + 4 * #C = ec G C P :=
    sum_sub_four_add fun q hq => hQ4 q (hCQ hq)
  have h9 := ec_sdiff_add_right (G := G) hCQ A
  have h10 := hcut A hAP C hCQ
  omega

/-! ### From a matching of the gadget to a 4-factor -/

/-- The kept pairs at `p ∈ P`. The deleted pairs at `p` are matched to distinct slots of `p`, so at
most `deg_Q p - 4` pairs at `p` are deleted and at least four are kept. -/
lemma four_le_card_kept {P Q : Finset V} (hP4 : ∀ p ∈ P, 4 ≤ dg G Q p)
    {g : (V × V) ⊕ (V × ℕ) → (V × V) ⊕ (V × ℕ)}
    (hginj : ∀ i ∈ gadgetIndex G P Q, ∀ j ∈ gadgetIndex G P Q, g i = g j → i = j)
    (hgt : ∀ i ∈ gadgetIndex G P Q, g i ∈ gadget G P Q i) {p : V} (hp : p ∈ P) :
    4 ≤ #{x ∈ (adjPairs G P Q).filter (fun e => g (inl e) = inl e) | x.1 = p} := by
  have hEp := card_adjPairs_filter_fst (G := G) (Q := Q) hp
  have hsplit := card_filter_add_card_filter_not (s := (adjPairs G P Q).filter fun e => e.1 = p)
    (fun e => g (inl e) = inl e)
  have hout : #(((adjPairs G P Q).filter fun e => e.1 = p).filter
      fun e => ¬ g (inl e) = inl e) ≤ dg G Q p - 4 := by
    have h := card_le_card_of_injOn
      (s := ((adjPairs G P Q).filter fun e => e.1 = p).filter fun e => ¬ g (inl e) = inl e)
      (t := (∅ : Finset (V × V)).disjSum (slots {p} fun p => dg G Q p - 4))
      (fun e => g (inl e)) ?_ ?_
    · rwa [card_disjSum, card_empty, zero_add, card_slots, sum_singleton] at h
    · intro e he
      rw [mem_coe, mem_filter, mem_filter] at he
      obtain ⟨⟨heE, rfl⟩, hne⟩ := he
      have hmem := hgt (inl e) (inl_mem_gadgetIndex.2 heE)
      simp only [mem_coe]
      generalize hx : g (inl e) = x at hmem hne ⊢
      rcases x with a | s
      · exact absurd (congrArg inl (inl_mem_gadget_inl.1 hmem)) hne
      · obtain ⟨hs1, hs2⟩ := inr_mem_gadget_inl.1 hmem
        exact inr_mem_disjSum.2 (mem_slots.2 ⟨mem_singleton.2 hs1, hs2⟩)
    · intro e he e' he' hee
      rw [mem_coe, mem_filter, mem_filter] at he he'
      exact inl_injective (hginj _ (inl_mem_gadgetIndex.2 he.1.1) _
        (inl_mem_gadgetIndex.2 he'.1.1) hee)
  rw [filter_comm]
  have := hP4 p hp
  omega

/-- The kept pairs at `q ∈ Q`. The slots of `q` are matched to distinct pairs at `q`, all deleted
by injectivity, so at least `deg_P q - 4` pairs at `q` are deleted and at most four are kept. -/
lemma card_kept_le_four {P Q : Finset V}
    {g : (V × V) ⊕ (V × ℕ) → (V × V) ⊕ (V × ℕ)}
    (hginj : ∀ i ∈ gadgetIndex G P Q, ∀ j ∈ gadgetIndex G P Q, g i = g j → i = j)
    (hgt : ∀ i ∈ gadgetIndex G P Q, g i ∈ gadget G P Q i) {q : V} (hq : q ∈ Q) :
    #{x ∈ (adjPairs G P Q).filter (fun e => g (inl e) = inl e) | x.2 = q} ≤ 4 := by
  have hEq := card_adjPairs_filter_snd (G := G) (P := P) hq
  have hsplit := card_filter_add_card_filter_not (s := (adjPairs G P Q).filter fun e => e.2 = q)
    (fun e => g (inl e) = inl e)
  have hslot : ∀ j < dg G P q - 4, inr (q, j) ∈ gadgetIndex G P Q := fun j hj =>
    inr_mem_gadgetIndex.2 ⟨hq, hj⟩
  have hin : dg G P q - 4 ≤ #(((adjPairs G P Q).filter fun e => e.2 = q).filter
      fun e => ¬ g (inl e) = inl e) := by
    have h := card_le_card_of_injOn (s := range (dg G P q - 4))
      (t := (((adjPairs G P Q).filter fun e => e.2 = q).filter
        fun e => ¬ g (inl e) = inl e).disjSum (∅ : Finset (V × ℕ)))
      (fun j => g (inr (q, j))) ?_ ?_
    · rwa [card_range, card_disjSum, card_empty, add_zero] at h
    · intro j hj
      simp only [coe_range, Set.mem_Iio] at hj
      have hmem := hgt _ (hslot j hj)
      simp only [mem_coe]
      generalize hx : g (inr (q, j)) = x at hmem ⊢
      rcases x with e | s
      · obtain ⟨heE, heq⟩ := inl_mem_gadget_inr.1 hmem
        refine inl_mem_disjSum.2 (mem_filter.2 ⟨mem_filter.2 ⟨heE, heq⟩, fun hgood => ?_⟩)
        exact inl_ne_inr (hginj _ (inl_mem_gadgetIndex.2 heE) _ (hslot j hj) (hgood.trans hx.symm))
      · exact absurd hmem inr_notMem_gadget_inr
    · intro j hj j' hj' hjj
      simp only [coe_range, Set.mem_Iio] at hj hj'
      have := hginj _ (hslot j hj) _ (hslot j' hj') hjj
      simpa using this
  rw [filter_comm]
  omega

/-- **The bipartite 4-factor criterion** (the direction used). If
`|P| = |Q|` and `4 |A| ≤ e(A, Q - C) + 4 |C|` for all `A ⊆ P` and `C ⊆ Q`, then the bipartite
graph `G[P, Q]` has a 4-factor: a set `F` of adjacent pairs of `P × Q` with every `p ∈ P` the
first entry of exactly four pairs and every `q ∈ Q` the second entry of exactly four pairs. -/
theorem exists_four_factor (P Q : Finset V) (hcard : #P = #Q)
    (hcut : ∀ A ⊆ P, ∀ C ⊆ Q, 4 * #A ≤ ec G A (Q \ C) + 4 * #C) :
    ∃ F ⊆ P ×ˢ Q, (∀ x ∈ F, G.Adj x.1 x.2) ∧
      (∀ p ∈ P, #{x ∈ F | x.1 = p} = 4) ∧ (∀ q ∈ Q, #{x ∈ F | x.2 = q} = 4) := by
  have hP4 : ∀ p ∈ P, 4 ≤ dg G Q p := fun p hp => four_le_dg_left hcut hp
  have hQ4 : ∀ q ∈ Q, 4 ≤ dg G P q := fun q hq => four_le_dg_right hcard hcut hq
  rcases P.eq_empty_or_nonempty with hPe | ⟨p0, -⟩
  · have hQe : Q = ∅ := card_eq_zero.1 (by rw [← hcard, hPe, card_empty])
    exact ⟨∅, empty_subset _, by simp, by simp [hPe], by simp [hQe]⟩
  have : Nonempty ((V × V) ⊕ (V × ℕ)) := ⟨inr (p0, 0)⟩
  obtain ⟨g, hginj, hgt⟩ := exists_injOn_of_hall (gadgetIndex G P Q) (gadget G P Q)
    fun S hS => gadget_hall hcut hP4 hQ4 S hS
  set F := (adjPairs G P Q).filter fun e => g (inl e) = inl e with hF
  have hFPQ : F ⊆ P ×ˢ Q := (filter_subset _ _).trans (filter_subset _ _)
  have hFP : ∀ p ∈ P, 4 ≤ #{x ∈ F | x.1 = p} := fun p hp => four_le_card_kept hP4 hginj hgt hp
  have hFQ : ∀ q ∈ Q, #{x ∈ F | x.2 = q} ≤ 4 := fun q hq => card_kept_le_four hginj hgt hq
  -- double counting the kept pairs
  have hsumP : #F = ∑ p ∈ P, #{x ∈ F | x.1 = p} :=
    card_eq_sum_card_fiberwise fun x hx => (mem_product.1 (hFPQ hx)).1
  have hsumQ : #F = ∑ q ∈ Q, #{x ∈ F | x.2 = q} :=
    card_eq_sum_card_fiberwise fun x hx => (mem_product.1 (hFPQ hx)).2
  have hlo : ∑ _p ∈ P, 4 ≤ ∑ p ∈ P, #{x ∈ F | x.1 = p} := sum_le_sum hFP
  have hhi : ∑ q ∈ Q, #{x ∈ F | x.2 = q} ≤ ∑ _q ∈ Q, 4 := sum_le_sum hFQ
  have hcP : ∑ _p ∈ P, (4 : ℕ) = 4 * #P := by rw [sum_const, smul_eq_mul, mul_comm]
  have hcQ : ∑ _q ∈ Q, (4 : ℕ) = 4 * #Q := by rw [sum_const, smul_eq_mul, mul_comm]
  have heqP : ∑ _p ∈ P, 4 = ∑ p ∈ P, #{x ∈ F | x.1 = p} := by omega
  have heqQ : ∑ q ∈ Q, #{x ∈ F | x.2 = q} = ∑ _q ∈ Q, 4 := by omega
  refine ⟨F, hFPQ, fun x hx => (mem_filter.1 (filter_subset _ _ hx)).2, fun p hp => ?_,
    fun q hq => ?_⟩
  · exact ((sum_eq_sum_iff_of_le hFP).1 heqP p hp).symm
  · exact (sum_eq_sum_iff_of_le hFQ).1 heqQ q hq

/-! ### The bridge to `sparse_core` -/

variable (G) in
/-- A quartic subgraph of the pair `(U, W)`: a nonempty set of adjacent pairs in `U × W` in which
every vertex is the first entry of 0 or 4 pairs and the second entry of 0 or 4 pairs. -/
def Quartic (U W : Finset V) : Prop :=
  ∃ F : Finset (V × V), F.Nonempty ∧ F ⊆ U ×ˢ W ∧ (∀ x ∈ F, G.Adj x.1 x.2) ∧
    (∀ u, #{x ∈ F | x.1 = u} = 0 ∨ #{x ∈ F | x.1 = u} = 4) ∧
    (∀ w, #{x ∈ F | x.2 = w} = 0 ∨ #{x ∈ F | x.2 = w} = 4)

omit [DecidableRel G.Adj] in
/-- A 4-factor of `(P, Q)` with `Q` nonempty, read with the two sides swapped, is a quartic
subgraph of `(Q, W)` for every `W ⊇ P`. -/
lemma quartic_of_four_factor {P Q W : Finset V} (hPW : P ⊆ W) (hQ : Q.Nonempty)
    {F : Finset (V × V)} (hF : F ⊆ P ×ˢ Q) (hadj : ∀ x ∈ F, G.Adj x.1 x.2)
    (hFP : ∀ p ∈ P, #{x ∈ F | x.1 = p} = 4) (hFQ : ∀ q ∈ Q, #{x ∈ F | x.2 = q} = 4) :
    Quartic G Q W := by
  refine ⟨F.map ⟨Prod.swap, Prod.swap_injective⟩, ?_, ?_, ?_, fun u => ?_, fun w => ?_⟩
  · obtain ⟨q, hq⟩ := hQ
    obtain ⟨x, hx⟩ := card_pos.1 (by rw [hFQ q hq]; norm_num : 0 < #{x ∈ F | x.2 = q})
    exact ⟨_, mem_map_of_mem _ (mem_filter.1 hx).1⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := mem_map.1 hx
    obtain ⟨h1, h2⟩ := mem_product.1 (hF hy)
    exact mem_product.2 ⟨h2, hPW h1⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := mem_map.1 hx
    exact (hadj y hy).symm
  · rw [filter_map, card_map]
    by_cases hu : u ∈ Q
    · exact Or.inr (hFQ u hu)
    · refine Or.inl (card_eq_zero.2 (filter_eq_empty_iff.2 fun x hx hxu => hu ?_))
      have hxu' : x.2 = u := hxu
      rw [← hxu']
      exact (mem_product.1 (hF hx)).2
  · rw [filter_map, card_map]
    by_cases hw : w ∈ P
    · exact Or.inr (hFP w hw)
    · refine Or.inl (card_eq_zero.2 (filter_eq_empty_iff.2 fun x hx hxw => hw ?_))
      have hxw' : x.1 = w := hxw
      rw [← hxw']
      exact (mem_product.1 (hF hx)).1

/-- **The bridge to `sparse_core`.** If the pair `(U, W)`, with `|W| = |U| + 1` and `U` nonempty,
has no quartic subgraph, then for every `y ∈ W` the balanced pair `(W - y, U)` violates the cut
condition. This is the hypothesis `hviol` of `sparse_core`: by `exists_four_factor`, the cut
condition would give a 4-factor of `(W - y, U)`, which is a quartic subgraph of `(U, W)`. The
port hypothesis `dg G U y ≤ 5` is not used; it makes the statement match `hviol`. -/
theorem hviol_of_not_quartic {U W : Finset V} (hW : #W = #U + 1) (hU : U.Nonempty)
    (hq : ¬ Quartic G U W) :
    ∀ y ∈ W, dg G U y ≤ 5 → ∃ A ⊆ W.erase y, ∃ C ⊆ U, ec G A (U \ C) + 4 * #C < 4 * #A := by
  intro y hy _
  by_contra! hcon
  obtain ⟨F, hF, hadj, hFP, hFQ⟩ := exists_four_factor (W.erase y) U
    (by rw [card_erase_of_mem hy, hW, Nat.add_sub_cancel]) hcon
  exact hq (quartic_of_four_factor (erase_subset y W) hU hF hadj hFP hFQ)

/-- **The sparse case.** A sparse pair `(U, W)` with `U` nonempty, `|W| = |U| + 1`,
degrees at most six and `D_U ≤ 1` has a quartic subgraph: otherwise `hviol_of_not_quartic`
supplies the violations that `sparse_core` rules out. -/
theorem quartic_of_sparse {U W : Finset V} (hW : #W = #U + 1) (hU : U.Nonempty)
    (hdU : ∀ u ∈ U, dg G W u ≤ 6) (hdW : ∀ w ∈ W, dg G U w ≤ 6) (hDU : df G W U ≤ 1)
    (hsp : Sparse G U W) : Quartic G U W := by
  by_contra hq
  exact sparse_core hW hdU hdW hDU hsp (hviol_of_not_quartic hW hU hq)

end Erdos585.QB4
