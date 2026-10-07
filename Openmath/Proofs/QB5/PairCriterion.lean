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
import Openmath.Proofs.QB5.Defs

/-!
# QB(5): the E5 block pair and the pair criterion

Two steps of the E5 half of the proof of QB(5) that need neither `kl1` nor `refined_cover`. The
labels (E5 instance, sparse, 2-block, cut condition, violated cut, demand, under-supplied) are
defined in the module docstring of `Defs.lean`.

* `e5_blocks`: a violated cut `(A, C)` of a sparse E5 instance `(P, Q)` makes `X = (A, C)` and
  `Y = (D, B)`, `B = P - A`, `D = Q - C`, two 2-blocks (`IsBlock`), joined by exactly seven
  edges, all between `A` and `D`. The proof: the exact slack (`ec_sdiff_eq`) is
  `σ = 2k - D(A) + ε` with `k = |A| - |C|`, `ε = D(C) + e(P - A, C)`, and `g(A, C) = 6k + 2ε`;
  `D(A) ≤ 5` and sparsity force `k = 2`, `ε = 0`, `D(A) = 5`.
* `cut_condition_of_good_pair`: the pair criterion, in the direction that the proof uses.

Setting of the pair criterion. A pair `(P, Q)` with a violated cut `(A, C)`, `A ⊆ P` and `C ⊆ Q`,
splits into the 2-blocks `X = (A, C)` and `Y = (D, B)` with `B = P - A` and `D = Q - C`, where
`|D| = |B| + 2` and every `b ∈ B` has six neighbors in `D` and none in `C`. A set `M` of at most
four adjacent pairs supplies `p` and `q` if no `A1 ⊆ A - p` and no `D1 ⊆ D - q` is under-supplied:
`dem_X(A1) ≤ m(A1)` and `dem_Y(D1) ≤ m(D1)`, where `dem_X = dem G C` and `dem_Y = dem G B` are the
demands in the two blocks, `m(A1)` counts the pairs of `M` with first entry in `A1` and `m(D1)`
those with second entry in `D1`. Then the pair `(P - p, Q - q)` satisfies the cut condition of
`exists_four_factor` (`cut_condition_of_good_pair`).

The proof: for `A' ⊆ P - p` and `C' ⊆ Q - q` put `A1 = A' ∩ A`, `B1 = A' - A` and
`D1 = (D - q) - (C' - C)`. Then `(Q - q) - C'` is the disjoint union of `C - C'` and `D1`, there
are no `B`-`C` edges, and

* `e(A1, C - C') + 4 |C' ∩ C| ≥ Σ_{c ∈ C} min(4, e(c, A1)) = 4 |A1| - dem_X(A1)`
  (`sum_min_four_le_ec_sdiff`);
* `e(B1, D1) - 4 |B1| ≥ Σ_{b ∈ B} min(4, e(b, D1)) - 4 |B| = 4 |D1| - dem_Y(D1) - 4 |B|`
  (`sum_min_four_sub_le_ec`);
* `dem_X(A1) + dem_Y(D1) ≤ m(A1) + m(D1) ≤ |M| + e(A1, D1) ≤ 4 + e(A1, D1)`
  (`card_fst_add_card_snd_le` for the last two steps).

Summing, with `|C' - C| + |D1| = |D| - 1 = |B| + 1`, gives `4 |A'| ≤ e(A', (Q - q) - C') + 4 |C'|`.
In this direction `p ∈ A`, `M ⊆ A × D`, `p, q ∉ V(M)` (the entries of the pairs of `M`) and the
fact that every `c ∈ C` has six neighbors in `A` are not needed.
-/

open Finset

namespace Erdos585.QB5

open QB4

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ### Two 2-blocks and a 7-edge cut -/

/-- **Two 2-blocks and a 7-edge cut.** A violated cut `(A, C)` of a sparse E5 instance `(P, Q)`
makes `X = (A, C)` and `Y = (Q - C, P - A)` two 2-blocks (`IsBlock`): `|A| = |C| + 2` and
`|Q - C| = |P - A| + 2`, `C` has all its neighbors in `A` and `P - A` all its neighbors in
`Q - C`, six each; exactly seven edges join `A` and `Q - C`; `D(A) = D(Q - C) = 5`; and
`|C|, |P - A| ≥ 4`. -/
theorem e5_blocks {P Q : Finset V} {a : ℕ} (h : IsE5 G P Q a)
    (hsp : Sparse5 G P Q) {A C : Finset V} (hA : A ⊆ P) (hC : C ⊆ Q)
    (hviol : ec G A (Q \ C) + 4 * #C < 4 * #A) :
    #A = #C + 2 ∧ #(Q \ C) = #(P \ A) + 2 ∧ (∀ c ∈ C, dg G A c = 6) ∧
      (∀ b ∈ P \ A, dg G (Q \ C) b = 6) ∧ ec G A (Q \ C) = 7 ∧ df G Q A = 5 ∧
      df G P (Q \ C) = 5 ∧ 4 ≤ #C ∧ 4 ≤ #(P \ A) ∧
      IsBlock G A C ∧ IsBlock G (Q \ C) (P \ A) := by
  have hgv := h.gv_eq
  have h5 := h.five_le
  have hcP := h.cardP
  have hcQ := h.cardQ
  have hδP : ∀ x ∈ P, 4 ≤ dg G Q x := fun x hx =>
    four_le_dg_of_sparse5_left hsp (by rw [hgv]) (by omega) hx
  have hδQ : ∀ y ∈ Q, 4 ≤ dg G P y := fun y hy =>
    four_le_dg_of_sparse5_right hsp (by rw [hgv]) (by omega) hy
  have hcA := card_le_card hA
  have hcC := card_le_card hC
  -- the exact slack (`ec_sdiff_eq`)
  have hslack := ec_sdiff_eq (G := G) hA hC
  have hDA : df G Q A ≤ 5 := h.defP ▸ df_le_of_subset hA h.degP
  have hDC : 0 ≤ df G P C := df_nonneg fun c hc => h.degQ c (hC hc)
  -- `C` is nonempty: `e(A, Q) ≥ 4 |A|`
  have hCne : C.Nonempty := by
    rw [nonempty_iff_ne_empty]
    rintro rfl
    have : ∑ _x ∈ A, 4 ≤ ec G A Q := sum_le_sum fun x hx => hδP x (hA hx)
    rw [sum_const, smul_eq_mul, sdiff_empty] at *
    omega
  have hC1 := card_pos.2 hCne
  -- `g(A, C) = 6 k + 2 ε` with `k = |A| - |C|`, `ε = D(C) + e(P - A, C)`
  have hgAC : gv G A C = 6 * ((#A : ℤ) - #C) + 2 * (df G P C + ec G (P \ A) C) := by
    have e1 := ec_sdiff_add_right (G := G) hA C
    have e2 := ec_comm (G := G) C (P \ A)
    have e3 := ec_comm (G := G) A C
    have e4 := df_eq (G := G) P C
    unfold gv
    omega
  have hspAC := hsp A hA C hC (by omega) (by omega)
  -- so `k = 2`, `ε = 0`, `D(A) = 5`
  have hk : #A = #C + 2 := by omega
  have hDC0 : df G P C = 0 := by omega
  have heBC : ec G (P \ A) C = 0 := by omega
  have hDA5 : df G Q A = 5 := by omega
  have hcut : ec G A (Q \ C) = 7 := by omega
  -- every `c ∈ C` has six neighbors in `A`, and every `b ∈ B = P - A` six in `Q - C`
  have hsatC : ∀ c ∈ C, dg G A c = 6 := fun c hc => by
    have h6 := dg_eq_six_of_df_eq_zero (fun z hz => h.degQ z (hC hz)) hDC0 hc
    have h0 : dg G (P \ A) c = 0 := by
      have := ec_comm (G := G) (P \ A) C
      rw [heBC] at this
      exact (sum_eq_zero_iff.1 this.symm) c hc
    have := dg_sdiff_add (G := G) hA c
    omega
  have hDB0 : df G Q (P \ A) = 0 := by
    have := df_sdiff_add (G := G) (S := Q) hA
    rw [h.defP] at this
    omega
  have hBC0 : ∀ b ∈ P \ A, dg G C b = 0 := fun b hb => (sum_eq_zero_iff.1 heBC) b hb
  have hsatB : ∀ b ∈ P \ A, dg G (Q \ C) b = 6 := fun b hb => by
    have h6 := dg_eq_six_of_df_eq_zero (fun z hz => h.degP z (sdiff_subset hz)) hDB0 hb
    have := dg_sdiff_add (G := G) hC b
    have := hBC0 b hb
    omega
  have hcB := card_sdiff_add_card_eq_card hA
  have hcD := card_sdiff_add_card_eq_card hC
  have hcardB : #(Q \ C) = #(P \ A) + 2 := by omega
  have hDD : df G P (Q \ C) = 5 := by
    have := df_sdiff_add (G := G) (S := P) hC
    rw [h.defQ, hDC0] at this
    omega
  -- `|C| ≥ 4`: a vertex of `C` has six neighbors in `A`
  have hC4 : 4 ≤ #C := by
    obtain ⟨c, hc⟩ := hCne
    have := hsatC c hc
    have := dg_le_card (G := G) A c
    omega
  -- `|B| ≥ 4`: `7 + 6 |B| = e(D, A) + e(D, B) = e(D, P) ≥ 4 |D| = 4 |B| + 8`, so `B ≠ ∅`
  have hB4 : 4 ≤ #(P \ A) := by
    have hBne : (P \ A).Nonempty := by
      rw [← card_pos]
      have e1 := ec_sdiff_add_right (G := G) hA (Q \ C)
      have e2 := ec_comm (G := G) (Q \ C) A
      have e3 := ec_comm (G := G) (Q \ C) (P \ A)
      have e4 : ec G (P \ A) (Q \ C) = ∑ _b ∈ P \ A, 6 := sum_congr rfl hsatB
      have e5 : ∑ _y ∈ Q \ C, 4 ≤ ec G (Q \ C) P :=
        sum_le_sum fun y hy => hδQ y (sdiff_subset hy)
      rw [sum_const, smul_eq_mul] at e4 e5
      omega
    obtain ⟨b, hb⟩ := hBne
    have := hsatB b hb
    have := dg_le_card (G := G) (Q \ C) b
    omega
  refine ⟨hk, hcardB, hsatC, hsatB, hcut, hDA5, hDD, hC4, hB4, ?_, ?_⟩
  · -- the block `X = (A, C)`
    have hg12 : gv G A C = 12 := by rw [hgAC, hDC0, heBC]; push_cast; omega
    refine ⟨hk, by omega, hsatC, fun S hS T hT h3 => hsp S (hS.trans hA) T (hT.trans hC) h3
      (by have := card_le_card hS; have := card_le_card hT; omega), fun x hx => ?_,
      fun x hx => (dg_mono hC x).trans (h.degP x (hA hx))⟩
    have h1 := gv_erase_left (G := G) hx C
    have h2 := card_erase_add_one hx
    have h3 := hsp (A.erase x) ((erase_subset x A).trans hA) C hC (by omega) (by omega)
    omega
  · -- the block `Y = (D, B)`
    have hecDB : ec G (Q \ C) (P \ A) = 6 * #(P \ A) := by
      rw [ec_comm]
      unfold ec
      rw [sum_congr rfl hsatB, sum_const, smul_eq_mul, mul_comm]
    have hg12 : gv G (Q \ C) (P \ A) = 12 := by
      unfold gv
      rw [hecDB, hcardB]
      push_cast
      ring
    refine ⟨hcardB, ?_, hsatB, fun S hS T hT h3 => ?_, fun y hy => ?_,
      fun y hy => (dg_mono sdiff_subset y).trans (h.degQ y (sdiff_subset hy))⟩
    · obtain ⟨b, hb⟩ := card_pos.1 (by omega : 0 < #(P \ A))
      have := hsatB b hb
      have := dg_le_card (G := G) (Q \ C) b
      omega
    · rw [gv_comm]
      exact hsp T (hT.trans sdiff_subset) S (hS.trans sdiff_subset) (by omega)
        (by have := card_le_card hS; have := card_le_card hT; omega)
    · have h1 := gv_erase_left (G := G) hy (P \ A)
      have h2 := card_erase_add_one hy
      have h3 := hsp (P \ A) sdiff_subset ((Q \ C).erase y) ((erase_subset y _).trans sdiff_subset)
        (by omega) (by omega)
      rw [gv_comm] at h3
      omega

/-! ### The pair criterion -/

/-- Edge counts add over a disjoint union of the second set. -/
private lemma ec_union_right_of_disjoint (X : Finset V) {S T : Finset V} (h : Disjoint S T) :
    ec G X (S ∪ T) = ec G X S + ec G X T := by
  unfold ec
  rw [← sum_add_distrib]
  exact sum_congr rfl fun x _ => dg_union_of_disjoint h x

/-- Edge counts add over the split of the first set by membership in `A`. -/
private lemma ec_filter_add_filter_not (X A S : Finset V) :
    ec G {x ∈ X | x ∈ A} S + ec G {x ∈ X | x ∉ A} S = ec G X S :=
  sum_filter_add_sum_filter_not X (· ∈ A) (dg G S)

/-- **The capped count of the demand against a cut** (the first inequality in the module
docstring): for all `A1`, `C` and `C'`, `Σ_{c ∈ C} min(4, e(c, A1)) ≤ e(A1, C - C') + 4 |C ∩ C'|`.
-/
lemma sum_min_four_le_ec_sdiff (A1 C C' : Finset V) :
    ∑ c ∈ C, (min 4 (dg G A1 c) : ℤ) ≤ (ec G A1 (C \ C') : ℤ) + 4 * #(C ∩ C') := by
  rw [← sum_inter_add_sum_sdiff C C', ec_comm]
  have h1 : ∑ c ∈ C ∩ C', (min 4 (dg G A1 c) : ℤ) ≤ ∑ _c ∈ C ∩ C', (4 : ℤ) :=
    sum_le_sum fun c _ => min_le_left _ _
  have h2 : ∑ c ∈ C \ C', (min 4 (dg G A1 c) : ℤ) ≤ ∑ c ∈ C \ C', (dg G A1 c : ℤ) :=
    sum_le_sum fun c _ => min_le_right _ _
  have h3 : (ec G (C \ C') A1 : ℤ) = ∑ c ∈ C \ C', (dg G A1 c : ℤ) := by
    unfold ec
    push_cast
    rfl
  rw [sum_const, nsmul_eq_mul] at h1
  linarith

/-- **The capped count on the second block** (the second inequality in the module docstring): for
`B1 ⊆ B`, `Σ_{b ∈ B} min(4, e(b, D1)) - 4 |B| ≤ e(B1, D1) - 4 |B1|`. -/
private lemma sum_min_four_sub_le_ec {B B1 : Finset V} (hB1 : B1 ⊆ B) (D1 : Finset V) :
    ∑ b ∈ B, (min 4 (dg G D1 b) : ℤ) - 4 * #B ≤ (ec G B1 D1 : ℤ) - 4 * #B1 := by
  have hsplit := sum_sdiff (f := fun b => (min 4 (dg G D1 b) : ℤ) - 4) hB1
  have h1 : ∑ b ∈ B \ B1, ((min 4 (dg G D1 b) : ℤ) - 4) ≤ 0 :=
    sum_nonpos fun b _ => by have := min_le_left (4 : ℤ) (dg G D1 b); linarith
  have h2 : ∑ b ∈ B1, ((min 4 (dg G D1 b) : ℤ) - 4) ≤ ∑ b ∈ B1, ((dg G D1 b : ℤ) - 4) :=
    sum_le_sum fun b _ => by have := min_le_right (4 : ℤ) (dg G D1 b); linarith
  have h3 : (ec G B1 D1 : ℤ) = ∑ b ∈ B1, (dg G D1 b : ℤ) := by
    unfold ec
    push_cast
    rfl
  simp only [sum_sub_distrib, sum_const, nsmul_eq_mul] at hsplit h1 h2
  linarith

/-- **The supply count** (the third inequality in the module docstring): for a set `M` of at most
four adjacent pairs, `m(A1) + m(D1) ≤ 4 + e(A1, D1)`, where `m(A1)` counts the pairs with first
entry in `A1` and `m(D1)` the pairs with second entry in `D1`. -/
private lemma card_fst_add_card_snd_le (M : Finset (V × V)) (hMadj : ∀ x ∈ M, G.Adj x.1 x.2)
    (hM4 : #M ≤ 4) (A1 D1 : Finset V) :
    #{x ∈ M | x.1 ∈ A1} + #{x ∈ M | x.2 ∈ D1} ≤ 4 + ec G A1 D1 := by
  have hu : #({x ∈ M | x.1 ∈ A1} ∪ {x ∈ M | x.2 ∈ D1}) ≤ 4 :=
    (card_le_card (union_subset (filter_subset _ _) (filter_subset _ _))).trans hM4
  have hi : #({x ∈ M | x.1 ∈ A1} ∩ {x ∈ M | x.2 ∈ D1}) ≤ ec G A1 D1 := by
    rw [← card_adjPairs]
    refine card_le_card fun x hx => ?_
    obtain ⟨hx1, hx2⟩ := mem_inter.1 hx
    obtain ⟨hxM, hxA⟩ := mem_filter.1 hx1
    obtain ⟨-, hxD⟩ := mem_filter.1 hx2
    exact mem_filter.2 ⟨mem_product.2 ⟨hxA, hxD⟩, hMadj x hxM⟩
  have := card_union_add_card_inter {x ∈ M | x.1 ∈ A1} {x ∈ M | x.2 ∈ D1}
  omega

/-- **The pair criterion, in the direction used.** Let `A ⊆ P` and `C ⊆ Q` with
`|Q - C| = |P - A| + 2`, where every `b ∈ P - A` has six neighbors in `Q - C` and at most six in
`Q`. Let `M` be a set of at most four adjacent pairs, `q ∈ Q - C`, and suppose that no
`A1 ⊆ A - p` and no `D1 ⊆ (Q - C) - q` is under-supplied by `M`, in the sense of the module
docstring. Then `(P - p, Q - q)` satisfies the cut condition of `exists_four_factor`. -/
theorem cut_condition_of_good_pair {P Q A C : Finset V} (hC : C ⊆ Q)
    (hcardB : #(Q \ C) = #(P \ A) + 2) (hsatB : ∀ b ∈ P \ A, dg G (Q \ C) b = 6)
    (hdegB : ∀ b ∈ P \ A, dg G Q b ≤ 6) (M : Finset (V × V)) (hMadj : ∀ x ∈ M, G.Adj x.1 x.2)
    (hM4 : #M ≤ 4) {p q : V} (hq : q ∈ Q \ C)
    (hX : ∀ A1 ⊆ A.erase p, dem G C A1 ≤ (#{x ∈ M | x.1 ∈ A1} : ℤ))
    (hY : ∀ D1 ⊆ (Q \ C).erase q, dem G (P \ A) D1 ≤ (#{x ∈ M | x.2 ∈ D1} : ℤ)) :
    ∀ A' ⊆ P.erase p, ∀ C' ⊆ Q.erase q, 4 * #A' ≤ ec G A' (Q.erase q \ C') + 4 * #C' := by
  intro A' hA' C' hC'
  have hqC : q ∉ C := (mem_sdiff.1 hq).2
  set A1 := {x ∈ A' | x ∈ A} with hA1def
  set B1 := {x ∈ A' | x ∉ A} with hB1def
  set D1 := ((Q \ C).erase q) \ (C' \ C) with hD1def
  -- the pieces
  have hA1 : A1 ⊆ A.erase p := fun x hx => by
    obtain ⟨hxA', hxA⟩ := mem_filter.1 hx
    exact mem_erase.2 ⟨(mem_erase.1 (hA' hxA')).1, hxA⟩
  have hB1 : B1 ⊆ P \ A := fun x hx => by
    obtain ⟨hxA', hxA⟩ := mem_filter.1 hx
    exact mem_sdiff.2 ⟨(mem_erase.1 (hA' hxA')).2, hxA⟩
  have hD1 : D1 ⊆ (Q \ C).erase q := sdiff_subset
  have hC'C : C' \ C ⊆ (Q \ C).erase q := fun x hx => by
    obtain ⟨hxC', hxC⟩ := mem_sdiff.1 hx
    obtain ⟨hxq, hxQ⟩ := mem_erase.1 (hC' hxC')
    exact mem_erase.2 ⟨hxq, mem_sdiff.2 ⟨hxQ, hxC⟩⟩
  -- the second set of the cut splits into `C - C'` and `D1`
  have hR : Q.erase q \ C' = (C \ C') ∪ D1 := by
    ext x
    simp only [hD1def, mem_sdiff, mem_erase, mem_union]
    constructor
    · rintro ⟨⟨hxq, hxQ⟩, hxC'⟩
      by_cases hxC : x ∈ C
      · exact Or.inl ⟨hxC, hxC'⟩
      · exact Or.inr ⟨⟨hxq, hxQ, hxC⟩, fun h => hxC' h.1⟩
    · rintro (⟨hxC, hxC'⟩ | ⟨⟨hxq, hxQ, hxC⟩, hx⟩)
      · exact ⟨⟨fun h => hqC (h ▸ hxC), hC hxC⟩, hxC'⟩
      · exact ⟨⟨hxq, hxQ⟩, fun h => hx ⟨h, hxC⟩⟩
  have hdisj : Disjoint (C \ C') D1 := by
    rw [disjoint_left]
    intro x hx hxD
    exact (mem_sdiff.1 (mem_erase.1 (sdiff_subset hxD)).2).2 (mem_sdiff.1 hx).1
  -- edge counts
  have hec : ec G A' (Q.erase q \ C') =
      ec G A1 (C \ C') + ec G A1 D1 + (ec G B1 (C \ C') + ec G B1 D1) := by
    rw [hR, ← ec_filter_add_filter_not A' A, ec_union_right_of_disjoint _ hdisj,
      ec_union_right_of_disjoint _ hdisj]
  have hBC : ec G B1 (C \ C') = 0 := by
    refine sum_eq_zero fun b hb => ?_
    have hbB := hB1 hb
    have h1 := dg_sdiff_add (G := G) hC b
    have h2 := hsatB b hbB
    have h3 := hdegB b hbB
    have h4 := dg_mono (G := G) (sdiff_subset : C \ C' ⊆ C) b
    omega
  -- cardinalities
  have hcA : #A1 + #B1 = #A' := card_filter_add_card_filter_not (s := A') (· ∈ A)
  have hcC : #(C' ∩ C) + #(C' \ C) = #C' := by
    have := card_sdiff_add_card_eq_card (inter_subset_left : C' ∩ C ⊆ C')
    rw [sdiff_inter_self_left] at this
    omega
  have hcD : #D1 + #(C' \ C) + 1 = #(Q \ C) := by
    have h1 := card_sdiff_add_card_eq_card hC'C
    have h2 := card_erase_add_one hq
    rw [← hD1def] at h1
    omega
  -- the three inequalities
  have hcap1 := sum_min_four_le_ec_sdiff (G := G) A1 C C'
  have hcap2 := sum_min_four_sub_le_ec (G := G) hB1 D1
  have hsup := card_fst_add_card_snd_le M hMadj hM4 A1 D1
  have hdX := hX A1 hA1
  have hdY := hY D1 hD1
  rw [inter_comm] at hcap1
  unfold dem at hdX hdY
  zify at hec hBC hcA hcC hcD hcardB hsup ⊢
  linarith

end Erdos585.QB5
