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
import Openmath.Proofs.QB5.KL1
import Openmath.Proofs.QB5.PairCriterion

/-!
# QB(5): a sparse C2 instance with a vertex of degree four

Part of the proof of QB(5) (`Erdos585.qb5`). Let `(U, W)` be a sparse C2 instance: `IsC2` (sides `U`
and `W` with `|W| = |U| + 1`, every degree at most six, deficiency `D(U) = 2` on `U`) and `Sparse5`
(every proper sub-pair with at least three vertices has `g ≥ 12`). This file treats the case in
which the deficiency of `U` sits on one vertex `u0` of degree four, and shows that `(U, W)` then has
a quartic subgraph (`quartic_of_sparse_c2_hub`). The proof applies KL1 (`kl1`, in `KL1.lean`) to the
2-block `(W, U - u0)` (`IsBlock`, see below): the instance is this block together with the vertex
`u0`, and the four edges at `u0`, which leave the block, are the chosen edges `M` that define the
supply `m`.

Put `A = W`, `C = U - u0` and `m(w) = 1` if `w ~ u0` (`w` is adjacent to `u0`), else `0`
(`m w = dg G {u0} w`). Write `deg` for the degree in `(U, W)` and `d_a` for the number of
neighbors of `a ∈ A` in `C`. Then:

* `(A, C)` is a 2-block (`IsBlock`: `|A| = |C| + 2 ≥ 6`, every `c ∈ C` has six neighbors in `A`,
  `g ≥ 12` on every sub-pair with at least three vertices, and `3 ≤ d_a ≤ 6` on `A`):
  `|A| = |C| + 2 ≥ 6` since `|U| ≥ 5` (`IsC2.five_le`), every `c ∈ C` has degree six (the
  deficiency two is all at `u0`), a sub-pair of `(A, C)` misses `u0` and is proper, so sparsity
  gives `g ≥ 12`, and `d_w = deg w - m(w) ≥ 4 - 1 = 3`, since every vertex of `W` has degree at
  least four (`four_le_dg_of_sparse5_right`).
* `m(A) = deg u0 = 4`, `m(w) + d_w = deg w ≤ 6` and `d_w + m(w) = deg w ≥ 4`. These are the
  hypotheses of `kl1`; the last one is its covering condition.

KL1 gives `p ∈ W` with `dem(A1) ≤ m(A1)` for every `A1 ⊆ W - p`, where
`dem(A1) = 4 |A1| - Σ_{c ∈ C} min(4, e(c, A1))` is the demand of `A1` (`dem`). Then `(W - p, U)`
satisfies the cut condition `4 |A'| ≤ e(A', U - C') + 4 |C'|` of `exists_four_factor`: for
`A' ⊆ W - p` and `C' ⊆ U`, `Σ_{c ∈ C} min(4, e(c, A')) ≤ e(A', C - C') + 4 |C ∩ C'|`
(`sum_min_four_le_ec_sdiff`); if `u0 ∈ C'` the requirement follows from `dem(A') ≤ m(A') ≤ 4`,
and if `u0 ∉ C'` from `e(A', U - C') = e(A', C - C') + m(A')` and `dem(A') ≤ m(A')`. The 4-factor
criterion `exists_four_factor` then gives a 4-factor of `(W - p, U)`, which is a quartic subgraph
of `(U, W)` (`quartic_of_four_factor`).
-/

open Finset

namespace Erdos585.QB5

open QB4

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- **A sparse C2 instance with a `U`-vertex of degree four has a quartic subgraph**, through `kl1`
on the 2-block `(W, U - u0)` with the four edges at `u0` as the chosen edges. -/
theorem quartic_of_sparse_c2_hub {U W : Finset V} {s : ℕ} (h : IsC2 G U W s)
    (hsp : Sparse5 G U W) {u0 : V} (hu0 : u0 ∈ U) (hdeg : dg G W u0 = 4) : Quartic G U W := by
  have h5 := h.five_le
  have hgv := h.gv_eq
  have hcU := h.cardU
  have hcW := h.cardW
  have hcC : #(U.erase u0) + 1 = #U := card_erase_add_one hu0
  -- the deficiency `D(U) = 2` is all at `u0`
  have hsat : ∀ c ∈ U.erase u0, dg G W c = 6 := by
    have h1 := sum_erase_add U (fun u => 6 - (dg G W u : ℤ)) hu0
    change df G W (U.erase u0) + (6 - (dg G W u0 : ℤ)) = df G W U at h1
    have h2 : df G W (U.erase u0) = 0 := by
      rw [h.defU, hdeg] at h1
      omega
    exact fun c hc => dg_eq_six_of_df_eq_zero (fun z hz => h.degU z (erase_subset u0 U hz)) h2 hc
  -- every vertex of `W` has degree at least four
  have hδW : ∀ w ∈ W, 4 ≤ dg G U w := fun w hw =>
    four_le_dg_of_sparse5_right hsp (by rw [hgv]) (by omega) hw
  -- the supply: one unit at each neighbor of `u0`
  have hsplitU : ∀ w, dg G (U.erase u0) w + dg G {u0} w = dg G U w := fun w => by
    have := dg_sdiff_add (G := G) (singleton_subset_iff.2 hu0) w
    rwa [sdiff_singleton_eq_erase] at this
  have hm1 : ∀ w, dg G {u0} w ≤ 1 := fun w => (dg_le_card {u0} w).trans (card_singleton u0).le
  have hm : ∑ w ∈ W, dg G {u0} w = 4 := by
    have := ec_comm (G := G) W {u0}
    unfold ec at this
    rw [sum_singleton] at this
    rw [this, hdeg]
  -- `(W, U - u0)` is a 2-block
  have hX : IsBlock G W (U.erase u0) :=
    { card := by omega
      six_le := by omega
      satC := hsat
      sparse := fun S hS T hT h3 => by
        rw [gv_comm]
        exact hsp T (hT.trans (erase_subset u0 U)) S hS (by omega)
          (by have := card_le_card hT; have := card_le_card hS; omega)
      three_le := fun w hw => by
        have := hsplitU w
        have := hδW w hw
        have := hm1 w
        omega
      le_six := fun w hw => by
        have := hsplitU w
        have := h.degW w hw
        omega }
  -- KL1
  obtain ⟨p, hp, hpgood⟩ := kl1 hX (fun w => dg G {u0} w) hm
    (fun w hw => by
      have := hsplitU w
      have := h.degW w hw
      omega)
    (fun w hw => by
      have := hsplitU w
      have := hδW w hw
      omega)
  -- the cut condition of `(W - p, U)`
  have hcut : ∀ A' ⊆ W.erase p, ∀ C' ⊆ U, 4 * #A' ≤ ec G A' (U \ C') + 4 * #C' := by
    intro A' hA' C' hC'
    have hdem := hpgood A' hA'
    unfold dem at hdem
    have hcap := sum_min_four_le_ec_sdiff (G := G) A' (U.erase u0) C'
    have hmA : ∑ w ∈ A', ((dg G {u0} w : ℕ) : ℤ) = (ec G A' {u0} : ℤ) := by
      unfold ec
      push_cast
      rfl
    have hmA4 : ec G A' {u0} ≤ 4 := by
      rw [← hm]
      exact sum_le_sum_of_subset (hA'.trans (erase_subset p W))
    rw [hmA] at hdem
    by_cases hu : u0 ∈ C'
    · have hUC : U \ C' = U.erase u0 \ C' := by
        ext x
        simp only [mem_sdiff, mem_erase]
        constructor
        · rintro ⟨hxU, hxC'⟩
          exact ⟨⟨fun hx => hxC' (hx ▸ hu), hxU⟩, hxC'⟩
        · rintro ⟨⟨-, hxU⟩, hxC'⟩
          exact ⟨hxU, hxC'⟩
      have hIC : U.erase u0 ∩ C' = C'.erase u0 := by
        ext x
        simp only [mem_inter, mem_erase]
        constructor
        · rintro ⟨⟨hx, -⟩, hxC'⟩
          exact ⟨hx, hxC'⟩
        · rintro ⟨hx, hxC'⟩
          exact ⟨⟨hx, hC' hxC'⟩, hxC'⟩
      have hcC' := card_erase_add_one hu
      rw [hUC]
      rw [hIC] at hcap
      zify at hmA4 hcC' ⊢
      linarith
    · have hUC : (U \ C') \ {u0} = U.erase u0 \ C' := by
        ext x
        simp only [mem_sdiff, mem_erase, mem_singleton]
        constructor
        · rintro ⟨⟨hxU, hxC'⟩, hx⟩
          exact ⟨⟨hx, hxU⟩, hxC'⟩
        · rintro ⟨⟨hx, hxU⟩, hxC'⟩
          exact ⟨⟨hxU, hxC'⟩, hx⟩
      have hsplit := ec_sdiff_add_right (G := G)
        (singleton_subset_iff.2 (mem_sdiff.2 ⟨hu0, hu⟩) : {u0} ⊆ U \ C') A'
      rw [hUC] at hsplit
      have hIC : U.erase u0 ∩ C' = C' := inter_eq_right.2 fun x hx =>
        mem_erase.2 ⟨fun h => hu (h ▸ hx), hC' hx⟩
      rw [hIC] at hcap
      rw [← hsplit]
      zify at hmA4 ⊢
      linarith
  obtain ⟨F, hF, hadj, hFP, hFQ⟩ := exists_four_factor (W.erase p) U
    (by rw [card_erase_of_mem hp]; omega) hcut
  exact quartic_of_four_factor (erase_subset p W) (card_pos.1 (by omega)) hF hadj hFP hFQ

end Erdos585.QB5
