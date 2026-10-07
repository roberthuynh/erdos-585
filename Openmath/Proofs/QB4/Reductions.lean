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
import Openmath.Proofs.QB4.FourFactor

/-!
# QB(4): the instance classes and the reductions

This file defines the classes C1 and E4 for pairs of vertex sets and proves the two reductions
that the induction in `quartic_of_isC1` needs.

* `IsC1 G U W s`: sides `U` (size `s ≥ 1`) and `W` (size `s + 1`), degrees at most six, `D_U ≤ 1`.
* `IsE4 G P Q a`: both sides of size `a ≥ 1`, degrees at most six, deficiency at most four on each
  side.
* `Quartic.swap` and `Quartic.mono`: a quartic subgraph of a pair is one of the swapped pair and of
  every larger pair.
* `quartic_of_isE4` (the E4 reduction): an E4 instance of size `a` has a quartic subgraph
  if C1 holds below `a`.
* `small_gv_cases`, the case split behind `sparse_of_minimal` and `quartic_of_dense`: a pair with
  `g ≤ 8` and at least two vertices is an E4 instance or a C1 instance in one of the two
  orientations.
* `sparse_of_minimal` (sparsity): a quartic-free C1 instance of size `s`, with C1 holding below
  `s`, is sparse.
-/

open Finset

namespace Erdos585.QB4

variable {V : Type*} {G : SimpleGraph V} [DecidableRel G.Adj]

variable (G) in
/-- A C1 instance of size `s`: sides `U` (size `s ≥ 1`) and `W` (size `s + 1`), every
degree at most six, and deficiency `D_U ≤ 1` on the smaller side. -/
structure IsC1 (U W : Finset V) (s : ℕ) : Prop where
  pos : 1 ≤ s
  cardU : #U = s
  cardW : #W = s + 1
  degU : ∀ u ∈ U, dg G W u ≤ 6
  degW : ∀ w ∈ W, dg G U w ≤ 6
  defU : df G W U ≤ 1

variable (G) in
/-- An E4 instance of size `a`: both sides of size `a ≥ 1`, every degree at most
six, and deficiency at most four on each side. -/
structure IsE4 (P Q : Finset V) (a : ℕ) : Prop where
  pos : 1 ≤ a
  cardP : #P = a
  cardQ : #Q = a
  degP : ∀ p ∈ P, dg G Q p ≤ 6
  degQ : ∀ q ∈ Q, dg G P q ≤ 6
  defP : df G Q P ≤ 4
  defQ : df G P Q ≤ 4

/-- `e(A, B) ≤ |A| |B|`. -/
lemma ec_le_card_mul (A B : Finset V) : ec G A B ≤ #A * #B := by
  unfold ec
  calc ∑ a ∈ A, dg G B a ≤ ∑ _a ∈ A, #B := sum_le_sum fun a _ => dg_le_card B a
    _ = #A * #B := by rw [sum_const, smul_eq_mul]

variable [DecidableEq V]

/-! ### Bookkeeping for quartic subgraphs -/

omit [DecidableRel G.Adj] in
/-- A quartic subgraph of `(U, W)`, read with the two sides swapped, is one of `(W, U)`. -/
lemma Quartic.swap {U W : Finset V} (h : Quartic G U W) : Quartic G W U := by
  obtain ⟨F, hne, hsub, hadj, h1, h2⟩ := h
  refine ⟨F.map ⟨Prod.swap, Prod.swap_injective⟩, hne.map, ?_, ?_, fun u => ?_, fun w => ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := mem_map.1 hx
    obtain ⟨hy1, hy2⟩ := mem_product.1 (hsub hy)
    exact mem_product.2 ⟨hy2, hy1⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := mem_map.1 hx
    exact (hadj y hy).symm
  · rw [filter_map, card_map]
    exact h2 u
  · rw [filter_map, card_map]
    exact h1 w

omit [DecidableRel G.Adj] in
/-- A quartic subgraph of `(U, W)` is one of every pair `(U', W')` with `U ⊆ U'` and `W ⊆ W'`. -/
lemma Quartic.mono {U W U' W' : Finset V} (hU : U ⊆ U') (hW : W ⊆ W') (h : Quartic G U W) :
    Quartic G U' W' := by
  obtain ⟨F, hne, hsub, hadj, h1, h2⟩ := h
  exact ⟨F, hne, hsub.trans (product_subset_product hU hW), hadj, h1, h2⟩

/-! ### The E4 reduction -/

/-- **The E4 reduction.** An E4 instance `(P, Q)` of size `a` has a quartic subgraph if every C1
instance of size below `a` has one. Either the cut condition holds and `exists_four_factor` gives
a 4-factor, or a violated cut `(A, C)` has `k = |A| - |C| = 1` and `ε = D(C) + e(C, P - A) ≤ 1`.
Then the pieces `(C, A)` and `(P - A, Q - C)` both have in-piece deficiency at most one, and the
proof uses `(P - A, Q - C)`, a C1 instance of size `a - 1`, when `C` is empty, and `(C, A)`, a
C1 instance of size `|C|`, otherwise. -/
theorem quartic_of_isE4 {P Q : Finset V} {a : ℕ} (h : IsE4 G P Q a)
    (ih : ∀ s < a, ∀ U W : Finset V, IsC1 G U W s → Quartic G U W) : Quartic G P Q := by
  have hQne : Q.Nonempty := card_pos.1 (by rw [h.cardQ]; exact h.pos)
  by_cases hcut : ∀ A ⊆ P, ∀ C ⊆ Q, 4 * #A ≤ ec G A (Q \ C) + 4 * #C
  · obtain ⟨F, hF, hadj, hFP, hFQ⟩ := exists_four_factor P Q (h.cardP.trans h.cardQ.symm) hcut
    exact (quartic_of_four_factor Subset.rfl hQne hF hadj hFP hFQ).swap
  obtain ⟨A, hA, C, hC, hv⟩ : ∃ A ⊆ P, ∃ C ⊆ Q, ec G A (Q \ C) + 4 * #C < 4 * #A := by
    by_contra! hc
    exact hcut hc
  have hcA := card_le_card hA
  have hcC := card_le_card hC
  have hcP := h.cardP
  have hcQ := h.cardQ
  have hcPA := card_sdiff_add_card_eq_card hA
  have hcQC := card_sdiff_add_card_eq_card hC
  have hdC : ∀ x ∈ C, dg G P x ≤ 6 := fun x hx => h.degQ x (hC hx)
  -- the deficiencies of `A ⊆ P` and of `P`
  have hDA : df G Q A ≤ df G Q P := df_le_of_subset hA h.degP
  have hDP := h.defP
  have hDC0 : 0 ≤ df G P C := df_nonneg hdC
  -- the slack of `(A, C)`: `e(A, Q - C) = 6k - D_A + ε`, with `ε = D(C) + e(C, P - A)`
  have e1 := ec_sdiff_add_right (G := G) hC A
  have e2 := ec_comm (G := G) A C
  have e3 := ec_sdiff_add_right (G := G) hA C
  have e4 := df_eq (G := G) Q A
  have e5 := df_eq (G := G) P C
  -- the in-piece deficiencies of `C` in `(C, A)` and of `P - A` in `(P - A, Q - C)`
  have p1 := df_eq (G := G) A C
  have p2 := df_eq (G := G) (Q \ C) (P \ A)
  have e6 := ec_sdiff_add_right (G := G) hC (P \ A)
  have e7 := ec_comm (G := G) (P \ A) C
  have e8 := df_eq (G := G) Q (P \ A)
  have e9 := df_sdiff_add (G := G) (S := Q) hA
  -- `k = 1`, and both pieces have in-piece deficiency at most one
  have hk : #A = #C + 1 := by omega
  have hε1 : df G A C ≤ 1 := by omega
  have hε2 : df G (Q \ C) (P \ A) ≤ 1 := by omega
  rcases Nat.eq_zero_or_pos #C with hC0 | hCpos
  · -- `C = ∅`: the piece `(P - A, Q - C)` has size `a - 1 ≥ 1`
    have ha : 2 ≤ a := by
      by_contra ha
      have ha1 : a = 1 := by omega
      have hPQ : #P * #Q = 1 := by rw [hcP, hcQ, ha1]
      have := ec_le_card_mul (G := G) P Q
      have := df_eq (G := G) Q P
      omega
    have hc2 : IsC1 G (P \ A) (Q \ C) (a - 1) :=
      { pos := by omega
        cardU := by omega
        cardW := by omega
        degU := fun x hx => (dg_mono sdiff_subset x).trans (h.degP x (mem_sdiff.1 hx).1)
        degW := fun x hx => (dg_mono sdiff_subset x).trans (h.degQ x (mem_sdiff.1 hx).1)
        defU := hε2 }
    exact (ih (a - 1) (by omega) _ _ hc2).mono sdiff_subset sdiff_subset
  · -- `C ≠ ∅`: the piece `(C, A)` has size `|C| ≥ 1`
    have hc1 : IsC1 G C A #C :=
      { pos := hCpos
        cardU := rfl
        cardW := hk
        degU := fun x hx => (dg_mono hA x).trans (h.degQ x (hC hx))
        degW := fun x hx => (dg_mono hC x).trans (h.degP x (hA hx))
        defU := hε1 }
    exact (ih #C (by omega) _ _ hc1).swap.mono hA hC

/-! ### Sparsity of a minimal counterexample -/

omit [DecidableEq V] in
/-- **The case split.** A pair `(X, Y)` with degrees at most six, at least two vertices and
`g(X, Y) ≤ 8` is an E4 instance or a C1 instance in one of the two orientations. By `gv_eq_left`
and `gv_eq_right`, `g = 2d + 6j` with `j` the size difference of the sides and `d` the deficiency
of the smaller side, so `j ≤ 1`; `j = 0` gives E4 (`d ≤ 4`) and `j = 1` gives C1 (`d ≤ 1`). -/
theorem small_gv_cases {X Y : Finset V} (hdX : ∀ x ∈ X, dg G Y x ≤ 6)
    (hdY : ∀ y ∈ Y, dg G X y ≤ 6) (h2 : 2 ≤ #X + #Y) (hg : gv G X Y ≤ 8) :
    IsE4 G X Y #X ∨ IsC1 G X Y #X ∨ IsC1 G Y X #Y := by
  have hl := gv_eq_left (G := G) X Y
  have hr := gv_eq_right (G := G) X Y
  have hY0 : 0 ≤ df G X Y := df_nonneg hdY
  have hX0 : 0 ≤ df G Y X := df_nonneg hdX
  rcases lt_trichotomy #X #Y with hlt | heq | hgt
  · exact Or.inr (Or.inl
      { pos := by omega
        cardU := rfl
        cardW := by omega
        degU := hdX
        degW := hdY
        defU := by omega })
  · exact Or.inl
      { pos := by omega
        cardP := rfl
        cardQ := heq.symm
        degP := hdX
        degQ := hdY
        defP := by omega
        defQ := by omega }
  · exact Or.inr (Or.inr
      { pos := by omega
        cardU := rfl
        cardW := by omega
        degU := hdY
        degW := hdX
        defU := by omega })

/-- **Sparsity.** Let `(U, W)` be a C1 instance of size `s` with no quartic subgraph,
and suppose every C1 instance of size below `s` has one. Then `(U, W)` is sparse: every proper
sub-pair with at least two vertices has `g ≥ 10`. A sub-pair with `g ≤ 8` would be an E4 instance
of size at most `s` (covered by `quartic_of_isE4`) or a C1 instance of size below `s`, in one of
the two orientations, and its quartic subgraph would be one of `(U, W)`. -/
theorem sparse_of_minimal {U W : Finset V} {s : ℕ} (h : IsC1 G U W s)
    (ih : ∀ s' < s, ∀ U' W' : Finset V, IsC1 G U' W' s' → Quartic G U' W')
    (hq : ¬ Quartic G U W) : Sparse G U W := by
  intro X hX Y hY h2 hlt
  by_contra hg
  have hg8 : gv G X Y ≤ 8 := by
    obtain ⟨r, hr⟩ := even_gv (G := G) X Y
    omega
  have hdX : ∀ x ∈ X, dg G Y x ≤ 6 := fun x hx => (dg_mono hY x).trans (h.degU x (hX hx))
  have hdY : ∀ y ∈ Y, dg G X y ≤ 6 := fun y hy => (dg_mono hX y).trans (h.degW y (hY hy))
  have hcX := card_le_card hX
  have hcY := card_le_card hY
  have hU := h.cardU
  have hW := h.cardW
  rcases small_gv_cases hdX hdY h2 hg8 with hE | hC | hC
  · exact hq ((quartic_of_isE4 hE fun s' hs' => ih s' (by omega)).mono hX hY)
  · have := hC.cardW
    exact hq ((ih #X (by omega) X Y hC).mono hX hY)
  · have := hC.cardW
    exact hq ((ih #Y (by omega) Y X hC).swap.mono hX hY)

end Erdos585.QB4
