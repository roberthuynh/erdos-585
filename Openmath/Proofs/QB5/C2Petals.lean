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
# QB(5), C2 with two deficient `U`-vertices: port petals, the lattice, 2-blocks, the budget

Part of the proof of QB(5) (`Erdos585.qb5`). This file and `C2TwoBlock.lean` show that a sparse
C2 instance `(U, W)` (`IsC2`, `Sparse5`) whose deficiency `D_U = 2` sits on two `U`-vertices of
degree five has a quartic subgraph. This file holds the tools, in the pair setting of QB4, and
`C2TwoBlock.lean` combines them (`quartic_of_sparse_c2_ports`).

Notation. `D(·)`, `D_U` and `def(y) = 6 - dg G U y` are the deficiency notation of QB4's
`Defs.lean`. `Z` is the set of the two `U`-vertices of degree five. A *sub-pair* `R = (X, Y)` has
`X ⊆ U` and `Y ⊆ W`, and it is *proper* if `|X| + |Y| < |U| + |W|`. Containment, unions,
intersections and differences of sub-pairs are taken side by side, and `R_U = X`, `R_W = Y` are the
sides of `R`. Write `κ(R) = |X| - |Y|` and `h(R) = df G X Y`, the deficiency of `Y` inside `R`, so
that `g(R) = 2 h(R) + 6 κ(R)` (`gv_eq_left`) and `h(R) ≥ D(Y)`. A *port* is a vertex of `W` of
degree at most five.

* `C2P.Setting G U W Z`: a sparse C2 instance `(U, W)` whose deficient `U`-vertices are the two
  vertices of `Z`, both of degree five.
* `C2P.Fam G U W Z g k X Y`: a proper sub-pair `(X, Y)` with `Z ⊆ X`, `g(X, Y) = g` and
  `κ = |X| - |Y| = k`. Three families are used: `𝒜 = Fam 12 1`, `Fam 12 2` and `Fam 14 2`. A
  *`W`-small 2-block* on `Z` is a member of `Fam 12 2` (so it contains `Z`); its `W`-side is the
  smaller one, and every vertex of its `W`-side has six neighbors in its `U`-side (`C2P.block_sat`).
  It need not satisfy `IsBlock`: `(Z, ∅)` is a `W`-small 2-block.
* `C2P.Setting.twelve_le_gv`: every proper sub-pair containing `Z` has `g ≥ 12`, including
  `(Z, ∅)` itself, so the proper unions and the intersections of members of the families have
  `g ≥ 12` whatever their size.
* `C2P.port_petal` (petals at a port): let `y` be a port and `(A, C)` a violated cut of the
  balanced pair `(W - y, U)`, that is `A ⊆ W - y`, `C ⊆ U` and `e(A, U - C) + 4 |C| < 4 |A|`, so
  that the cut condition of `exists_four_factor` fails. Then the complement `(U - C, W - A)`
  contains `y` and lies in `Fam 12 1` or in `Fam 14 2`; call it an *α-petal* or a *β-petal* of
  `y`.
* `C2P.lattice` (the lattice lemma): for `S` in `Fam g k` and `S'` in `Fam g' k'` with
  `g + g' < 6 (k + k') + 16`, the union `S ∪ S'` is proper, the union and the intersection have
  `g ≥ 12`, and `g(S ∪ S') + g(S ∩ S') ≤ g + g'`.
* `C2P.block_sat`, `C2P.block_boundary`: for a `W`-small 2-block `T` on `Z`, every vertex of
  `T_W` has six neighbors in `T_U`, and exactly ten edges leave `T`, all between `T_U` and
  `W - T_W`.
* `C2P.part_bound` (one inequality per part): for a `W`-small 2-block `T` on `Z` and every
  `R ⊇ T` in `Fam 12 1` or `Fam 14 2`, `3 D(R_W - T_W) ≤ 2 e(R_W - T_W, T_U)`.
* `C2P.budget`: the final count. If each `y ∈ P` has a part `f y ∋ y` inside `B`, two parts are
  equal or disjoint, `d, ω ≥ 0` on `B`, and each part has `3 Σ d ≤ 2 Σ ω`, then
  `3 Σ_P d ≤ 2 Σ_B ω`.
-/

open Finset

namespace Erdos585.QB5

open QB4

namespace C2P

variable {V : Type*} {G : SimpleGraph V} [DecidableRel G.Adj]

variable (G) in
/-- The setting of this file and of `C2TwoBlock.lean`: a sparse C2 instance `(U, W)`
(`|W| = |U| + 1`, degrees at most six, `D_U = 2`, `Sparse5`) whose deficiency sits on the two
vertices of `Z ⊆ U`, both of degree five; every other vertex of `U` has degree six. -/
structure Setting (U W Z : Finset V) : Prop where
  degU : ∀ u ∈ U, dg G W u ≤ 6
  degW : ∀ w ∈ W, dg G U w ≤ 6
  cardW : #W = #U + 1
  defU : df G W U = 2
  sparse : Sparse5 G U W
  subZ : Z ⊆ U
  cardZ : #Z = 2
  degZ : ∀ z ∈ Z, dg G W z = 5
  degU6 : ∀ u ∈ U, u ∉ Z → dg G W u = 6

variable (G) in
/-- The proper sub-pairs `(X, Y)` of `(U, W)` (`|X| + |Y| < |U| + |W|`) with `Z ⊆ X`,
`g(X, Y) = g0` and `κ = |X| - |Y| = k`. The proof uses `𝒜 = Fam 12 1`, the `W`-small 2-blocks on
`Z` (`Fam 12 2`) and `Fam 14 2`, which contains the β-petals. -/
def Fam (U W Z : Finset V) (g0 : ℤ) (k : ℕ) (X Y : Finset V) : Prop :=
  X ⊆ U ∧ Y ⊆ W ∧ Z ⊆ X ∧ #X + #Y < #U + #W ∧ gv G X Y = g0 ∧ #X = #Y + k

namespace Setting

variable {U W Z : Finset V}

/-- A C2 instance has `g = 10`. -/
lemma gv_eq (hS : Setting G U W Z) : gv G U W = 10 := by
  rw [gv_full hS.cardW, hS.defU]
  norm_num

/-- A C2 instance has `D(W) = 8`. -/
lemma dfW (hS : Setting G U W Z) : df G U W = 8 := by
  rw [df_right_eq hS.cardW, hS.defU]
  norm_num

/-- `U` has at least the two vertices of `Z`. -/
lemma two_le_card (hS : Setting G U W Z) : 2 ≤ #U := hS.cardZ ▸ card_le_card hS.subZ

/-- `g ≥ 6 κ` on sub-pairs, from `g = 2h + 6κ` (`gv_eq_left`) and `h ≥ 0`. -/
lemma six_mul_le_gv (hS : Setting G U W Z) {X Y : Finset V} (hX : X ⊆ U) (hY : Y ⊆ W) :
    6 * ((#X : ℤ) - #Y) ≤ gv G X Y := by
  have h1 := gv_eq_left (G := G) X Y
  have h2 : 0 ≤ df G X Y := df_nonneg fun y hy => (dg_mono hX y).trans (hS.degW y (hY hy))
  linarith

/-- `g ≥ -6 κ` on sub-pairs, from `gv_eq_right`: the deficiency of `X` inside the pair is at
least zero. -/
lemma six_mul_le_gv' (hS : Setting G U W Z) {X Y : Finset V} (hX : X ⊆ U) (hY : Y ⊆ W) :
    6 * ((#Y : ℤ) - #X) ≤ gv G X Y := by
  have h1 := gv_eq_right (G := G) X Y
  have h2 : 0 ≤ df G Y X := df_nonneg fun x hx => (dg_mono hY x).trans (hS.degU x (hX hx))
  linarith

/-- **Sparsity on sets containing `Z`.** Every proper sub-pair whose first set contains `Z` has
`g ≥ 12`: with at least three vertices by sparsity, and otherwise it is `(Z, ∅)`, with `g = 12`.
-/
lemma twelve_le_gv (hS : Setting G U W Z) {X Y : Finset V} (hX : X ⊆ U) (hY : Y ⊆ W)
    (hZX : Z ⊆ X) (hlt : #X + #Y < #U + #W) : 12 ≤ gv G X Y := by
  by_cases h3 : 3 ≤ #X + #Y
  · exact hS.sparse X hX Y hY h3 hlt
  · have hZ := card_le_card hZX
    rw [hS.cardZ] at hZ
    have hY0 : Y = ∅ := card_eq_zero.1 (by omega)
    have hX2 : #X = 2 := by omega
    subst hY0
    have he : ec G X ∅ = 0 := by simp [ec, dg]
    unfold gv
    rw [he, hX2]
    norm_num

/-- `(Z, ∅)` is a `W`-small 2-block containing `Z` (`g = 12`, `κ = 2`), so the family of
`W`-small 2-blocks on `Z` is never empty. `C2TwoBlock.lean` takes a member of maximum size,
which may be `(Z, ∅)` itself. -/
lemma fam_Z (hS : Setting G U W Z) : Fam G U W Z 12 2 Z ∅ := by
  have h2 := hS.two_le_card
  have hcW := hS.cardW
  have he : ec G Z ∅ = 0 := by simp [ec, dg]
  refine ⟨hS.subZ, empty_subset _, Subset.rfl, ?_, ?_, ?_⟩
  · rw [hS.cardZ, card_empty]
    omega
  · unfold gv
    rw [he, hS.cardZ, card_empty]
    norm_num
  · rw [hS.cardZ, card_empty]

/-- A proper sub-pair with at least two vertices has `g ≥ 10`. -/
lemma ten_le_gv (hS : Setting G U W Z) {X Y : Finset V} (hX : X ⊆ U) (hY : Y ⊆ W)
    (h2 : 2 ≤ #X + #Y) (hlt : #X + #Y < #U + #W) : 10 ≤ gv G X Y := by
  by_cases h3 : 3 ≤ #X + #Y
  · have := hS.sparse X hX Y hY h3 hlt
    linarith
  · have h1 := ec_le_card_mul (G := G) X Y
    have h4 : #X * #Y ≤ 1 := by
      rcases (by omega : #X = 0 ∨ #X = 1 ∨ #X = 2) with h | h | h
      · rw [h, zero_mul]
        norm_num
      · rw [h, show #Y = 1 by omega]
      · rw [show #Y = 0 by omega, mul_zero]
        norm_num
    unfold gv
    omega

variable [DecidableEq V]

/-- Every `U`-vertex has degree at least five. -/
lemma five_le_dg (hS : Setting G U W Z) {u : V} (hu : u ∈ U) : 5 ≤ dg G W u := by
  by_cases hz : u ∈ Z
  · rw [hS.degZ u hz]
  · rw [hS.degU6 u hu hz]
    norm_num

/-- Every vertex of `W` has degree at least four (`four_le_dg_of_sparse5_right`). -/
lemma four_le_dg (hS : Setting G U W Z) {w : V} (hw : w ∈ W) : 4 ≤ dg G U w :=
  four_le_dg_of_sparse5_right hS.sparse (by rw [hS.gv_eq])
    (by have := hS.two_le_card; have := hS.cardW; omega) hw

/-- A subset of `U` containing `Z` carries all of `D_U = 2`. -/
lemma df_of_subset (hS : Setting G U W Z) {X : Finset V} (hX : X ⊆ U) (hZX : Z ⊆ X) :
    df G W X = 2 := by
  have h1 := df_sdiff_add (G := G) (S := W) hX
  have h2 : df G W (U \ X) = 0 := sum_eq_zero fun u hu => by
    have hu' := mem_sdiff.1 hu
    rw [hS.degU6 u hu'.1 fun hz => hu'.2 (hZX hz)]
    norm_num
  linarith [hS.defU]

/-- A subset of `U` with no deficiency misses `Z`. -/
lemma subset_sdiff_of_df (hS : Setting G U W Z) {C : Finset V} (hC : C ⊆ U)
    (h0 : df G W C = 0) : Z ⊆ U \ C := by
  intro z hz
  refine mem_sdiff.2 ⟨hS.subZ hz, fun hzC => ?_⟩
  have h6 := dg_eq_six_of_df_eq_zero (fun c hc => hS.degU c (hC hc)) h0 hzC
  rw [hS.degZ z hz] at h6
  omega

end Setting

/-! ### `W`-small 2-blocks containing `Z` -/

/-- **Saturation.** In a `W`-small 2-block `T = (X, Y)` (`g = 12`, `κ = 2`) every vertex of `Y`
has six neighbors in `X`, since `h(T) = 0` (`gv_eq_left`). -/
lemma block_sat {U W Z : Finset V} (hS : Setting G U W Z) {X Y : Finset V}
    (hT : Fam G U W Z 12 2 X Y) {y : V} (hy : y ∈ Y) : dg G X y = 6 := by
  obtain ⟨hX, hY, -, -, hg, hk⟩ := hT
  have h1 := gv_eq_left (G := G) X Y
  have hk' : (#X : ℤ) = #Y + 2 := by exact_mod_cast hk
  have h0 : df G X Y = 0 := by linarith
  exact dg_eq_six_of_df_eq_zero (fun y hy => (dg_mono hX y).trans (hS.degW y (hY hy))) h0 hy

/-- A vertex of the `W`-side of a `W`-small 2-block on `Z` is not a port. -/
lemma six_le_dg_of_block {U W Z : Finset V} (hS : Setting G U W Z) {X Y : Finset V}
    (hT : Fam G U W Z 12 2 X Y) {y : V} (hy : y ∈ Y) : 6 ≤ dg G U y := by
  have h1 := block_sat hS hT hy
  have h2 := dg_mono (G := G) hT.1 y
  omega

variable [DecidableEq V]

/-! ### Petals at a port -/

/-- **Petals at a port.** Let `y` be a port (degree at most five) and `(A, C)` a violated cut of
the balanced pair `(W - y, U)`. Then `D(C) = 0`, so the complement `Q = (U - C, W - A)` contains
`Z`; it contains `y`, it is proper, and it has `g = 12`, `κ = 1` (an α-petal of `y`) or
`g = 14`, `κ = 2` (a β-petal of `y`). In particular, at a port the complement is never a
`W`-small 2-block. The proof combines the exact slack `ec_sdiff_eq`, the cut identity
`gv_sdiff_sdiff` and sparsity; a complement with only two vertices would need a `U`-vertex of
degree four. -/
theorem port_petal {U W Z : Finset V} (hS : Setting G U W Z) {y : V} (hy : y ∈ W)
    (hport : dg G U y ≤ 5) {A C : Finset V} (hA : A ⊆ W.erase y) (hC : C ⊆ U)
    (hviol : ec G A (U \ C) + 4 * #C < 4 * #A) :
    y ∈ W \ A ∧ (Fam G U W Z 12 1 (U \ C) (W \ A) ∨ Fam G U W Z 14 2 (U \ C) (W \ A)) := by
  have hAW : A ⊆ W := hA.trans (erase_subset y W)
  have hyA : y ∉ A := fun h => by simpa using hA h
  have hyWA : y ∈ W \ A := mem_sdiff.2 ⟨hy, hyA⟩
  -- the exact slack: `e(A, U - C) = 6k - D_A + D(C) + e(W - A, C)`
  have hslack := ec_sdiff_eq (G := G) hAW hC
  -- `D_A ≤ D(W - y) = 8 - def(y)`
  have hDA : df G U A ≤ df G U (W.erase y) :=
    df_le_of_subset hA fun z hz => hS.degW z (mem_of_mem_erase hz)
  have hDy : df G U (W.erase y) + (6 - (dg G U y : ℤ)) = df G U W := by
    unfold df
    exact sum_erase_add W _ hy
  have hDW := hS.dfW
  have hDC0 : 0 ≤ df G W C := df_nonneg fun c hc => hS.degU c (hC hc)
  -- sizes
  have hcA : #A ≤ #U := by
    have := card_le_card hA
    rw [card_erase_of_mem hy, hS.cardW] at this
    omega
  have hUC := card_sdiff_add_card_eq_card hC
  have hWA := card_sdiff_add_card_eq_card hAW
  have hWA1 : 1 ≤ #(W \ A) := card_pos.2 ⟨y, hyWA⟩
  have hcW := hS.cardW
  -- the cut identity `gv_sdiff_sdiff`
  have hcut := gv_sdiff_sdiff (G := G) hAW hC
  rw [hS.defU] at hcut
  have hviol' : (ec G A (U \ C) : ℤ) + 4 * #C < 4 * #A := by exact_mod_cast hviol
  -- the complement has at least three vertices: `|Q| = 2` would need a `U`-vertex of degree four
  have h3 : 3 ≤ #(U \ C) + #(W \ A) := by
    by_contra hlt
    have hUC1 : #(U \ C) = 1 := by omega
    have hWA1' : #(W \ A) = 1 := by omega
    have e1 := ec_sdiff_add_right (G := G) hAW (U \ C)
    have e2 := ec_comm (G := G) (U \ C) A
    have e3 := ec_le_card_mul (G := G) (U \ C) (W \ A)
    have e4 : 5 * #(U \ C) ≤ ec G (U \ C) W := by
      unfold ec
      calc 5 * #(U \ C) = ∑ _u ∈ U \ C, 5 := by rw [sum_const, smul_eq_mul, mul_comm]
        _ ≤ ∑ u ∈ U \ C, dg G W u := sum_le_sum fun u hu => hS.five_le_dg (mem_sdiff.1 hu).1
    rw [hUC1, hWA1'] at e3
    rw [hUC1] at e4
    omega
  have hlt : #(U \ C) + #(W \ A) < #U + #W := by omega
  have hg := hS.sparse (U \ C) sdiff_subset (W \ A) sdiff_subset h3 hlt
  have hec0 : (0 : ℤ) ≤ ec G (W \ A) C := by positivity
  have hdy : (dg G U y : ℤ) ≤ 5 := by exact_mod_cast hport
  have hDC : df G W C = 0 := by omega
  have hZ : Z ⊆ U \ C := hS.subset_sdiff_of_df hC hDC
  have hcases : (gv G (U \ C) (W \ A) = 12 ∧ #(U \ C) = #(W \ A) + 1) ∨
      (gv G (U \ C) (W \ A) = 14 ∧ #(U \ C) = #(W \ A) + 2) := by
    omega
  refine ⟨hyWA, ?_⟩
  rcases hcases with ⟨hg12, hk⟩ | ⟨hg14, hk⟩
  · exact Or.inl ⟨sdiff_subset, sdiff_subset, hZ, hlt, hg12, hk⟩
  · exact Or.inr ⟨sdiff_subset, sdiff_subset, hZ, hlt, hg14, hk⟩

/-! ### The lattice lemma -/

/-- **The lattice lemma.** For two members `S = (X, Y)`, `S' = (X', Y')` of the families with
`g(S) + g(S') < 6 (κ(S) + κ(S')) + 16`, the union is proper (otherwise
`κ(S ∩ S') = κ(S) + κ(S') + 1` and `6 κ(S ∩ S') ≤ g(S ∩ S') ≤ g(S) + g(S') - 10`), both the
union and the intersection have `g ≥ 12` (they contain `Z`), and
`g(S ∪ S') + g(S ∩ S') ≤ g(S) + g(S')` (`gv_union_add_gv_inter_le`). -/
theorem lattice {U W Z : Finset V} (hS : Setting G U W Z) {g g' : ℤ} {k k' : ℕ}
    {X Y X' Y' : Finset V} (hF : Fam G U W Z g k X Y) (hF' : Fam G U W Z g' k' X' Y')
    (hκ : g + g' < 6 * ((k : ℤ) + k') + 16) :
    #(X ∪ X') + #(Y ∪ Y') < #U + #W ∧ 12 ≤ gv G (X ∪ X') (Y ∪ Y') ∧
      12 ≤ gv G (X ∩ X') (Y ∩ Y') ∧ gv G (X ∪ X') (Y ∪ Y') + gv G (X ∩ X') (Y ∩ Y') ≤ g + g' := by
  obtain ⟨hX, hY, hZ, hlt, hg, hk⟩ := hF
  obtain ⟨hX', hY', hZ', hlt', hg', hk'⟩ := hF'
  have hsub := gv_union_add_gv_inter_le (G := G) X X' Y Y'
  rw [hg, hg'] at hsub
  have hXu := card_union_add_card_inter X X'
  have hYu := card_union_add_card_inter Y Y'
  have hXU : X ∪ X' ⊆ U := union_subset hX hX'
  have hYW : Y ∪ Y' ⊆ W := union_subset hY hY'
  have hXi : X ∩ X' ⊆ U := inter_subset_left.trans hX
  have hYi : Y ∩ Y' ⊆ W := inter_subset_left.trans hY
  have hκi := hS.six_mul_le_gv hXi hYi
  have hcXU := card_le_card hXU
  have hcYW := card_le_card hYW
  have hlt_u : #(X ∪ X') + #(Y ∪ Y') < #U + #W := by
    by_contra hge
    have hXeq : X ∪ X' = U := eq_of_subset_of_card_le hXU (by omega)
    have hYeq : Y ∪ Y' = W := eq_of_subset_of_card_le hYW (by omega)
    rw [hXeq, hYeq, hS.gv_eq] at hsub
    rw [hXeq] at hXu
    rw [hYeq] at hYu
    have hcW := hS.cardW
    omega
  have hli : #(X ∩ X') + #(Y ∩ Y') < #U + #W := by
    have := card_le_card (inter_subset_left : X ∩ X' ⊆ X)
    have := card_le_card (inter_subset_left : Y ∩ Y' ⊆ Y)
    omega
  have hgu := hS.twelve_le_gv hXU hYW (hZ.trans subset_union_left) hlt_u
  have hgi := hS.twelve_le_gv hXi hYi (subset_inter hZ hZ') hli
  exact ⟨hlt_u, hgu, hgi, hsub⟩

/-! ### The boundary of a `W`-small 2-block, and the parts -/

/-- **The boundary of a `W`-small 2-block.** Exactly ten edges leave a `W`-small 2-block
`T = (X, Y)` containing `Z`, all from `X` to `W - Y`: the deficiency of `X` inside `T` is
`h(T) + 6 κ(T) = 12`, it is `D(X) + e(X, W - Y)` (`df_eq_df_add_ec`), and `D(X) = D_U = 2`
(`C2P.Setting.df_of_subset`). -/
lemma block_boundary {U W Z : Finset V} (hS : Setting G U W Z) {X Y : Finset V}
    (hT : Fam G U W Z 12 2 X Y) : ec G (W \ Y) X = 10 := by
  obtain ⟨hX, hY, hZX, -, hg, hk⟩ := hT
  have h1 := gv_eq_right (G := G) X Y
  have h2 := df_eq_df_add_ec (G := G) hY X
  have h3 := hS.df_of_subset hX hZX
  have h4 := ec_comm (G := G) X (W \ Y)
  have hk' : (#X : ℤ) = #Y + 2 := by exact_mod_cast hk
  have h5 : (ec G X (W \ Y) : ℤ) = 10 := by linarith
  omega

/-- **One inequality per part.** Let `T = (XT, YT)` be a `W`-small 2-block containing `Z` and
`R = (X, Y) ⊇ T` (`XT ⊆ X`, `YT ⊆ Y`) a member of `Fam 12 1` or `Fam 14 2`. Then
`3 D(Y - YT) ≤ 2 c(R)`, where `c(R) = e(Y - YT, XT)` counts the boundary edges of `T` that end in
`R`. Proof: splitting `R` into `T` and `R - T` gives `g(R - T) = g(R) - 12 + 2 c(R)`, since `YT`
has no neighbor outside `XT`. For `κ(R) = 1`: `D(Y) ≤ h(R) = 3`, and `R - T` is one `W`-vertex
(`c = 3`, and `D ≤ 2` since every vertex of `W` has degree at least four) or has at least three
vertices (`c ≥ 6`). For `κ(R) = 2`, `g(R) = 14`: `D(Y) ≤ h(R) = 1`, and `R - T` has `κ = 0` and
`g = 2 + 2 c(R) ≥ 10`. -/
theorem part_bound {U W Z : Finset V} (hS : Setting G U W Z) {XT YT X Y : Finset V}
    (hT : Fam G U W Z 12 2 XT YT)
    (hR : Fam G U W Z 12 1 X Y ∨ Fam G U W Z 14 2 X Y) (hTX : XT ⊆ X) (hTY : YT ⊆ Y) :
    3 * df G U (Y \ YT) ≤ 2 * (ec G (Y \ YT) XT : ℤ) := by
  have hsat : ∀ y ∈ YT, dg G XT y = 6 := fun y hy => block_sat hS hT hy
  obtain ⟨hXT, hYT, -, -, hgT, hkT⟩ := hT
  have hXY : X ⊆ U ∧ Y ⊆ W ∧ #X + #Y < #U + #W := by
    rcases hR with ⟨hX, hY, -, hlt, -⟩ | ⟨hX, hY, -, hlt, -⟩ <;> exact ⟨hX, hY, hlt⟩
  obtain ⟨hX, hY, hlt⟩ := hXY
  -- `YT` has no neighbor in `X - XT`
  have hzero : ec G (X \ XT) YT = 0 := by
    rw [ec_comm]
    refine sum_eq_zero fun y hy => ?_
    have h1 := dg_sdiff_add (G := G) hTX y
    have h2 := dg_mono (G := G) hX y
    have h3 := hS.degW y (hYT hy)
    have h4 := hsat y hy
    omega
  -- the decomposition `g(R) = g(T) + g(R - T) - 2 c(R)`
  have hdec : gv G X Y = gv G XT YT + gv G (X \ XT) (Y \ YT) - 2 * (ec G (Y \ YT) XT : ℤ) := by
    have e1 := ec_sdiff_add_left (G := G) hTX Y
    have e2 := ec_sdiff_add_right (G := G) hTY XT
    have e3 := ec_sdiff_add_right (G := G) hTY (X \ XT)
    have e4 := ec_comm (G := G) XT (Y \ YT)
    have c1 := card_sdiff_add_card_eq_card hTX
    have c2 := card_sdiff_add_card_eq_card hTY
    unfold gv
    omega
  rw [hgT] at hdec
  -- `D(Y - YT) ≤ D(Y) ≤ h(R)`
  have hD1 : df G U (Y \ YT) ≤ df G U Y :=
    df_le_of_subset sdiff_subset fun y hy => hS.degW y (hY hy)
  have hD2 : df G U Y ≤ df G X Y := df_anti hX
  have hh := gv_eq_left (G := G) X Y
  have hc0 : (0 : ℤ) ≤ ec G (Y \ YT) XT := by positivity
  have c1 := card_sdiff_add_card_eq_card hTX
  have c2 := card_sdiff_add_card_eq_card hTY
  have hX' : X \ XT ⊆ U := sdiff_subset.trans hX
  have hY' : Y \ YT ⊆ W := sdiff_subset.trans hY
  have hlt' : #(X \ XT) + #(Y \ YT) < #U + #W := by omega
  rcases hR with ⟨-, -, -, -, hg, hk⟩ | ⟨-, -, -, -, hg, hk⟩
  · -- `κ(R) = 1`: `h(R) = 3`, and `R - T` has `κ = -1`
    have hk' : (#X : ℤ) = #Y + 1 := by exact_mod_cast hk
    by_cases h3 : 3 ≤ #(X \ XT) + #(Y \ YT)
    · have := hS.sparse (X \ XT) hX' (Y \ YT) hY' h3 hlt'
      linarith
    · -- `R - T` is a single `W`-vertex `y0`, with `c(R) = 3` and `def(y0) ≤ 2`
      have hX0 : X \ XT = ∅ := card_eq_zero.1 (by omega)
      have hY1 : #(Y \ YT) = 1 := by omega
      obtain ⟨y0, hy0⟩ := card_eq_one.1 hY1
      have hg0 : gv G (X \ XT) (Y \ YT) = 6 := by
        rw [hX0, hy0]
        simp [gv, ec]
      have hdf : df G U (Y \ YT) = 6 - (dg G U y0 : ℤ) := by
        rw [hy0]
        simp [df]
      have h4 := hS.four_le_dg (hY' (by rw [hy0]; exact mem_singleton_self y0))
      have h4' : (4 : ℤ) ≤ dg G U y0 := by exact_mod_cast h4
      linarith
  · -- `κ(R) = 2`, `g(R) = 14`: `h(R) = 1`, and `R - T` has `κ = 0`
    have hk' : (#X : ℤ) = #Y + 2 := by exact_mod_cast hk
    by_cases h2 : 2 ≤ #(X \ XT) + #(Y \ YT)
    · have := hS.ten_le_gv hX' hY' h2 hlt'
      linarith
    · have hX0 : X \ XT = ∅ := card_eq_zero.1 (by omega)
      have hY0 : Y \ YT = ∅ := card_eq_zero.1 (by omega)
      have hg0 : gv G (X \ XT) (Y \ YT) = 0 := by
        rw [hX0, hY0]
        simp [gv, ec]
      linarith

/-! ### The budget -/

/-- **The budget count.** The vertices `y ∈ P` (the ports, in `C2TwoBlock.lean`) get parts
`f y ∋ y` inside `B`; two parts are equal or disjoint; `d, ω ≥ 0` on `B`; each part satisfies
`3 Σ_{f y} d ≤ 2 Σ_{f y} ω`. Then `3 Σ_P d ≤ 2 Σ_B ω`. The proof removes the part of one port
and recurses. -/
theorem budget {P B : Finset V} (f : V → Finset V) (d ω : V → ℤ)
    (hd : ∀ z ∈ B, 0 ≤ d z) (hω : ∀ z ∈ B, 0 ≤ ω z) (h1 : ∀ y ∈ P, y ∈ f y)
    (h2 : ∀ y ∈ P, ∀ y' ∈ P, f y = f y' ∨ Disjoint (f y) (f y'))
    (h3 : ∀ y ∈ P, f y ⊆ B) (h4 : ∀ y ∈ P, 3 * ∑ z ∈ f y, d z ≤ 2 * ∑ z ∈ f y, ω z) :
    3 * ∑ z ∈ P, d z ≤ 2 * ∑ z ∈ B, ω z := by
  induction P using Finset.strongInduction generalizing B with
  | H P ih =>
    rcases P.eq_empty_or_nonempty with rfl | ⟨y, hy⟩
    · simp only [sum_empty, mul_zero]
      have := sum_nonneg hω
      linarith
    · have hSB : f y ⊆ B := h3 y hy
      have hP' : P.filter (· ∉ f y) ⊂ P :=
        filter_ssubset.2 ⟨y, hy, not_not.2 (h1 y hy)⟩
      have hsub : ∀ z ∈ P.filter (· ∉ f y), f z ⊆ B \ f y := by
        intro z hz
        obtain ⟨hzP, hzS⟩ := mem_filter.1 hz
        rcases h2 z hzP y hy with heq | hdis
        · exact absurd (heq ▸ h1 z hzP) hzS
        · exact subset_sdiff.2 ⟨h3 z hzP, hdis⟩
      have ih' := ih (P.filter (· ∉ f y)) hP' (B := B \ f y)
        (fun z hz => hd z (sdiff_subset hz)) (fun z hz => hω z (sdiff_subset hz))
        (fun z hz => h1 z (mem_filter.1 hz).1)
        (fun z hz z' hz' => h2 z (mem_filter.1 hz).1 z' (mem_filter.1 hz').1)
        hsub (fun z hz => h4 z (mem_filter.1 hz).1)
      have hsplitP := sum_filter_add_sum_filter_not P (· ∈ f y) d
      have hsplitB := sum_sdiff hSB (f := ω)
      have hin : ∑ z ∈ P.filter (· ∈ f y), d z ≤ ∑ z ∈ f y, d z :=
        sum_le_sum_of_subset_of_nonneg (fun z hz => (mem_filter.1 hz).2)
          fun z hz _ => hd z (hSB hz)
      have hy4 := h4 y hy
      linarith

end C2P

end Erdos585.QB5
