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
import Openmath.Proofs.QB4.Defs

/-!
# QB(4): the sparse core of the C1 argument

This file proves the core of the induction for C1 instances (`IsC1` in `Reductions.lean`), with
sparsity as a hypothesis. The setting is a pair `(U, W)` with `|W| = |U| + 1`, every degree at
most six and `D_U ≤ 1`, which is *sparse*: every proper pair `(X, Y)` with `X ⊆ U`, `Y ⊆ W` and at
least two vertices has `g(X, Y) ≥ 10`. If every port `y` (a vertex of `W` of degree at most five)
carries a violated cut `(A, C)` of the balanced pair `(W - y, U)`, there is a contradiction
(`sparse_core`). For a pair `(X, Y)` write `κ = |X| - |Y|`; when `D_U = 1`, `u1` is the vertex of
`U` of degree five.

* `petal_of_violation` (the petal lemma): a violation at a port forces `D_U = 1` and `D(C) = 0`,
  and the complement pair has `g = 10` and `κ = 1`.
* `IsPetal` is the family `𝒫` of petals. `IsPetal.df_le_two` bounds the `W`-deficiency of a
  petal, `IsPetal.three_le_dg` gives `u1` three neighbors in it, and `IsPetal.union` shows that
  the union of two petals is a petal.
* `sparse_core` is the final count: the union of the petals of all ports is a petal, so it
  carries `W`-deficiency at most two, while the ports carry seven.

Sparsity and the violations are hypotheses here. They come from `sparse_of_minimal`
(`Reductions.lean`) and `hviol_of_not_quartic` (`FourFactor.lean`).
-/

open Finset

namespace Erdos585.QB4

variable {V : Type*} {G : SimpleGraph V} [DecidableRel G.Adj]

variable (G) in
/-- Sparsity of a pair `(U, W)`: every proper sub-pair with at least two vertices has `g ≥ 10`. -/
def Sparse (U W : Finset V) : Prop :=
  ∀ X ⊆ U, ∀ Y ⊆ W, 2 ≤ #X + #Y → #X + #Y < #U + #W → 10 ≤ gv G X Y

variable (G) in
/-- The family `𝒫` of petals: proper sub-pairs with at least two vertices, `g = 10`,
`κ = |X| - |Y| = 1`, containing the vertex `u1`. -/
def IsPetal (U W : Finset V) (u1 : V) (X Y : Finset V) : Prop :=
  X ⊆ U ∧ Y ⊆ W ∧ 2 ≤ #X + #Y ∧ #X + #Y < #U + #W ∧ gv G X Y = 10 ∧ #X = #Y + 1 ∧ u1 ∈ X

/-- Basic count: `D_W = 6 + D_U` when `|W| = |U| + 1`. -/
lemma df_right_eq {U W : Finset V} (hW : #W = #U + 1) : df G U W = 6 + df G W U := by
  rw [df_eq, df_eq, ec_comm W U, hW]
  push_cast
  ring

/-- Basic count: `g(U, W) = 6 + 2 D_U` when `|W| = |U| + 1`. -/
lemma gv_full {U W : Finset V} (hW : #W = #U + 1) : gv G U W = 6 + 2 * df G W U := by
  rw [gv_eq_right, hW]
  push_cast
  ring

/-- If `D_Z > 0` and degrees are at most six, some vertex of `Z` has degree at most five. -/
lemma exists_dg_le_five {S Z : Finset V} (h : ∀ z ∈ Z, dg G S z ≤ 6) (hpos : 0 < df G S Z) :
    ∃ z ∈ Z, dg G S z ≤ 5 := by
  by_contra! hc
  have h0 : df G S Z = 0 := sum_eq_zero fun z hz => by
    have h1 := h z hz
    have h2 := hc z hz
    have h3 : dg G S z = 6 := by omega
    rw [h3]
    norm_num
  omega

/-- **The petal lemma**, with sparsity as a hypothesis. A violated cut `(A, C)` of the
balanced pair `(W - y, U)` at a port `y` forces `D_U = 1` and `D(C) = 0`, and its complement
`(U - C, W - A)` is a proper pair with `g = 10`, `κ = 1`, at least two vertices and `y ∈ W - A`. -/
lemma petal_of_violation [DecidableEq V] {U W : Finset V} (hW : #W = #U + 1)
    (hdU : ∀ u ∈ U, dg G W u ≤ 6) (hdW : ∀ w ∈ W, dg G U w ≤ 6) (hDU : df G W U ≤ 1)
    (hsp : Sparse G U W) {y : V} (hy : y ∈ W) (hport : dg G U y ≤ 5)
    {A C : Finset V} (hA : A ⊆ W.erase y) (hC : C ⊆ U)
    (hviol : ec G A (U \ C) + 4 * #C < 4 * #A) :
    df G W U = 1 ∧ df G W C = 0 ∧ gv G (U \ C) (W \ A) = 10 ∧ #(U \ C) = #(W \ A) + 1 ∧
      2 ≤ #(U \ C) + #(W \ A) ∧ #(U \ C) + #(W \ A) < #U + #W ∧ y ∈ W \ A := by
  have hAW : A ⊆ W := hA.trans (erase_subset y W)
  have hyA : y ∉ A := fun h => by simpa using hA h
  -- the slack bound: `e(A, U - C) ≥ 6k - D_A`
  have hslack := six_mul_sub_le_ec_sdiff (G := G) hAW hC fun c hc => hdU c (hC hc)
  -- `D_A + def(y) ≤ D_W = 6 + D_U`
  have hDA : df G U A ≤ df G U (W.erase y) :=
    df_le_of_subset hA fun z hz => hdW z (mem_of_mem_erase hz)
  have hDy : df G U (W.erase y) + (6 - (dg G U y : ℤ)) = df G U W := by
    unfold df
    exact sum_erase_add W _ hy
  have hDW := df_right_eq (G := G) hW
  have hDU0 : 0 ≤ df G W U := df_nonneg hdU
  have hDC0 : 0 ≤ df G W C := df_nonneg fun c hc => hdU c (hC hc)
  -- sizes
  have hcardA : #A ≤ #U := by
    have := card_le_card hA
    rw [card_erase_of_mem hy] at this
    omega
  have hcC : #C ≤ #U := card_le_card hC
  have hUC := card_sdiff_add_card_eq_card hC
  have hWA := card_sdiff_add_card_eq_card hAW
  have hyWA : y ∈ W \ A := mem_sdiff.2 ⟨hy, hyA⟩
  have hWA1 : 1 ≤ #(W \ A) := card_pos.2 ⟨y, hyWA⟩
  -- `k ≥ 1` and `k ≤ 2`
  have hport' : (dg G U y : ℤ) ≤ 5 := by exact_mod_cast hport
  have hviol' : (ec G A (U \ C) : ℤ) + 4 * #C < 4 * #A := by exact_mod_cast hviol
  have hk1 : #C + 1 ≤ #A := by omega
  have hk2 : (#A : ℤ) ≤ #C + 2 := by linarith
  -- the complement is a proper pair with at least two vertices
  have hUC1 : 1 ≤ #(U \ C) := by omega
  have hsize : 2 ≤ #(U \ C) + #(W \ A) := by omega
  have hprop : #(U \ C) + #(W \ A) < #U + #W := by omega
  have hg := hsp (U \ C) sdiff_subset (W \ A) sdiff_subset hsize hprop
  -- the cut identity (`gv_sdiff_sdiff`)
  have hcut := gv_sdiff_sdiff (G := G) hAW hC
  rw [hW] at hcut
  push_cast at hcut
  have hk : (#A : ℤ) = #C + 2 := by linarith
  have hD1 : df G W U = 1 := by linarith
  have hDC : df G W C = 0 := by linarith
  refine ⟨hD1, hDC, by linarith, by omega, hsize, hprop, hyWA⟩

namespace IsPetal

variable {U W : Finset V} {u1 : V} {X Y : Finset V}

lemma card_right_pos (hP : IsPetal G U W u1 X Y) : 1 ≤ #Y := by
  obtain ⟨-, -, h2, -, -, hk, -⟩ := hP
  omega

/-- A petal has in-petal `W`-deficiency two, so `W`-deficiency at most two. -/
lemma df_le_two (hP : IsPetal G U W u1 X Y) : df G U Y ≤ 2 := by
  obtain ⟨hX, hY, -, -, hg, hk, -⟩ := hP
  have h1 := gv_eq_left (G := G) X Y
  have h2 : df G U Y ≤ df G X Y := df_anti hX
  have hk' : (#X : ℤ) = #Y + 1 := by exact_mod_cast hk
  linarith

/-- `u1` has at least three neighbors in every petal. -/
lemma three_le_dg [DecidableEq V] (hsp : Sparse G U W) (hP : IsPetal G U W u1 X Y) : 3 ≤ dg G Y u1 := by
  have hY1 := hP.card_right_pos
  obtain ⟨hX, hY, h2, hlt, hg, hk, hu⟩ := hP
  have hcard := card_erase_add_one hu
  have hg' := hsp (X.erase u1) ((erase_subset u1 X).trans hX) Y hY (by omega) (by omega)
  rw [gv_erase_left hu, hg] at hg'
  omega

/-- **The lattice lemma**: the union of two petals is a petal. The proof goes through the
intersection, which has at least two vertices because `u1` has degree five and at least three
neighbors in each petal. -/
lemma union [DecidableEq V] (hW : #W = #U + 1) (hdW : ∀ w ∈ W, dg G U w ≤ 6) (hDU : df G W U = 1)
    (hu1 : dg G W u1 = 5) (hsp : Sparse G U W) {X' Y' : Finset V}
    (hP : IsPetal G U W u1 X Y) (hP' : IsPetal G U W u1 X' Y') :
    IsPetal G U W u1 (X ∪ X') (Y ∪ Y') := by
  have h3 := hP.three_le_dg hsp
  have h3' := hP'.three_le_dg hsp
  obtain ⟨hX, hY, h2, hlt, hg, hk, hu⟩ := hP
  obtain ⟨hX', hY', h2', hlt', hg', hk', hu'⟩ := hP'
  have hXu := card_union_add_card_inter X X'
  have hYu := card_union_add_card_inter Y Y'
  have hXU : X ∪ X' ⊆ U := union_subset hX hX'
  have hYW : Y ∪ Y' ⊆ W := union_subset hY hY'
  have hcXU := card_le_card hXU
  have hcYW := card_le_card hYW
  -- (a) the intersection has at least two vertices
  have hYi : 1 ≤ #(Y ∩ Y') := by
    have h1 := dg_union_add_dg_inter (G := G) Y Y' u1
    have h2 := dg_mono (G := G) hYW u1
    have h3 := dg_le_card (G := G) (Y ∩ Y') u1
    omega
  have hXi : 1 ≤ #(X ∩ X') := card_pos.2 ⟨u1, mem_inter.2 ⟨hu, hu'⟩⟩
  -- submodularity, and `g(U, W) = 8`
  have hsub := gv_union_add_gv_inter_le (G := G) X X' Y Y'
  have hfull := gv_full (G := G) hW
  rw [hDU] at hfull
  -- (b) the union is proper
  have hlt_u : #(X ∪ X') + #(Y ∪ Y') < #U + #W := by
    by_contra hge
    have hXeq : X ∪ X' = U := eq_of_subset_of_card_le hXU (by omega)
    have hYeq : Y ∪ Y' = W := eq_of_subset_of_card_le hYW (by omega)
    rw [hXeq, hYeq, hfull] at hsub
    have hdf : 0 ≤ df G (X ∩ X') (Y ∩ Y') :=
      df_nonneg fun y hy =>
        (dg_mono (G := G) (inter_subset_left.trans hX) y).trans
          (hdW y (hY (inter_subset_left hy)))
    have hgi := gv_eq_left (G := G) (X ∩ X') (Y ∩ Y')
    rw [hXeq] at hXu
    rw [hYeq] at hYu
    have hXu' : (#U : ℤ) + #(X ∩ X') = #X + #X' := by exact_mod_cast hXu
    have hYu' : (#W : ℤ) + #(Y ∩ Y') = #Y + #Y' := by exact_mod_cast hYu
    have hW' : (#W : ℤ) = #U + 1 := by exact_mod_cast hW
    have hk1 : (#X : ℤ) = #Y + 1 := by exact_mod_cast hk
    have hk2 : (#X' : ℤ) = #Y' + 1 := by exact_mod_cast hk'
    linarith
  -- (c) both sides of the submodular inequality are at least 10, so both are 10
  have hgi := hsp (X ∩ X') (inter_subset_left.trans hX) (Y ∩ Y') (inter_subset_left.trans hY)
    (by omega) (by
      have := card_le_card (inter_subset_left : X ∩ X' ⊆ X)
      have := card_le_card (inter_subset_left : Y ∩ Y' ⊆ Y)
      omega)
  have hXs := card_le_card (subset_union_left : X ⊆ X ∪ X')
  have hYs := card_le_card (subset_union_left : Y ⊆ Y ∪ Y')
  have hgu := hsp (X ∪ X') hXU (Y ∪ Y') hYW (by omega) hlt_u
  have hgu10 : gv G (X ∪ X') (Y ∪ Y') = 10 := by linarith
  have hgi10 : gv G (X ∩ X') (Y ∩ Y') = 10 := by linarith
  -- a pair with `g = 10` has `κ ≤ 1`
  have hκi : (#(X ∩ X') : ℤ) ≤ #(Y ∩ Y') + 1 := by
    have h1 := gv_eq_left (G := G) (X ∩ X') (Y ∩ Y')
    have h2 : 0 ≤ df G (X ∩ X') (Y ∩ Y') :=
      df_nonneg fun y hy =>
        (dg_mono (G := G) (inter_subset_left.trans hX) y).trans
          (hdW y (hY (inter_subset_left hy)))
    linarith
  have hκu : (#(X ∪ X') : ℤ) ≤ #(Y ∪ Y') + 1 := by
    have h1 := gv_eq_left (G := G) (X ∪ X') (Y ∪ Y')
    have h2 : 0 ≤ df G (X ∪ X') (Y ∪ Y') :=
      df_nonneg fun y hy => (dg_mono (G := G) hXU y).trans (hdW y (hYW hy))
    linarith
  refine ⟨hXU, hYW, by omega, hlt_u, hgu10, by omega, mem_union_left _ hu⟩

end IsPetal

/-- **The sparse core.** A sparse pair
`(U, W)` with `|W| = |U| + 1`, degrees at most six and `D_U ≤ 1` cannot have a violated cut of
`(W - y, U)` at every port `y`. -/
theorem sparse_core [DecidableEq V] {U W : Finset V} (hW : #W = #U + 1)
    (hdU : ∀ u ∈ U, dg G W u ≤ 6) (hdW : ∀ w ∈ W, dg G U w ≤ 6) (hDU : df G W U ≤ 1)
    (hsp : Sparse G U W)
    (hviol : ∀ y ∈ W, dg G U y ≤ 5 →
      ∃ A ⊆ W.erase y, ∃ C ⊆ U, ec G A (U \ C) + 4 * #C < 4 * #A) : False := by
  have hDW := df_right_eq (G := G) hW
  have hDU0 : 0 ≤ df G W U := df_nonneg hdU
  -- a port exists, and its violation forces `D_U = 1`
  obtain ⟨y0, hy0, hport0⟩ := exists_dg_le_five hdW (by linarith)
  obtain ⟨A0, hA0, C0, hC0, hv0⟩ := hviol y0 hy0 hport0
  have hD1 := (petal_of_violation hW hdU hdW hDU hsp hy0 hport0 hA0 hC0 hv0).1
  -- the vertex `u1` of degree five
  obtain ⟨u1, hu1U, hu1le⟩ := exists_dg_le_five hdU (by linarith)
  have hu1 : dg G W u1 = 5 := by
    have h := single_le_sum (f := fun u => 6 - (dg G W u : ℤ))
      (fun u hu => by have := hdU u hu; omega) hu1U
    change 6 - (dg G W u1 : ℤ) ≤ df G W U at h
    omega
  -- every port lies in a petal
  have hpetal : ∀ y ∈ W, dg G U y ≤ 5 → ∃ X Y, IsPetal G U W u1 X Y ∧ y ∈ Y := by
    intro y hy hport
    obtain ⟨A, hA, C, hC, hv⟩ := hviol y hy hport
    obtain ⟨-, hDC, hg, hk, h2, hlt, hyY⟩ :=
      petal_of_violation hW hdU hdW hDU hsp hy hport hA hC hv
    have hu1C : u1 ∉ C := fun h => by
      have := dg_eq_six_of_df_eq_zero (fun c hc => hdU c (hC hc)) hDC h
      omega
    exact ⟨U \ C, W \ A, ⟨sdiff_subset, sdiff_subset, h2, hlt, hg, hk,
      mem_sdiff.2 ⟨hu1U, hu1C⟩⟩, hyY⟩
  -- the union of the petals of all ports is a petal
  set ports := W.filter fun w => dg G U w ≤ 5 with hports
  have hunion : ∀ T ⊆ ports, T.Nonempty → ∃ X Y, IsPetal G U W u1 X Y ∧ T ⊆ Y := by
    intro T
    induction T using Finset.induction_on with
    | empty => intro _ h; exact absurd h (by simp)
    | insert a T haT ih =>
      intro hT _
      have ha := hT (mem_insert_self a T)
      rw [hports, mem_filter] at ha
      obtain ⟨Xa, Ya, hPa, hya⟩ := hpetal a ha.1 ha.2
      rcases T.eq_empty_or_nonempty with hTe | hTne
      · exact ⟨Xa, Ya, hPa, by simp [hTe, hya]⟩
      · obtain ⟨X, Y, hP, hTY⟩ := ih ((subset_insert a T).trans hT) hTne
        refine ⟨X ∪ Xa, Y ∪ Ya, hP.union hW hdW hD1 hu1 hsp hPa, ?_⟩
        exact insert_subset (mem_union_right _ hya) (hTY.trans subset_union_left)
  obtain ⟨X, Y, hP, hpY⟩ := hunion ports Subset.rfl ⟨y0, by rw [hports, mem_filter]; exact ⟨hy0, hport0⟩⟩
  -- the petal carries all of `D_W = 7`, but at most two
  have hYW : Y ⊆ W := hP.2.1
  have hrest : df G U (W \ Y) = 0 := sum_eq_zero fun w hw => by
    have hwW := (mem_sdiff.1 hw).1
    have hwY := (mem_sdiff.1 hw).2
    have h6 : ¬ dg G U w ≤ 5 := fun h => hwY (hpY (by rw [hports, mem_filter]; exact ⟨hwW, h⟩))
    have := hdW w hwW
    have h7 : dg G U w = 6 := by omega
    rw [h7]
    norm_num
  have hsplit := df_sdiff_add (G := G) (S := U) hYW
  have h2 := hP.df_le_two
  linarith

end Erdos585.QB4
