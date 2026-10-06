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
import Openmath.Proofs.QB4.Statement

/-!
# QB(5): shared definitions and counting lemmas

QB(5) is this project's label for the statement of `Erdos585.qb5` (`Statement.lean`), and QB(4)
the label for `Erdos585.qb4`. The proof of QB(5) runs in the pair setting of the proof of QB(4):
one ambient graph `G`, pairs `(X, Y)` of finite vertex sets, and only the adjacencies between the
two sets of a pair are counted. QB4 means the namespace `Erdos585.QB4` of that proof, whose
`Defs.lean` fixes the notation: `dg G S v` is the number of neighbors of `v` in `S`, written
`e(v, S)`, or `deg v` when `S` is the other side of the pair; `ec G X Y = e(X, Y)`;
`gv G X Y = g(X, Y) = 6 (|X| + |Y|) - 2 e(X, Y)`; and `df G S Z = D(Z) = Σ_{z ∈ Z} (6 - dg G S z)`
is the deficiency of `Z`, with degrees taken into `S`. A sub-pair of `(U, W)` is a pair `(X, Y)`
with `X ⊆ U` and `Y ⊆ W`; it is proper if `|X| + |Y| < |U| + |W|`.

This file holds the instance classes, sparsity, blocks, the demand and rigid sets, which several
QB5 files use, and the counting lemmas. The labels below are used across the QB5 files.

* Quartic subgraph: QB4's `Quartic`, a nonempty set of adjacent pairs in `U × W` in which every
  vertex is the first entry of 0 or 4 pairs and the second entry of 0 or 4 pairs. A 4-factor of
  `(P, Q)` is a set of adjacent pairs of `P × Q` in which every vertex of `P` and of `Q` is an
  entry of exactly four pairs. For `|P| = |Q|`, QB4's 4-factor criterion `exists_four_factor`
  gives one when the cut condition `4 |A| ≤ e(A, Q - C) + 4 |C|` holds for all `A ⊆ P` and
  `C ⊆ Q`; a pair `(A, C)` at which it fails is a violated cut.
* C1, E4, C2, E5: the instance classes QB4's `IsC1` and `IsE4`, and `IsC2` and `IsE5` below. C1:
  sides of sizes `s ≥ 1` and `s + 1`, every degree at most six, deficiency at most one on the
  smaller side. C2: the same with deficiency exactly two. E4: both sides of size `a ≥ 1`, every
  degree at most six, deficiency at most four on each side. E5: both sides of size `a ≥ 2`, every
  degree at most six, deficiency exactly five on each side. A port of a C2 instance `(U, W)` is a
  vertex `y ∈ W` with `dg G U y ≤ 5`.
* Sparse: `Sparse5`, `g ≥ 12` on every proper sub-pair with at least three vertices.
* 2-block, or block: a pair `(A, C)` with `IsBlock G A C`, with big side `A` and small side `C`.
  The in-block degree of `v ∈ A` is `d_v = dg G C v`, and `δ_v = 6 - d_v`. The in-degree-3
  vertices are those with `d_v = 3`; they form the set `L_A`.
* Cut edges: by `e5_blocks` (`PairCriterion.lean`), a violated cut `(A, C)` of a sparse E5
  instance `(P, Q)` splits it into the blocks `(A, C)` and `(Q - C, P - A)`, joined by exactly
  seven edges, all between `A` and `Q - C`. These seven are the cut edges.
* Supply and demand: a supply is a function `m : V → ℕ` on the big side `A` of a block; in the
  proof, `m(v)` is the number of edges at `v` of a chosen set `M` of four edges that leave the block
  (four cut edges in `E5.lean`, the four edges at a vertex `u0` in `C2Hub.lean`). Write
  `m(S) = Σ_{v ∈ S} m(v)`. The demand `dem G C A1` is defined below. A set `A1 ⊆ A` is
  under-supplied (by `m`, or by `M`) if `m(A1) < dem(A1)`. A set `T ⊆ A` is overloaded if
  `θ*(T) ≥ 1`, with `θ*` (`thetaStar`) as in `Block.lean`; when `m(A) = 4`, `T` is overloaded if and
  only if `A - T` is under-supplied (`overloaded_iff`). The weight of `v ∈ A` is
  `w(v) = δ_v - m(v)`, and `w(S)` is its sum over `S`. `M` covers `L_A` if every vertex of `L_A` is
  an end of an edge of `M`; in a block this is `d_v + m(v) ≥ 4` for every `v ∈ A`, that is `w ≤ 2`
  on `A`.
* Rigid set and `GoodSide`: defined below, for one side of a cut of seven edges.
* KL1: this project's label for the statement of `kl1` (`KL1.lean`): in a block `(A, C)` with a
  supply `m` such that `m(A) = 4` and `4 ≤ d_v + m(v) ≤ 6` for every `v ∈ A`, some `p ∈ A` has no
  under-supplied subset of `A - p`.

Lemmas:

* `g` of a union and an intersection, with the crossing term (`gv_union_add_gv_inter`); deleting
  or adding a vertex (`gv_erase_left` of QB4, `gv_erase_right`, `gv_insert_left`,
  `gv_insert_right`); the deficiency inside a sub-pair (`df_eq_df_add_ec`); and the exact slack of
  a cut (`ec_sdiff_eq`).
* The sizes `s ≥ 5` and `a ≥ 5` of C2 and E5 instances (`IsC2.five_le`, `IsE5.five_le`), minimum
  degree four in a sparse pair with `g ≤ 10` and at least four vertices
  (`four_le_dg_of_sparse5_left`, `four_le_dg_of_sparse5_right`), the case split
  (`small_gv_cases5`), sparsity of a minimal counterexample (`sparse5_of_minimal`) and the
  violated cuts of a pair with no quartic subgraph (`exists_violation_of_not_quartic`,
  `exists_violation_erase_of_not_quartic`).
-/

open Finset

namespace Erdos585.QB5

open QB4

variable {V : Type*} {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ### The instance classes and sparsity -/

variable (G) in
/-- Sparsity of a pair for QB(5): every proper sub-pair `(X, Y)` (`X ⊆ U`, `Y ⊆ W` and
`|X| + |Y| < |U| + |W|`) with at least three vertices has `g(X, Y) ≥ 12`. -/
def Sparse5 (U W : Finset V) : Prop :=
  ∀ X ⊆ U, ∀ Y ⊆ W, 3 ≤ #X + #Y → #X + #Y < #U + #W → 12 ≤ gv G X Y

variable (G) in
/-- A C2 instance of size `s`: sides `U` (size `s ≥ 1`) and `W` (size `s + 1`), every degree at
most six, and deficiency exactly two on the smaller side. -/
structure IsC2 (U W : Finset V) (s : ℕ) : Prop where
  pos : 1 ≤ s
  cardU : #U = s
  cardW : #W = s + 1
  degU : ∀ u ∈ U, dg G W u ≤ 6
  degW : ∀ w ∈ W, dg G U w ≤ 6
  defU : df G W U = 2

variable (G) in
/-- An E5 instance of size `a`: both sides of size `a ≥ 2` (for equal sides, `n ≥ 3` means
`a ≥ 2`), every degree at most six, and deficiency exactly five on each side. -/
structure IsE5 (P Q : Finset V) (a : ℕ) : Prop where
  pos : 2 ≤ a
  cardP : #P = a
  cardQ : #Q = a
  degP : ∀ p ∈ P, dg G Q p ≤ 6
  degQ : ∀ q ∈ Q, dg G P q ≤ 6
  defP : df G Q P = 5
  defQ : df G P Q = 5

/-! ### Blocks, demand, rigid sets -/

variable (G) in
/-- A 2-block `X = (A, C)`, with big side `A` and small side `C`: `|A| = |C| + 2 ≥ 6`, every
`c ∈ C` has six neighbors in `A`, `g ≥ 12` on every sub-pair with at least three vertices, and
in-block degrees `3 ≤ d_a ≤ 6` on `A`, where `d_a = dg G C a`. -/
structure IsBlock (A C : Finset V) : Prop where
  card : #A = #C + 2
  six_le : 6 ≤ #A
  satC : ∀ c ∈ C, dg G A c = 6
  sparse : ∀ S ⊆ A, ∀ T ⊆ C, 3 ≤ #S + #T → 12 ≤ gv G S T
  three_le : ∀ a ∈ A, 3 ≤ dg G C a
  le_six : ∀ a ∈ A, dg G C a ≤ 6

variable (G) in
/-- The demand of `A1` in a block with small side `C`:
`dem(A1) = 4 |A1| - Σ_{c ∈ C} min(4, e(c, A1))`. -/
def dem (C A1 : Finset V) : ℤ := 4 * #A1 - ∑ c ∈ C, (min 4 (dg G A1 c) : ℤ)

/-- A rigid set for `M` on one side of a cut of seven edges: a set `K` whose members in `L` have
three cut edges, such that every cut edge at a vertex of `K` lies in `M` and exactly three or four
cut edges are at vertices of `K` (`GoodSide` applies it to sets of ends of `M`). The edges are
`Fin 7`, and `r i` is the end of edge `i` on this side. -/
def IsRigid {α : Type*} [DecidableEq α] (r : Fin 7 → α) (L : Finset α) (M : Finset (Fin 7))
    (K : Finset α) : Prop :=
  (∀ v ∈ K, v ∈ L → #{j | r j = v} = 3) ∧ (∀ j, r j ∈ K → j ∈ M) ∧
    (#{j | r j ∈ K} = 3 ∨ #{j | r j ∈ K} = 4)

/-- The conclusion of `refined_cover` (`Cover.lean`) on one side of a cut of seven edges: at most
one member of `L` is not an end of `M`, and if `a` is such a member, no rigid set lies in
`V(M) - a`, where `V(M)` is the set of ends of `M` on this side. -/
def GoodSide {α : Type*} [DecidableEq α] (r : Fin 7 → α) (L : Finset α) (M : Finset (Fin 7)) :
    Prop :=
  (∀ a ∈ L, ∀ b ∈ L, (∀ i ∈ M, r i ≠ a) → (∀ i ∈ M, r i ≠ b) → a = b) ∧
    ∀ a ∈ L, (∀ i ∈ M, r i ≠ a) → ∀ K : Finset α, a ∉ K → (∀ v ∈ K, ∃ i ∈ M, r i = v) →
      ¬ IsRigid r L M K

/-! ### Counting identities and the exact slack of a cut -/

/-- The edge count behind `gv_union_add_gv_inter`: for pairs `(X, Y)` and `(X', Y')`,
`e(X ∪ X', Y ∪ Y') + e(X ∩ X', Y ∩ Y')` equals
`e(X, Y) + e(X', Y') + e(X - X', Y' - Y) + e(X' - X, Y - Y')`. -/
lemma ec_union_add_ec_inter [DecidableEq V] (X X' Y Y' : Finset V) :
    ec G (X ∪ X') (Y ∪ Y') + ec G (X ∩ X') (Y ∩ Y') =
      ec G X Y + ec G X' Y' + ec G (X \ X') (Y' \ Y) + ec G (X' \ X) (Y \ Y') := by
  have hX : ec G X Y = ∑ x ∈ X ∪ X', if x ∈ X then dg G Y x else 0 := by
    rw [sum_ite_mem, union_inter_cancel_left]; rfl
  have hX' : ec G X' Y' = ∑ x ∈ X ∪ X', if x ∈ X' then dg G Y' x else 0 := by
    rw [sum_ite_mem, union_inter_cancel_right]; rfl
  have hI : ec G (X ∩ X') (Y ∩ Y') =
      ∑ x ∈ X ∪ X', if x ∈ X ∩ X' then dg G (Y ∩ Y') x else 0 := by
    rw [sum_ite_mem, inter_eq_right.2 (inter_subset_union : X ∩ X' ⊆ X ∪ X')]; rfl
  have hD : ec G (X \ X') (Y' \ Y) =
      ∑ x ∈ X ∪ X', if x ∈ X \ X' then dg G (Y' \ Y) x else 0 := by
    rw [sum_ite_mem, inter_eq_right.2 (sdiff_subset.trans subset_union_left)]; rfl
  have hD' : ec G (X' \ X) (Y \ Y') =
      ∑ x ∈ X ∪ X', if x ∈ X' \ X then dg G (Y \ Y') x else 0 := by
    rw [sum_ite_mem, inter_eq_right.2 (sdiff_subset.trans subset_union_right)]; rfl
  have hU : ec G (X ∪ X') (Y ∪ Y') = ∑ x ∈ X ∪ X', dg G (Y ∪ Y') x := rfl
  rw [hX, hX', hI, hU, hD, hD', ← sum_add_distrib, ← sum_add_distrib, ← sum_add_distrib,
    ← sum_add_distrib]
  refine sum_congr rfl fun x hxu => ?_
  have h1 := dg_union_add_dg_inter (G := G) Y Y' x
  have h2 : dg G (Y' \ Y) x + dg G Y x = dg G (Y ∪ Y') x := by
    rw [← union_sdiff_left]
    exact dg_sdiff_add subset_union_left x
  have h3 : dg G (Y \ Y') x + dg G Y' x = dg G (Y ∪ Y') x := by
    rw [← union_sdiff_right]
    exact dg_sdiff_add subset_union_right x
  rcases mem_union.1 hxu with hx | hx'
  · by_cases hx' : x ∈ X' <;> simp [hx, hx'] <;> omega
  · by_cases hx : x ∈ X <;> simp [hx, hx'] <;> omega

/-- **`g` of a union and an intersection, with the crossing term**: for `S = (X, Y)` and
`S' = (X', Y')`, `g(S ∪ S') + g(S ∩ S') = g(S) + g(S') - 2 e(S - S', S' - S)`, where the edges
between `S - S'` and `S' - S` are those of `(X - X', Y' - Y)` and of `(X' - X, Y - Y')`. QB4 has
the inequality `gv_union_add_gv_inter_le`. -/
theorem gv_union_add_gv_inter [DecidableEq V] (X X' Y Y' : Finset V) :
    gv G (X ∪ X') (Y ∪ Y') + gv G (X ∩ X') (Y ∩ Y') =
      gv G X Y + gv G X' Y' - 2 * ((ec G (X \ X') (Y' \ Y) : ℤ) + ec G (X' \ X) (Y \ Y')) := by
  have h := ec_union_add_ec_inter (G := G) X X' Y Y'
  have hX := card_union_add_card_inter X X'
  have hY := card_union_add_card_inter Y Y'
  unfold gv
  omega

/-- Deleting a vertex `y` of the second set (QB4's `gv_erase_left` deletes from the first). -/
lemma gv_erase_right [DecidableEq V] (X : Finset V) {Y : Finset V} {y : V} (hy : y ∈ Y) :
    gv G X (Y.erase y) = gv G X Y - 6 + 2 * (dg G X y : ℤ) := by
  have h := gv_erase_left (G := G) hy X
  rw [gv_comm X (Y.erase y), gv_comm X Y]
  exact h

/-- Adding a vertex `x ∉ X` to the first set. -/
lemma gv_insert_left [DecidableEq V] {X : Finset V} {x : V} (hx : x ∉ X) (Y : Finset V) :
    gv G (insert x X) Y = gv G X Y + 6 - 2 * (dg G Y x : ℤ) := by
  have h := gv_erase_left (G := G) (mem_insert_self x X) Y
  rw [erase_insert hx] at h
  linarith

/-- Adding a vertex `y ∉ Y` to the second set. -/
lemma gv_insert_right [DecidableEq V] (X : Finset V) {Y : Finset V} {y : V} (hy : y ∉ Y) :
    gv G X (insert y Y) = gv G X Y + 6 - 2 * (dg G X y : ℤ) := by
  have h := gv_insert_left (G := G) hy X
  rw [gv_comm X (insert y Y), gv_comm X Y]
  exact h

/-- **The deficiency inside a sub-pair**: for `X ⊆ U`, the deficiency of `Y` inside the pair
`(X, Y)` is its deficiency into `U` plus the number of edges from `Y` to `U - X`. QB4's
`gv_eq_left` writes `g(X, Y)` through the deficiency `df G X Y`. -/
lemma df_eq_df_add_ec [DecidableEq V] {U X : Finset V} (hX : X ⊆ U) (Y : Finset V) :
    df G X Y = df G U Y + (ec G Y (U \ X) : ℤ) := by
  have h1 := ec_sdiff_add_right (G := G) hX Y
  have h2 := df_eq (G := G) X Y
  have h3 := df_eq (G := G) U Y
  omega

/-- **The exact slack of a cut**: for `A ⊆ P` and `C ⊆ Q`,
`e(A, Q - C) = 6 (|A| - |C|) - D(A) + D(C) + e(P - A, C)`, with the deficiencies taken in the pair
`(P, Q)`. So the slack `σ = e(A, Q - C) - 4k` (`k = |A| - |C|`) of the cut condition at `(A, C)`
is `2k - D(A) + ε` with `ε = D(C) + e(P - A, C)`. QB4 has the bound `six_mul_sub_le_ec_sdiff`.
-/
theorem ec_sdiff_eq [DecidableEq V] {P Q A C : Finset V} (hA : A ⊆ P) (hC : C ⊆ Q) :
    (ec G A (Q \ C) : ℤ) = 6 * ((#A : ℤ) - #C) - df G Q A + df G P C + (ec G (P \ A) C : ℤ) := by
  have e1 := ec_sdiff_add_right (G := G) hC A
  have e2 := ec_comm (G := G) A C
  have e3 := ec_sdiff_add_right (G := G) hA C
  have e4 := ec_comm (G := G) (P \ A) C
  have e5 := df_eq (G := G) Q A
  have e6 := df_eq (G := G) P C
  omega

/-! ### Sizes, minimum degree, and the instance classes -/

/-- Sparsity does not depend on the order of the two sets of a pair. -/
lemma Sparse5.swap {U W : Finset V} (h : Sparse5 G U W) : Sparse5 G W U :=
  fun Y hY X hX h3 hlt => by
    rw [gv_comm]
    exact h X hX Y hY (by omega) (by omega)

/-- **Minimum degree four**, first set: in a sparse pair with `g ≤ 10` and at least four
vertices, every vertex of the first set has at least four neighbors in the second, since
`12 ≤ g(U - u, W) = g(U, W) - 6 + 2 deg u` (`gv_erase_left`). -/
lemma four_le_dg_of_sparse5_left [DecidableEq V] {U W : Finset V} (hsp : Sparse5 G U W)
    (hg : gv G U W ≤ 10) (h4 : 4 ≤ #U + #W) {u : V} (hu : u ∈ U) : 4 ≤ dg G W u := by
  have h1 := gv_erase_left (G := G) hu W
  have h2 := card_erase_add_one hu
  have h3 := hsp (U.erase u) (erase_subset u U) W Subset.rfl (by omega) (by omega)
  omega

/-- **Minimum degree four**, second set. -/
lemma four_le_dg_of_sparse5_right [DecidableEq V] {U W : Finset V} (hsp : Sparse5 G U W)
    (hg : gv G U W ≤ 10) (h4 : 4 ≤ #U + #W) {w : V} (hw : w ∈ W) : 4 ≤ dg G U w :=
  four_le_dg_of_sparse5_left hsp.swap (by rwa [gv_comm]) (by omega) hw

namespace IsC2

variable {U W : Finset V} {s : ℕ}

/-- A C2 instance has `g = 10`. -/
lemma gv_eq (h : IsC2 G U W s) : gv G U W = 10 := by
  rw [gv_eq_right, h.defU, h.cardU, h.cardW]
  push_cast
  ring

/-- A C2 instance has `D(W) = 8`. -/
lemma defW (h : IsC2 G U W s) : df G U W = 8 := by
  rw [df_right_eq (by rw [h.cardW, h.cardU]), h.defU]
  norm_num

/-- **The size of a C2 instance**: `s ≥ 5`, since `6s - 2 = e(U, W) ≤ s (s + 1)`. -/
lemma five_le (h : IsC2 G U W s) : 5 ≤ s := by
  have h1 := ec_le_card_mul (G := G) U W
  have h2 := df_eq (G := G) W U
  rw [h.defU, h.cardU] at h2
  rw [h.cardU, h.cardW] at h1
  have hpos := h.pos
  by_contra hlt
  interval_cases s <;> omega

end IsC2

namespace IsE5

variable {P Q : Finset V} {a : ℕ}

/-- An E5 instance has `g = 10`. -/
lemma gv_eq (h : IsE5 G P Q a) : gv G P Q = 10 := by
  rw [gv_eq_left, h.defQ, h.cardP, h.cardQ]
  norm_num

/-- An E5 instance read with the two sides swapped. -/
lemma swap (h : IsE5 G P Q a) : IsE5 G Q P a :=
  { pos := h.pos
    cardP := h.cardQ
    cardQ := h.cardP
    degP := h.degQ
    degQ := h.degP
    defP := h.defQ
    defQ := h.defP }

/-- **The size of an E5 instance**: `a ≥ 5`, since `6a - 5 = e(P, Q) ≤ a²` and `a ≥ 2`. -/
lemma five_le (h : IsE5 G P Q a) : 5 ≤ a := by
  have h1 := ec_le_card_mul (G := G) P Q
  have h2 := df_eq (G := G) Q P
  rw [h.defP, h.cardP] at h2
  rw [h.cardP, h.cardQ] at h1
  have hpos := h.pos
  by_contra hlt
  interval_cases a <;> omega

end IsE5

/-- **The case split.** A pair with degrees at most six, at least three vertices and `g ≤ 10` is an
E4, C1, E5 or C2 instance, C1 and C2 in one of the two orientations. By `gv_eq_left` and
`gv_eq_right`, `g = 2d + 6j` with `j` the size difference of the sides and `d` the deficiency of the
smaller side: `j = 0, d ≤ 4` is E4, `j = 0, d = 5` is E5, `j = 1, d ≤ 1` is C1 and `j = 1, d = 2` is
C2. -/
theorem small_gv_cases5 {X Y : Finset V} (hdX : ∀ x ∈ X, dg G Y x ≤ 6)
    (hdY : ∀ y ∈ Y, dg G X y ≤ 6) (h3 : 3 ≤ #X + #Y) (hg : gv G X Y ≤ 10) :
    IsE4 G X Y #X ∨ IsC1 G X Y #X ∨ IsC1 G Y X #Y ∨
      IsE5 G X Y #X ∨ IsC2 G X Y #X ∨ IsC2 G Y X #Y := by
  have hl := gv_eq_left (G := G) X Y
  have hr := gv_eq_right (G := G) X Y
  have hY0 : 0 ≤ df G X Y := df_nonneg hdY
  have hX0 : 0 ≤ df G Y X := df_nonneg hdX
  rcases lt_trichotomy #X #Y with hlt | heq | hgt
  · by_cases hd : df G Y X ≤ 1
    · exact Or.inr (Or.inl
        { pos := by omega
          cardU := rfl
          cardW := by omega
          degU := hdX
          degW := hdY
          defU := hd })
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        { pos := by omega
          cardU := rfl
          cardW := by omega
          degU := hdX
          degW := hdY
          defU := by omega }))))
  · by_cases hd : df G X Y ≤ 4
    · exact Or.inl
        { pos := by omega
          cardP := rfl
          cardQ := heq.symm
          degP := hdX
          degQ := hdY
          defP := by omega
          defQ := hd }
    · exact Or.inr (Or.inr (Or.inr (Or.inl
        { pos := by omega
          cardP := rfl
          cardQ := heq.symm
          degP := hdX
          degQ := hdY
          defP := by omega
          defQ := by omega })))
  · by_cases hd : df G X Y ≤ 1
    · exact Or.inr (Or.inr (Or.inl
        { pos := by omega
          cardU := rfl
          cardW := by omega
          degU := hdY
          degW := hdX
          defU := hd }))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        { pos := by omega
          cardU := rfl
          cardW := by omega
          degU := hdY
          degW := hdX
          defU := by omega }))))

/-! ### A minimal counterexample: sparsity and violated cuts -/

/-- **Sparsity of a minimal counterexample.** A pair with no quartic subgraph is sparse once
every proper sub-pair with at least three vertices and `g ≤ 10` has a quartic subgraph: a
sub-pair with `g < 12` has `g ≤ 10` (`g` is even), and its quartic subgraph is one of the pair. -/
theorem sparse5_of_minimal [DecidableEq V] {U W : Finset V}
    (ih : ∀ X ⊆ U, ∀ Y ⊆ W, 3 ≤ #X + #Y → #X + #Y < #U + #W → gv G X Y ≤ 10 → Quartic G X Y)
    (hq : ¬ Quartic G U W) : Sparse5 G U W := by
  intro X hX Y hY h3 hlt
  by_contra hg
  have hg10 : gv G X Y ≤ 10 := by
    obtain ⟨r, hr⟩ := even_gv (G := G) X Y
    omega
  exact hq ((ih X hX Y hY h3 hlt hg10).mono hX hY)

/-- **A violated cut of a balanced pair** (used for E5): a pair `(P, Q)` with `|P| = |Q|`, `Q`
nonempty and no quartic subgraph has no 4-factor (a 4-factor would give one,
`quartic_of_four_factor`), so it violates the cut condition of `exists_four_factor`. -/
theorem exists_violation_of_not_quartic [DecidableEq V] {P Q : Finset V} (hcard : #P = #Q)
    (hQ : Q.Nonempty) (hq : ¬ Quartic G P Q) :
    ∃ A ⊆ P, ∃ C ⊆ Q, ec G A (Q \ C) + 4 * #C < 4 * #A := by
  by_contra! hcon
  obtain ⟨F, hF, hadj, hFP, hFQ⟩ := exists_four_factor P Q hcard hcon
  exact hq (quartic_of_four_factor Subset.rfl hQ hF hadj hFP hFQ).swap

/-- **A violated cut at every `W`-vertex** (used for C2): if `(U, W)` with `|W| = |U| + 1` and
`U` nonempty has no quartic subgraph, then for every `y ∈ W` the balanced pair `(W - y, U)`
violates the cut condition. This is QB4's `hviol_of_not_quartic` without the degree hypothesis. -/
theorem exists_violation_erase_of_not_quartic [DecidableEq V] {U W : Finset V}
    (hW : #W = #U + 1) (hU : U.Nonempty) (hq : ¬ Quartic G U W) {y : V} (hy : y ∈ W) :
    ∃ A ⊆ W.erase y, ∃ C ⊆ U, ec G A (U \ C) + 4 * #C < 4 * #A := by
  by_contra! hcon
  obtain ⟨F, hF, hadj, hFP, hFQ⟩ := exists_four_factor (W.erase y) U
    (by rw [card_erase_of_mem hy, hW, Nat.add_sub_cancel]) hcon
  exact hq (quartic_of_four_factor (erase_subset y W) hU hF hadj hFP hFQ)

end Erdos585.QB5
