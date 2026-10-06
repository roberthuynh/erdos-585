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
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Tactic

/-!
# QB(4): counting on a pair of vertex sets

The proof of QB(4), the statement of `Erdos585.qb4` in `Statement.lean`, works with one ambient
graph `G` and pairs of finite vertex sets `(X, Y)`.
Only the edges of `G` between `X` and `Y` are counted, so a pair `(X, Y)` stands for the
bipartite graph `G[X, Y]`, and a vertex set `S = X ∪ Y` of an instance with sides `(U, W)` is
the pair `(S ∩ U, S ∩ W)`. Sub-instances are smaller pairs of the same graph, so the induction
never changes the vertex type.

* `dg G S v`: the number of neighbors of `v` in `S`.
* `ec G A B`: the number of adjacent pairs in `A × B`, counted from `A`.
* `gv G X Y = 6 (|X| + |Y|) - 2 e(X, Y)`, written `g(X, Y)`.
* `df G S Z = Σ_{z ∈ Z} (6 - dg G S z)`, the deficiency of `Z` with degrees taken into `S`.
* In comments, for a pair with sides `(U, W)`: `D(Z)` is the deficiency of a subset `Z` of one
  side with degrees taken into the other side, `D_U = D(U)`, `D_W = D(W)`, and
  `def(y) = 6 - dg G U y` for `y ∈ W`. For a cut `(A, C)` with `A ⊆ W` and `C ⊆ U`,
  `k = |A| - |C|`.

The basic facts about `g`: `g` in terms of the deficiency of either set (`gv_eq_left`,
`gv_eq_right`), submodularity (`gv_union_add_gv_inter_le`), deleting a vertex (`gv_erase_left`),
the cut identity (`gv_sdiff_sdiff`) and the slack bound used with the 4-factor criterion
(`six_mul_sub_le_ec_sdiff`).
-/

open Finset

namespace Erdos585.QB4

variable {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The number of neighbors of `v` in `S`. -/
def dg (S : Finset V) (v : V) : ℕ := #{w ∈ S | G.Adj v w}

/-- The number of adjacent pairs `(a, b)` with `a ∈ A` and `b ∈ B`. -/
def ec (A B : Finset V) : ℕ := ∑ a ∈ A, dg G B a

/-- The function `g(X, Y) = 6 (|X| + |Y|) - 2 e(X, Y)` of a pair of vertex sets. For disjoint `X`
and `Y` this is `6 |X ∪ Y| - 2 e(X, Y)`. -/
def gv (X Y : Finset V) : ℤ := 6 * ((#X : ℤ) + #Y) - 2 * (ec G X Y : ℤ)

/-- The deficiency of `Z`, with the degree of each vertex taken into `S`. -/
def df (S Z : Finset V) : ℤ := ∑ z ∈ Z, (6 - (dg G S z : ℤ))

variable {G}

/-! ### Degrees into a set -/

lemma dg_mono {S T : Finset V} (h : S ⊆ T) (v : V) : dg G S v ≤ dg G T v :=
  card_le_card (filter_subset_filter _ h)

lemma dg_le_card (S : Finset V) (v : V) : dg G S v ≤ #S := card_filter_le _ _

lemma dg_union_of_disjoint [DecidableEq V] {S T : Finset V} (h : Disjoint S T) (v : V) :
    dg G (S ∪ T) v = dg G S v + dg G T v := by
  unfold dg
  rw [filter_union, card_union_of_disjoint (disjoint_filter_filter h)]

/-- Splitting the degree into `S` along a subset `T ⊆ S`. -/
lemma dg_sdiff_add [DecidableEq V] {S T : Finset V} (h : T ⊆ S) (v : V) :
    dg G (S \ T) v + dg G T v = dg G S v := by
  rw [← dg_union_of_disjoint sdiff_disjoint, sdiff_union_of_subset h]

lemma dg_union_add_dg_inter [DecidableEq V] (S T : Finset V) (v : V) :
    dg G (S ∪ T) v + dg G (S ∩ T) v = dg G S v + dg G T v := by
  unfold dg
  rw [filter_union, filter_inter_distrib, card_union_add_card_inter]

lemma dg_erase_add [DecidableEq V] {S : Finset V} {x : V} (hx : x ∈ S) (v : V) (hv : G.Adj v x) :
    dg G (S.erase x) v + 1 = dg G S v := by
  unfold dg
  rw [filter_erase, card_erase_add_one (mem_filter.2 ⟨hx, hv⟩)]

/-! ### Edge counts between two sets -/

/-- Double counting: the adjacent pairs of `A × B` and of `B × A` are equinumerous. -/
lemma ec_comm (A B : Finset V) : ec G A B = ec G B A := by
  unfold ec dg
  simp_rw [card_filter]
  rw [sum_comm]
  refine sum_congr rfl fun b _ => sum_congr rfl fun a _ => ?_
  simp only [G.adj_comm]

lemma ec_mono_left {A A' : Finset V} (h : A ⊆ A') (B : Finset V) : ec G A B ≤ ec G A' B :=
  sum_le_sum_of_subset h

lemma ec_mono_right (A : Finset V) {B B' : Finset V} (h : B ⊆ B') : ec G A B ≤ ec G A B' :=
  sum_le_sum fun a _ => dg_mono h a

lemma ec_mono {A A' B B' : Finset V} (hA : A ⊆ A') (hB : B ⊆ B') : ec G A B ≤ ec G A' B' :=
  (ec_mono_left hA B).trans (ec_mono_right A' hB)

lemma ec_sdiff_add_right [DecidableEq V] {B T : Finset V} (h : T ⊆ B) (A : Finset V) :
    ec G A (B \ T) + ec G A T = ec G A B := by
  unfold ec
  rw [← sum_add_distrib]
  exact sum_congr rfl fun a _ => dg_sdiff_add h a

lemma ec_sdiff_add_left [DecidableEq V] {A T : Finset V} (h : T ⊆ A) (B : Finset V) :
    ec G (A \ T) B + ec G T B = ec G A B := by
  unfold ec
  rw [sum_sdiff h]

/-- `e(A, B) ≤ 6 |A|` when every vertex of `A` has at most six neighbors in `B`. -/
lemma ec_le_six_mul {A B : Finset V} (h : ∀ a ∈ A, dg G B a ≤ 6) : ec G A B ≤ 6 * #A := by
  unfold ec
  calc ∑ a ∈ A, dg G B a ≤ ∑ _a ∈ A, 6 := sum_le_sum h
    _ = 6 * #A := by rw [sum_const, smul_eq_mul, mul_comm]

/-! ### Deficiencies -/

lemma df_eq (S Z : Finset V) : df G S Z = 6 * (#Z : ℤ) - (ec G Z S : ℤ) := by
  unfold df ec
  rw [sum_sub_distrib, sum_const, nsmul_eq_mul, Nat.cast_sum]
  ring

lemma df_nonneg {S Z : Finset V} (h : ∀ z ∈ Z, dg G S z ≤ 6) : 0 ≤ df G S Z :=
  sum_nonneg fun z hz => by have := h z hz; omega

lemma df_sdiff_add [DecidableEq V] {S Z T : Finset V} (h : T ⊆ Z) : df G S (Z \ T) + df G S T = df G S Z := by
  unfold df
  rw [sum_sdiff h]

/-- A deficiency over a subset is at most the deficiency over the whole set. -/
lemma df_le_of_subset [DecidableEq V] {S Z T : Finset V} (h : T ⊆ Z) (hZ : ∀ z ∈ Z, dg G S z ≤ 6) :
    df G S T ≤ df G S Z := by
  have h1 := df_sdiff_add (G := G) (S := S) h
  have h2 : 0 ≤ df G S (Z \ T) := df_nonneg fun z hz => hZ z (sdiff_subset hz)
  linarith

/-- A deficiency taken into a smaller set is at least the deficiency into the larger set. -/
lemma df_anti {S T Z : Finset V} (h : S ⊆ T) : df G T Z ≤ df G S Z :=
  sum_le_sum fun z _ => by have := dg_mono (G := G) h z; omega

/-- A sum of nonnegative deficiencies that vanishes vanishes termwise. -/
lemma dg_eq_six_of_df_eq_zero {S Z : Finset V} (h : ∀ z ∈ Z, dg G S z ≤ 6)
    (h0 : df G S Z = 0) {z : V} (hz : z ∈ Z) : dg G S z = 6 := by
  have hall := (sum_eq_zero_iff_of_nonneg (fun x hx => by have := h x hx; omega)).1 h0 z hz
  have := h z hz
  omega

/-! ### The function `g` -/

/-- `g` in terms of the deficiency of the second set `Y`: `g = 2 D(Y) + 6 (|X| - |Y|)`. -/
lemma gv_eq_left (X Y : Finset V) :
    gv G X Y = 2 * df G X Y + 6 * ((#X : ℤ) - #Y) := by
  unfold gv
  rw [df_eq, ec_comm Y X]
  ring

/-- `g` in terms of the deficiency of the first set `X`: `g = 2 D(X) + 6 (|Y| - |X|)`. -/
lemma gv_eq_right (X Y : Finset V) :
    gv G X Y = 2 * df G Y X + 6 * ((#Y : ℤ) - #X) := by
  unfold gv
  rw [df_eq]
  ring

lemma gv_comm (X Y : Finset V) : gv G X Y = gv G Y X := by
  unfold gv
  rw [ec_comm]
  ring

lemma even_gv (X Y : Finset V) : Even (gv G X Y) := by
  unfold gv
  exact ⟨3 * ((#X : ℤ) + #Y) - (ec G X Y : ℤ), by ring⟩

/-- Supermodularity of the induced edge count, the core of `gv_union_add_gv_inter_le`. -/
lemma ec_add_ec_le [DecidableEq V] (X X' Y Y' : Finset V) :
    ec G X Y + ec G X' Y' ≤ ec G (X ∪ X') (Y ∪ Y') + ec G (X ∩ X') (Y ∩ Y') := by
  have hX : ec G X Y = ∑ x ∈ X ∪ X', if x ∈ X then dg G Y x else 0 := by
    rw [sum_ite_mem, union_inter_cancel_left]; rfl
  have hX' : ec G X' Y' = ∑ x ∈ X ∪ X', if x ∈ X' then dg G Y' x else 0 := by
    rw [sum_ite_mem, union_inter_cancel_right]; rfl
  have hI : ec G (X ∩ X') (Y ∩ Y') =
      ∑ x ∈ X ∪ X', if x ∈ X ∩ X' then dg G (Y ∩ Y') x else 0 := by
    rw [sum_ite_mem, inter_eq_right.2 (inter_subset_union : X ∩ X' ⊆ X ∪ X')]; rfl
  have hU : ec G (X ∪ X') (Y ∪ Y') = ∑ x ∈ X ∪ X', dg G (Y ∪ Y') x := rfl
  rw [hX, hX', hI, hU, ← sum_add_distrib, ← sum_add_distrib]
  refine sum_le_sum fun x _ => ?_
  have h1 := dg_union_add_dg_inter (G := G) Y Y' x
  have h2 := dg_mono (G := G) (subset_union_left : Y ⊆ Y ∪ Y') x
  have h3 := dg_mono (G := G) (subset_union_right : Y' ⊆ Y ∪ Y') x
  by_cases hx : x ∈ X <;> by_cases hx' : x ∈ X' <;> simp [hx, hx'] <;> omega

/-- `g` is submodular on pairs. -/
lemma gv_union_add_gv_inter_le [DecidableEq V] (X X' Y Y' : Finset V) :
    gv G (X ∪ X') (Y ∪ Y') + gv G (X ∩ X') (Y ∩ Y') ≤ gv G X Y + gv G X' Y' := by
  have h := ec_add_ec_le (G := G) X X' Y Y'
  have hX := card_union_add_card_inter X X'
  have hY := card_union_add_card_inter Y Y'
  unfold gv
  omega

/-- Deleting a vertex `x` of the first set. -/
lemma gv_erase_left [DecidableEq V] {X : Finset V} {x : V} (hx : x ∈ X) (Y : Finset V) :
    gv G (X.erase x) Y = gv G X Y - 6 + 2 * (dg G Y x : ℤ) := by
  have h1 : ec G (X.erase x) Y + dg G Y x = ec G X Y := sum_erase_add X _ hx
  have h2 := card_erase_add_one hx
  unfold gv
  omega

/-! ### The cut identity and the slack bound -/

/-- The cut identity: for `A ⊆ W` and `C ⊆ U`, the complement pair
`(U - C, W - A)` has `g = 6 ((|W| - |A|) - (|U| - |C|)) + 2 D_U - 2 D(C) + 2 e(A, U - C)`. -/
lemma gv_sdiff_sdiff [DecidableEq V] {U W A C : Finset V} (hA : A ⊆ W) (hC : C ⊆ U) :
    gv G (U \ C) (W \ A) = 6 * (((#W : ℤ) - #A) - ((#U : ℤ) - #C)) + 2 * df G W U
      - 2 * df G W C + 2 * (ec G A (U \ C) : ℤ) := by
  have h1 := ec_sdiff_add_right (G := G) hA (U \ C)
  have h2 := ec_comm (G := G) (U \ C) A
  have h3 := df_sdiff_add (G := G) (S := W) hC
  have h4 := df_eq (G := G) W (U \ C)
  have hcU := card_sdiff_add_card_eq_card hC
  have hcW := card_sdiff_add_card_eq_card hA
  unfold gv
  omega

/-- The slack bound used with the 4-factor criterion: if every vertex of `C` has at most six
neighbors in `W`
and `A ⊆ W`, then `e(A, U - C) ≥ 6 (|A| - |C|) - D(A)`, the deficiency taken into `U`. -/
lemma six_mul_sub_le_ec_sdiff [DecidableEq V] {U W A C : Finset V} (hA : A ⊆ W) (hC : C ⊆ U)
    (hdeg : ∀ c ∈ C, dg G W c ≤ 6) :
    6 * ((#A : ℤ) - #C) - df G U A ≤ (ec G A (U \ C) : ℤ) := by
  have h1 := ec_sdiff_add_right (G := G) hC A
  have h2 : ec G A C ≤ 6 * #C := by
    rw [ec_comm]
    exact (ec_mono_right C hA).trans (ec_le_six_mul hdeg)
  have h3 := df_eq (G := G) U A
  omega

end Erdos585.QB4
