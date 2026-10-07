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
# QB(5): the θ-calculus of a 2-block

Part of the proof of QB(5) (`Erdos585.qb5`). This file sets up a function `θ` on the sub-pairs of a
2-block `X = (A, C)` (`IsBlock`: `|A| = |C| + 2 ≥ 6`, every `c ∈ C` has six neighbors in `A`,
`g ≥ 12` on every sub-pair with at least three vertices, and `3 ≤ d_a ≤ 6` for `a ∈ A`, where `d_a`
is the number of neighbors of `a` in `C`), with multiplicities `m : V → ℕ`. In the applications,
`m(a)` is the number of chosen edges at `a`, out of four chosen edges that leave the block at
vertices of `A`: four of the seven cut edges in `E5.lean`, the four edges at `u0` in `C2Hub.lean`. A
sub-pair `S` of `X` is a pair `(T, J)` with `T ⊆ A` and `J ⊆ C`, and only the `T`-`J` adjacencies
are counted, as everywhere in the pair setting of `Openmath/Proofs/QB4/Defs.lean`. The facts here
serve KL1 (`kl1_thetaStar` and `kl1` in `KL1.lean`): if `m(A) = 4`, `d_a + m(a) ≤ 6` on `A` and `m`
covers, that is `d_a + m(a) ≥ 4` on `A`, some `p ∈ A` lies in no overloaded set.

Notation, for `S = (T, J)`: `κ(S) = |T| - |J|`, `g(S) = gv G T J`, `e(T, J) = ec G T J`,
`δ_a = 6 - d_a`, the weight `w(a) = δ_a - m(a)`, `∂_A(S) = e(T, C - J)`, `∂_C(S) = e(J, A - T)`
and `h(S) = w(T) + ∂_A(S)`, where `m(T)` and `w(T)` are sums over `T`.

* `msum m T = m(T)` and `wsum G m C T = w(T) = Σ_{a ∈ T} (δ_a - m(a))`.
* `theta G m T J = θ(S) = m(T) + 4 - 4|T| - 2|J| + e(T, J)`, that is
  `θ(S) = m(T) + 4 - κ(S) - g(S)/2`.
* `thetaStar G m C T = θ*(T) = m(T) + 4 - 4|T| + Σ_{c ∈ C} (e(c, T) - 2)^+`, the maximum of
  `θ(T, J)` over `J ⊆ C`, attained at `cpr G C T = C'(T) = {c ∈ C : e(c, T) ≥ 3}`; write
  `X'(T) = (T, C'(T))`.
* `T ⊆ A` is *overloaded* if `θ*(T) ≥ 1`, and `A1 ⊆ A` is *under-supplied* if
  `m(A1) < dem(A1)`, where `dem(A1) = 4 |A1| - Σ_{c ∈ C} min(4, e(c, A1))` is the demand (`dem`).

Results:

* Identities for `θ`: in terms of `h` (`theta_eq_four_add`) and of `∂_C` (`theta_eq_boundary`),
  for a union and an intersection, with a crossing term (`theta_union_add_theta_inter`), and for
  adding one vertex of `C` (`theta_insert`).
* `theta_le_thetaStar`, `theta_eq_thetaStar` and `theta_cpr` (the maximum over `J`), and the
  supermodularity of `θ*` (`thetaStar_union_add_inter`).
* Values and bounds: `theta_empty`, `thetaStar_empty`, `thetaStar_singleton`,
  `thetaStar_of_card_le_two`, `thetaStar_of_card_eq_two` and `theta_singleton` on small sets;
  `theta_le_of_three_le`, `three_mul_theta_le`, `theta_le_two` and `thetaStar_le_two` on
  sub-pairs with at least three vertices; `kappa_bounds`, `cpr_nonempty` and `two_le_msum` on
  overloaded sets.
* When `m(A) = 4`, `T` is overloaded iff `A - T` is under-supplied (`overloaded_iff`), and the
  conclusion of KL1 in demand form follows from its form in `θ*` (`exists_good_of_thetaStar`).
* `KLData`: the hypotheses of `kl1` other than covering.
-/

open Finset

namespace Erdos585.QB5

open QB4

variable {V : Type*} {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ### Multiplicities and weights -/

/-- `m(T) = Σ_{a ∈ T} m(a)` as an integer; in the applications, the number of chosen edges at the
vertices of `T`. -/
def msum (m : V → ℕ) (T : Finset V) : ℤ := ∑ a ∈ T, (m a : ℤ)

lemma msum_nonneg (m : V → ℕ) (T : Finset V) : 0 ≤ msum m T :=
  sum_nonneg fun _ _ => Nat.cast_nonneg _

lemma msum_mono (m : V → ℕ) {T T' : Finset V} (h : T ⊆ T') : msum m T ≤ msum m T' :=
  sum_le_sum_of_subset_of_nonneg h fun _ _ _ => Nat.cast_nonneg _

lemma msum_empty (m : V → ℕ) : msum m ∅ = 0 := sum_empty

lemma msum_singleton (m : V → ℕ) (a : V) : msum m {a} = m a := sum_singleton _ _

lemma msum_union_add_inter [DecidableEq V] (m : V → ℕ) (T T' : Finset V) :
    msum m (T ∪ T') + msum m (T ∩ T') = msum m T + msum m T' :=
  sum_union_inter

lemma msum_sdiff_add [DecidableEq V] (m : V → ℕ) {T T' : Finset V} (h : T ⊆ T') :
    msum m (T' \ T) + msum m T = msum m T' :=
  sum_sdiff h

lemma msum_union_of_disjoint [DecidableEq V] (m : V → ℕ) {T T' : Finset V}
    (h : Disjoint T T') : msum m (T ∪ T') = msum m T + msum m T' :=
  sum_union h

/-- `m(v) ≤ m(T)` for `v ∈ T`. -/
lemma le_msum (m : V → ℕ) {T : Finset V} {v : V} (hv : v ∈ T) : (m v : ℤ) ≤ msum m T :=
  single_le_sum (f := fun a => (m a : ℤ)) (fun _ _ => Nat.cast_nonneg _) hv

variable (G) in
/-- The weight `w(T) = Σ_{a ∈ T} (δ_a - m(a))`, with `δ_a = 6 - d_a` and `d_a` the number of
neighbors of `a` in `C`. -/
def wsum (m : V → ℕ) (C T : Finset V) : ℤ := ∑ a ∈ T, (6 - (dg G C a : ℤ) - m a)

lemma wsum_eq (m : V → ℕ) (C T : Finset V) :
    wsum G m C T = 6 * #T - (ec G T C : ℤ) - msum m T := by
  unfold wsum msum ec
  rw [sum_sub_distrib, sum_sub_distrib, sum_const, nsmul_eq_mul, Nat.cast_sum]
  ring

lemma wsum_union_of_disjoint [DecidableEq V] (m : V → ℕ) (C : Finset V) {T T' : Finset V}
    (h : Disjoint T T') : wsum G m C (T ∪ T') = wsum G m C T + wsum G m C T' :=
  sum_union h

lemma wsum_sdiff_add [DecidableEq V] (m : V → ℕ) (C : Finset V) {T T' : Finset V} (h : T ⊆ T') :
    wsum G m C (T' \ T) + wsum G m C T = wsum G m C T' :=
  sum_sdiff h

/-- `w ≥ 0` on subsets of `A` when `m ≤ δ`. -/
lemma wsum_nonneg {m : V → ℕ} {A C T : Finset V} (hmδ : ∀ a ∈ A, m a + dg G C a ≤ 6)
    (hT : T ⊆ A) : 0 ≤ wsum G m C T :=
  sum_nonneg fun a ha => by have := hmδ a (hT ha); omega

/-- `w ≤ 2` at every vertex when `d_a + m(a) ≥ 4` on `A` (the covering condition of `kl1`), so
`w(T) ≤ 2|T|`. -/
lemma wsum_le_two_mul {m : V → ℕ} {A C T : Finset V} (hcov : ∀ a ∈ A, 4 ≤ dg G C a + m a)
    (hT : T ⊆ A) : wsum G m C T ≤ 2 * #T := by
  have h : wsum G m C T ≤ ∑ _a ∈ T, (2 : ℤ) :=
    sum_le_sum fun a ha => by have := hcov a (hT ha); omega
  rw [sum_const, nsmul_eq_mul] at h
  linarith

/-! ### The function `θ` -/

variable (G) in
/-- `θ` of the sub-pair `S = (T, J)`,
`θ(S) = m(T) + 4 - κ(S) - g(S)/2 = m(T) + 4 - 4|T| - 2|J| + e(T, J)`. -/
def theta (m : V → ℕ) (T J : Finset V) : ℤ := msum m T + 4 - 4 * #T - 2 * #J + ec G T J

variable (G) in
/-- `θ*(T) = m(T) + 4 - 4|T| + Σ_{c ∈ C} (e(c, T) - 2)^+`, which is `max_{J ⊆ C} θ(T, J)`
(`theta_le_thetaStar`, `theta_cpr`). -/
def thetaStar (m : V → ℕ) (C T : Finset V) : ℤ :=
  msum m T + 4 - 4 * #T + ∑ c ∈ C, max 0 ((dg G T c : ℤ) - 2)

variable (G) in
/-- `C'(T) = {c ∈ C : e(c, T) ≥ 3}`, where `θ(T, ·)` attains `θ*(T)` (`theta_cpr`). -/
def cpr (C T : Finset V) : Finset V := {c ∈ C | 3 ≤ dg G T c}

lemma cpr_subset (C T : Finset V) : cpr G C T ⊆ C := filter_subset _ _

lemma mem_cpr {C T : Finset V} {c : V} : c ∈ cpr G C T ↔ c ∈ C ∧ 3 ≤ dg G T c := mem_filter

/-- The edges of `(T, J)` counted from `J`. -/
private lemma ec_eq_sum_dg (T J : Finset V) : ec G T J = ∑ c ∈ J, dg G T c := by
  rw [ec_comm]
  rfl

/-- `θ(T, J) = m(T) + 4 - 4|T| + Σ_{c ∈ J} (e(c, T) - 2)`. -/
lemma theta_eq_sum (m : V → ℕ) (T J : Finset V) :
    theta G m T J = msum m T + 4 - 4 * #T + ∑ c ∈ J, ((dg G T c : ℤ) - 2) := by
  unfold theta
  rw [ec_eq_sum_dg, sum_sub_distrib, sum_const, nsmul_eq_mul, Nat.cast_sum]
  ring

/-- `θ(T, J) ≤ θ*(T)` for every `J ⊆ C`. -/
lemma theta_le_thetaStar (m : V → ℕ) {C J : Finset V} (hJ : J ⊆ C) (T : Finset V) :
    theta G m T J ≤ thetaStar G m C T := by
  rw [theta_eq_sum]
  unfold thetaStar
  have h1 : ∑ c ∈ J, ((dg G T c : ℤ) - 2) ≤ ∑ c ∈ J, max 0 ((dg G T c : ℤ) - 2) :=
    sum_le_sum fun c _ => le_max_right _ _
  have h2 : ∑ c ∈ J, max 0 ((dg G T c : ℤ) - 2) ≤ ∑ c ∈ C, max 0 ((dg G T c : ℤ) - 2) :=
    sum_le_sum_of_subset_of_nonneg hJ fun c _ _ => le_max_left _ _
  linarith

/-- `θ(T, J) = θ*(T)` whenever `J ⊆ C` contains every `c` with `e(c, T) ≥ 3` and only `c` with
`e(c, T) ≥ 2`, by `theta_eq_sum` (used in `theta_cpr` here and in `KL1.lean`). -/
lemma theta_eq_thetaStar (m : V → ℕ) {C J T : Finset V} (hJ : J ⊆ C)
    (h3 : ∀ c ∈ C, 3 ≤ dg G T c → c ∈ J) (h2 : ∀ c ∈ J, 2 ≤ dg G T c) :
    theta G m T J = thetaStar G m C T := by
  rw [theta_eq_sum]
  unfold thetaStar
  have e1 : ∑ c ∈ J, max 0 ((dg G T c : ℤ) - 2) = ∑ c ∈ C, max 0 ((dg G T c : ℤ) - 2) := by
    refine sum_subset hJ fun c hc hcJ => ?_
    have : dg G T c ≤ 2 := by
      by_contra h
      exact hcJ (h3 c hc (by omega))
    have : (dg G T c : ℤ) ≤ 2 := by exact_mod_cast this
    exact max_eq_left (by linarith)
  have e2 : ∑ c ∈ J, ((dg G T c : ℤ) - 2) = ∑ c ∈ J, max 0 ((dg G T c : ℤ) - 2) := by
    refine sum_congr rfl fun c hc => ?_
    have : (2 : ℤ) ≤ dg G T c := by exact_mod_cast h2 c hc
    exact (max_eq_right (by linarith)).symm
  rw [e2, e1]

/-- `θ*(T)` is attained at `X'(T) = (T, C'(T))`. -/
lemma theta_cpr (m : V → ℕ) (C T : Finset V) : theta G m T (cpr G C T) = thetaStar G m C T :=
  theta_eq_thetaStar m (cpr_subset C T) (fun c hc h => mem_cpr.2 ⟨hc, h⟩)
    (fun c hc => by have := (mem_cpr.1 hc).2; omega)

/-! ### Identities for `θ` -/

/-- **Union and intersection**: `θ(S ∪ S') + θ(S ∩ S') = θ(S) + θ(S') + e(S - S', S' - S)`, where
for pairs the edges between `S - S'` and `S' - S` are those of `(T - T', J' - J)` and
`(T' - T, J - J')`. -/
theorem theta_union_add_theta_inter [DecidableEq V] (m : V → ℕ) (T T' J J' : Finset V) :
    theta G m (T ∪ T') (J ∪ J') + theta G m (T ∩ T') (J ∩ J') =
      theta G m T J + theta G m T' J' + ec G (T \ T') (J' \ J) + ec G (T' \ T) (J \ J') := by
  have h := ec_union_add_ec_inter (G := G) T T' J J'
  have hT := card_union_add_card_inter T T'
  have hJ := card_union_add_card_inter J J'
  have hm := msum_union_add_inter m T T'
  unfold theta
  omega

/-- **Adding a vertex of `C`**: adding `c ∉ J` changes `θ` by `e(c, T) - 2`. -/
lemma theta_insert [DecidableEq V] (m : V → ℕ) (T : Finset V) {J : Finset V} {c : V}
    (hc : c ∉ J) : theta G m T (insert c J) = theta G m T J + dg G T c - 2 := by
  rw [theta_eq_sum, theta_eq_sum, sum_insert hc]
  ring

/-- Adding a set `Z` disjoint from `J` changes `θ` by `Σ_{c ∈ Z} (e(c, T) - 2)`. -/
lemma theta_union_right [DecidableEq V] (m : V → ℕ) (T : Finset V) {J Z : Finset V}
    (h : Disjoint J Z) :
    theta G m T (J ∪ Z) = theta G m T J + ∑ c ∈ Z, ((dg G T c : ℤ) - 2) := by
  rw [theta_eq_sum, theta_eq_sum, sum_union h]
  ring

/-- **`θ` and `h`**: `θ(S) = 4 + 2κ(S) - h(S)` with `h(S) = w(T) + ∂_A(S)` and
`∂_A(S) = e(T, C - J)`. -/
lemma theta_eq_four_add [DecidableEq V] (m : V → ℕ) {C J : Finset V} (hJ : J ⊆ C)
    (T : Finset V) :
    theta G m T J = 4 + 2 * ((#T : ℤ) - #J) - (wsum G m C T + ec G T (C \ J)) := by
  have h1 := ec_sdiff_add_right (G := G) hJ T
  rw [wsum_eq]
  unfold theta
  omega

/-- **`θ` and the boundary at `C`**: `θ(S) = m(T) + 4 - 4κ(S) - ∂_C(S)` with
`∂_C(S) = e(J, A - T)`. -/
lemma theta_eq_boundary [DecidableEq V] {A C : Finset V} (hX : IsBlock G A C) (m : V → ℕ)
    {T J : Finset V} (hT : T ⊆ A) (hJ : J ⊆ C) :
    theta G m T J = msum m T + 4 - 4 * ((#T : ℤ) - #J) - ec G J (A \ T) := by
  have h1 := ec_sdiff_add_right (G := G) hT J
  have h2 : ec G J A = 6 * #J := by
    unfold ec
    rw [sum_congr rfl fun c hc => hX.satC c (hJ hc), sum_const, smul_eq_mul, mul_comm]
  have h3 := ec_comm (G := G) T J
  unfold theta
  omega

/-- `2θ(S) = 2m(T) + 8 - 2κ(S) - g(S)`. -/
lemma two_mul_theta (m : V → ℕ) (T J : Finset V) :
    2 * theta G m T J = 2 * msum m T + 8 - 2 * ((#T : ℤ) - #J) - gv G T J := by
  unfold theta gv
  ring

/-! ### Supermodularity of `θ*` -/

/-- **Supermodularity of `θ*`**: for `S = X'(T)` and `S' = X'(T')`,
`θ*(T ∪ T') + θ*(T ∩ T') ≥ θ*(T) + θ*(T') + e(S - S', S' - S)`, the crossing term counted as in
`theta_union_add_theta_inter`. -/
theorem thetaStar_union_add_inter [DecidableEq V] (m : V → ℕ) (C T T' : Finset V) :
    thetaStar G m C T + thetaStar G m C T' +
        (ec G (T \ T') (cpr G C T' \ cpr G C T) + ec G (T' \ T) (cpr G C T \ cpr G C T') : ℤ) ≤
      thetaStar G m C (T ∪ T') + thetaStar G m C (T ∩ T') := by
  have h := theta_union_add_theta_inter (G := G) m T T' (cpr G C T) (cpr G C T')
  rw [theta_cpr, theta_cpr] at h
  have h1 := theta_le_thetaStar (G := G) m
    (union_subset (cpr_subset (G := G) C T) (cpr_subset (G := G) C T')) (T ∪ T')
  have h2 := theta_le_thetaStar (G := G) m
    ((inter_subset_left (s₂ := cpr G C T')).trans (cpr_subset (G := G) C T)) (T ∩ T')
  linarith

/-- Supermodularity of `θ*` (`thetaStar_union_add_inter`) without the crossing term. -/
lemma thetaStar_add_le [DecidableEq V] (m : V → ℕ) (C T T' : Finset V) :
    thetaStar G m C T + thetaStar G m C T' ≤
      thetaStar G m C (T ∪ T') + thetaStar G m C (T ∩ T') := by
  have := thetaStar_union_add_inter (G := G) m C T T'
  have h0 : (0 : ℤ) ≤ (ec G (T \ T') (cpr G C T' \ cpr G C T) : ℤ) +
      (ec G (T' \ T) (cpr G C T \ cpr G C T') : ℤ) := by positivity
  linarith

/-! ### Values and bounds -/

/-- `θ(∅) = 4`. -/
lemma theta_empty (m : V → ℕ) : theta G m ∅ ∅ = 4 := by
  simp [theta, msum, ec]

/-- If `|T| ≤ 2`, no `c` has three neighbors in `T`, so `θ*(T) = m(T) + 4 - 4|T|`. -/
lemma thetaStar_of_card_le_two (m : V → ℕ) (C : Finset V) {T : Finset V} (hT : #T ≤ 2) :
    thetaStar G m C T = msum m T + 4 - 4 * #T := by
  unfold thetaStar
  have : ∑ c ∈ C, max 0 ((dg G T c : ℤ) - 2) = 0 := by
    refine sum_eq_zero fun c _ => ?_
    have := dg_le_card (G := G) T c
    have : (dg G T c : ℤ) ≤ 2 := by exact_mod_cast (by omega : dg G T c ≤ 2)
    exact max_eq_left (by linarith)
  rw [this, add_zero]

lemma thetaStar_empty (m : V → ℕ) (C : Finset V) : thetaStar G m C ∅ = 4 := by
  rw [thetaStar_of_card_le_two m C (by simp), msum_empty]
  simp

/-- `θ*({a}) = m(a)`. -/
lemma thetaStar_singleton (m : V → ℕ) (C : Finset V) (a : V) :
    thetaStar G m C {a} = m a := by
  rw [thetaStar_of_card_le_two m C (by simp), msum_singleton]
  simp

/-- A two-element set has `θ*(T) = m(T) - 4`, so it is never overloaded when `m(T) ≤ 4`. -/
lemma thetaStar_of_card_eq_two (m : V → ℕ) (C : Finset V) {T : Finset V} (hT : #T = 2) :
    thetaStar G m C T = msum m T - 4 := by
  rw [thetaStar_of_card_le_two m C hT.le, hT]
  ring

/-- Sparsity in edge form: a sub-pair of the block with at least three vertices has
`e(T, J) ≤ 3(|T| + |J|) - 6` (that is, `g ≥ 12`). -/
lemma IsBlock.ec_le_of_three_le {A C : Finset V} (hX : IsBlock G A C) {T J : Finset V} (hT : T ⊆ A)
    (hJ : J ⊆ C) (h3 : 3 ≤ #T + #J) : ec G T J + 6 ≤ 3 * (#T + #J) := by
  have := hX.sparse T hT J hJ h3
  unfold gv at this
  omega

/-- On a sub-pair with at least three vertices, `θ(S) ≤ m(T) - 2 - κ(S)` (this is `g(S) ≥ 12`). -/
theorem theta_le_of_three_le {A C : Finset V} (hX : IsBlock G A C) (m : V → ℕ) {T J : Finset V}
    (hT : T ⊆ A) (hJ : J ⊆ C) (h3 : 3 ≤ #T + #J) :
    theta G m T J ≤ msum m T - 2 - ((#T : ℤ) - #J) := by
  have := hX.ec_le_of_three_le hT hJ h3
  unfold theta
  omega

/-- On a sub-pair with at least three vertices, `3θ(S) ≤ 2m(T) - w(T) - ∂_A(S)`. -/
lemma three_mul_theta_le [DecidableEq V] {A C : Finset V} (hX : IsBlock G A C) (m : V → ℕ)
    {T J : Finset V} (hT : T ⊆ A) (hJ : J ⊆ C) (h3 : 3 ≤ #T + #J) :
    3 * theta G m T J ≤ 2 * msum m T - (wsum G m C T + ec G T (C \ J)) := by
  have h1 := theta_le_of_three_le hX m hT hJ h3
  have h2 := theta_eq_four_add (G := G) m hJ T
  linarith

/-- `θ(S) ≤ 2` on a sub-pair with at least three vertices, when `m(A) = 4` and `m ≤ δ` on `A`. -/
lemma theta_le_two [DecidableEq V] {A C : Finset V} (hX : IsBlock G A C) {m : V → ℕ}
    (hm : msum m A = 4) (hmδ : ∀ a ∈ A, m a + dg G C a ≤ 6) {T J : Finset V} (hT : T ⊆ A)
    (hJ : J ⊆ C) (h3 : 3 ≤ #T + #J) : theta G m T J ≤ 2 := by
  have h1 := theta_le_of_three_le hX m hT hJ h3
  have h2 := theta_eq_four_add (G := G) m hJ T
  have h4 := msum_mono m hT
  have h5 := wsum_nonneg (G := G) hmδ hT
  have h6 : (0 : ℤ) ≤ ec G T (C \ J) := Nat.cast_nonneg _
  omega

/-- `θ*(T) ≤ 2` when `|T| ≥ 3` (`theta_le_two` at `X'(T)`). -/
lemma thetaStar_le_two [DecidableEq V] {A C : Finset V} (hX : IsBlock G A C) {m : V → ℕ}
    (hm : msum m A = 4) (hmδ : ∀ a ∈ A, m a + dg G C a ≤ 6) {T : Finset V} (hT : T ⊆ A)
    (h3 : 3 ≤ #T) : thetaStar G m C T ≤ 2 := by
  rw [← theta_cpr]
  exact theta_le_two hX hm hmδ hT (cpr_subset C T) (by omega)

/-- **The bounds on `κ`**: a sub-pair `S` with at least three vertices and `θ(S) ≥ 1` has
`-1 ≤ κ(S) ≤ m(T) - 3`. -/
lemma kappa_bounds [DecidableEq V] {A C : Finset V} (hX : IsBlock G A C) {m : V → ℕ}
    (hmδ : ∀ a ∈ A, m a + dg G C a ≤ 6) {T J : Finset V} (hT : T ⊆ A) (hJ : J ⊆ C)
    (h3 : 3 ≤ #T + #J) (h1 : 1 ≤ theta G m T J) :
    -1 ≤ (#T : ℤ) - #J ∧ (#T : ℤ) - #J ≤ msum m T - 3 := by
  have h2 := theta_le_of_three_le hX m hT hJ h3
  have h4 := theta_eq_four_add (G := G) m hJ T
  have h5 := wsum_nonneg (G := G) hmδ hT
  have h6 : (0 : ℤ) ≤ ec G T (C \ J) := Nat.cast_nonneg _
  omega

/-- An overloaded `T` with `|T| ≥ 3` and `m(T) ≤ 4` has `C'(T) ≠ ∅`. -/
lemma cpr_nonempty {C T : Finset V} {m : V → ℕ} (hm : msum m T ≤ 4) (h3 : 3 ≤ #T)
    (h1 : 1 ≤ thetaStar G m C T) : (cpr G C T).Nonempty := by
  rw [nonempty_iff_ne_empty]
  intro h0
  rw [← theta_cpr, h0] at h1
  have h2 : ec G T ∅ = 0 := by simp [ec, dg]
  unfold theta at h1
  rw [h2] at h1
  simp only [card_empty, CharP.cast_eq_zero] at h1
  omega

/-- An overloaded `T` with `|T| ≥ 3` has `m(T) ≥ 2`, and `X'(T)` has
`-1 ≤ κ ≤ m(T) - 3`. -/
lemma two_le_msum [DecidableEq V] {A C : Finset V} (hX : IsBlock G A C) {m : V → ℕ}
    (hmδ : ∀ a ∈ A, m a + dg G C a ≤ 6) {T : Finset V} (hT : T ⊆ A)
    (h3 : 3 ≤ #T) (h1 : 1 ≤ thetaStar G m C T) :
    2 ≤ msum m T ∧ -1 ≤ (#T : ℤ) - #(cpr G C T) ∧ (#T : ℤ) - #(cpr G C T) ≤ msum m T - 3 := by
  rw [← theta_cpr] at h1
  have := kappa_bounds hX hmδ hT (cpr_subset C T) (by omega) h1
  have hm' := msum_mono m hT
  refine ⟨by omega, this.1, this.2⟩

/-- For the sub-pair `{a} ∪ J = ({a}, J)`: `θ({a} ∪ J) = m(a) - 2|J| + e(a, J) ≤ m(a) - |J|`. -/
lemma theta_singleton (m : V → ℕ) (a : V) (J : Finset V) :
    theta G m {a} J = m a - 2 * #J + dg G J a ∧ theta G m {a} J ≤ m a - #J := by
  have h1 : ec G {a} J = dg G J a := by
    unfold ec
    rw [sum_singleton]
  have h2 := dg_le_card (G := G) J a
  unfold theta
  rw [h1, msum_singleton, card_singleton]
  constructor
  · ring
  · push_cast
    omega

/-! ### Overloaded and under-supplied sets -/

/-- `dem(A1) - m(A1) = θ*(A - A1)` for `A1 ⊆ A`, because `e(c, A) = 6` and
`min(4, 6 - x) = 4 - (x - 2)^+` for `0 ≤ x ≤ 6`, `|A| = |C| + 2` and `m(A) = 4`. -/
theorem dem_sub_msum {A C : Finset V} [DecidableEq V] (hX : IsBlock G A C) {m : V → ℕ}
    (hm : msum m A = 4) {A1 : Finset V} (hA1 : A1 ⊆ A) :
    dem G C A1 - msum m A1 = thetaStar G m C (A \ A1) := by
  unfold dem thetaStar
  have hc : ∀ c ∈ C,
      (min 4 (dg G A1 c) : ℤ) = 4 - max 0 ((dg G (A \ A1) c : ℤ) - 2) := by
    intro c hc
    have h1 := dg_sdiff_add (G := G) hA1 c
    have h2 := hX.satC c hc
    have h3 : (dg G (A \ A1) c : ℤ) + dg G A1 c = 6 := by exact_mod_cast h1.trans h2
    rcases le_total (dg G A1 c) 4 with h4 | h4
    · have h4' : (dg G A1 c : ℤ) ≤ 4 := by exact_mod_cast h4
      rw [min_eq_right h4', max_eq_right (by linarith)]
      ring_nf
      linarith
    · have h4' : (4 : ℤ) ≤ dg G A1 c := by exact_mod_cast h4
      rw [min_eq_left h4', max_eq_left (by linarith)]
      ring
  rw [sum_congr rfl hc, sum_sub_distrib, sum_const, nsmul_eq_mul]
  have h1 := msum_sdiff_add m hA1
  have h2 := card_sdiff_add_card_eq_card hA1
  have h3 := hX.card
  omega

/-- **Overloaded iff under-supplied**: for `A1 ⊆ A`, the set `A1` is under-supplied
(`m(A1) < dem(A1)`) iff its complement `T = A - A1` is overloaded (`θ*(T) ≥ 1`). -/
theorem overloaded_iff {A C : Finset V} [DecidableEq V] (hX : IsBlock G A C) {m : V → ℕ}
    (hm : msum m A = 4) {A1 : Finset V} (hA1 : A1 ⊆ A) :
    msum m A1 < dem G C A1 ↔ 1 ≤ thetaStar G m C (A \ A1) := by
  rw [← dem_sub_msum hX hm hA1]
  omega

/-- The conclusion of KL1 in demand form from its form in `θ*`: if `p ∈ A` lies in no overloaded
set, then no `A1 ⊆ A - p` is under-supplied. -/
theorem exists_good_of_thetaStar {A C : Finset V} [DecidableEq V] (hX : IsBlock G A C)
    {m : V → ℕ} (hm : msum m A = 4)
    (h : ∃ p ∈ A, ∀ T ⊆ A, p ∈ T → thetaStar G m C T ≤ 0) :
    ∃ p ∈ A, ∀ A1 ⊆ A.erase p, dem G C A1 ≤ ∑ a ∈ A1, (m a : ℤ) := by
  obtain ⟨p, hp, hT⟩ := h
  refine ⟨p, hp, fun A1 hA1 => ?_⟩
  have hA1A : A1 ⊆ A := hA1.trans (erase_subset p A)
  have hpA1 : p ∉ A1 := fun h => (mem_erase.1 (hA1 h)).1 rfl
  have h1 := hT (A \ A1) sdiff_subset (mem_sdiff.2 ⟨hp, hpA1⟩)
  have h2 := dem_sub_msum hX hm hA1A
  change dem G C A1 ≤ msum m A1
  omega

/-! ### The data of KL1 -/

/-- In a block, `e(A, C) = 6|C|`: every `c ∈ C` has its six neighbors in `A`. -/
lemma IsBlock.ec_eq_six_mul {A C : Finset V} (hX : IsBlock G A C) : ec G A C = 6 * #C := by
  rw [ec_comm]
  unfold ec
  rw [sum_congr rfl fun c hc => hX.satC c hc, sum_const, smul_eq_mul, mul_comm]

variable (G) in
/-- The hypotheses of `kl1` other than covering: a 2-block `(A, C)` and multiplicities `m` with
`m(A) = 4` and `m(a) ≤ δ_a = 6 - d_a`. -/
structure KLData (A C : Finset V) (m : V → ℕ) : Prop where
  block : IsBlock G A C
  msum_eq : msum m A = 4
  le_delta : ∀ a ∈ A, m a + dg G C a ≤ 6

namespace KLData

variable {A C : Finset V} {m : V → ℕ}

/-- `m(T) ≤ 4` on subsets of `A`. -/
lemma msum_le (hK : KLData G A C m) {T : Finset V} (hT : T ⊆ A) : msum m T ≤ 4 :=
  hK.msum_eq ▸ msum_mono m hT

/-- `m(a) ≤ δ_a ≤ 3`. -/
lemma m_le_three (hK : KLData G A C m) {a : V} (ha : a ∈ A) : m a ≤ 3 := by
  have h1 := hK.le_delta a ha
  have h2 := hK.block.three_le a ha
  omega

/-- `w(A) = 12 - 4 = 8`: `Σ_{a ∈ A} δ_a = 6 |A| - e(A, C) = 12` and `m(A) = 4`. -/
lemma wsum_eq_eight (hK : KLData G A C m) : wsum G m C A = 8 := by
  rw [wsum_eq, hK.block.ec_eq_six_mul, hK.msum_eq, hK.block.card]
  push_cast
  ring

/-- `Σ_{a ∈ A} (2m(a) - w(a)) = 0`, written as `Σ_{a ∈ A} (3m(a) - 6 + d_a) = 0` (used in
`KL1Merge.lean`). -/
lemma sum_f_eq_zero (hK : KLData G A C m) :
    ∑ a ∈ A, (3 * (m a : ℤ) - 6 + dg G C a) = 0 := by
  have h1 := hK.block.ec_eq_six_mul
  have h2 := hK.msum_eq
  have h3 := hK.block.card
  unfold msum at h2
  unfold ec at h1
  rw [sum_add_distrib, sum_sub_distrib, ← mul_sum, h2, sum_const, nsmul_eq_mul, ← Nat.cast_sum,
    h1]
  push_cast
  rw [h3]
  push_cast
  ring

lemma wsum_nonneg' (hK : KLData G A C m) {T : Finset V} (hT : T ⊆ A) : 0 ≤ wsum G m C T :=
  wsum_nonneg hK.le_delta hT

end KLData

end Erdos585.QB5
