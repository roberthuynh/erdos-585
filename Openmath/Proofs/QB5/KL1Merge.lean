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
import Openmath.Proofs.QB5.Block

/-!
# QB(5): merging maximal overloaded sets

The setting of `Block.lean`: a block `(A, C)` (`IsBlock`) and multiplicities `m : V → ℕ` with
`m(A) = 4` and `m(a) + d_a ≤ 6` for `a ∈ A` (`KLData`), where `d_a` is the number of neighbors
of `a` in `C`. A subset `T ⊆ A` is *overloaded* if `θ*(T) ≥ 1`; by `overloaded_iff`, this says
that `A - T` is under-supplied, `m(A - T) < dem(A - T)` (`dem`).

Notation: `e(x, S)` is the number of neighbors of a vertex `x` in `S` (`dg G S x`), and `e(T, J)`
the number of adjacent pairs in `T × J` (`ec`). For `T ⊆ A` and `J ⊆ C`:
`m(T) = Σ_{a ∈ T} m(a)` (`msum`), `w(T) = Σ_{a ∈ T} (6 - d_a - m(a))` (`wsum`),
`θ(T, J) = m(T) + 4 - 4|T| - 2|J| + e(T, J)` (`theta`),
`θ*(T) = m(T) + 4 - 4|T| + Σ_{c ∈ C} (e(c, T) - 2)^+` (`thetaStar`),
`C'(T) = {c ∈ C : e(c, T) ≥ 3}` (`cpr`) and the pair `X'(T) = (T, C'(T))`. For a pair
`S = (T, J)`, `g(S) = 6 (|T| + |J|) - 2 e(T, J)` (`gv`) and `∂_A(S) = e(T, C - J)`. A *big
member* of the family of maximal overloaded sets is one with at least three vertices.

* `merge_theta_inter`, `merge_card_ne_two`, `merge_N1`, `merge_N3`: if two overloaded sets `T`,
  `T'` have `θ*(T ∪ T') ≤ 0`, they are disjoint, meet in one vertex `a` with
  `m(a) ≥ θ*(T) + θ*(T') + |C'(T) ∩ C'(T')|`, or share at least three vertices with
  `θ*(T ∩ T') = 2` and `θ*(T) = θ*(T') = 1`.
* `IsMaxOver`: the inclusion-maximal overloaded subsets of `A`.
* `exists_hub_pair`: if every vertex of `A` lies in an overloaded set, two distinct maximal
  overloaded sets share at least three vertices.

The proof of `exists_hub_pair` runs over the whole family of maximal overloaded sets. Its weight
count is the double count `sum_sum_eq_sum_filter` of `Σ_T Σ_{v ∈ T} (3m(v) - 6 + e(v, C'(T)))`
over the big members, against `Σ_{v ∈ A} (3m(v) - 6 + d_v) = 0` (`KLData.sum_f_eq_zero`).
-/

open Finset

namespace Erdos585.QB5

open QB4

variable {V : Type*} {G : SimpleGraph V} [DecidableRel G.Adj] [DecidableEq V]
  {A C : Finset V} {m : V → ℕ}

/-! ### Merging two overloaded sets -/

/-- If `θ*(T ∪ T') ≤ 0`, then `θ(X'(T) ∩ X'(T')) ≥ θ*(T) + θ*(T')`, where the intersection of
pairs is taken sidewise: `X'(T) ∩ X'(T') = (T ∩ T', C'(T) ∩ C'(T'))`. -/
theorem merge_theta_inter {T T' : Finset V} (hU : thetaStar G m C (T ∪ T') ≤ 0) :
    thetaStar G m C T + thetaStar G m C T' ≤
      theta G m (T ∩ T') (cpr G C T ∩ cpr G C T') := by
  have h := theta_union_add_theta_inter (G := G) m T T' (cpr G C T) (cpr G C T')
  rw [theta_cpr, theta_cpr] at h
  have h1 := theta_le_thetaStar (G := G) m
    (union_subset (cpr_subset (G := G) C T) (cpr_subset (G := G) C T')) (T ∪ T')
  have h0 : (0 : ℤ) ≤ (ec G (T \ T') (cpr G C T' \ cpr G C T) : ℤ) +
      (ec G (T' \ T) (cpr G C T \ cpr G C T') : ℤ) := by positivity
  linarith

/-- `θ*(T ∩ T') ≥ θ*(T) + θ*(T')` when `θ*(T ∪ T') ≤ 0`. -/
lemma merge_thetaStar_inter {T T' : Finset V} (hU : thetaStar G m C (T ∪ T') ≤ 0) :
    thetaStar G m C T + thetaStar G m C T' ≤ thetaStar G m C (T ∩ T') :=
  (merge_theta_inter hU).trans (theta_le_thetaStar (G := G) m
    ((inter_subset_left (s₂ := cpr G C T')).trans (cpr_subset (G := G) C T)) _)

/-- Two overloaded sets with `θ*(T ∪ T') ≤ 0` never share exactly two vertices (a two-element
set `S` has `θ*(S) = m(S) - 4 ≤ 0`). -/
lemma merge_card_ne_two (hK : KLData G A C m) {T T' : Finset V} (hT : T ⊆ A)
    (h1 : 1 ≤ thetaStar G m C T) (h1' : 1 ≤ thetaStar G m C T')
    (hU : thetaStar G m C (T ∪ T') ≤ 0) : #(T ∩ T') ≠ 2 := by
  intro h2
  have h3 := merge_thetaStar_inter hU
  rw [thetaStar_of_card_eq_two m C h2] at h3
  have h4 := hK.msum_le ((inter_subset_left (s₂ := T')).trans hT)
  linarith

/-- Overloaded `T`, `T'` with `θ*(T ∪ T') ≤ 0` sharing at least three vertices have
`θ*(T ∩ T') = 2` and `θ*(T) = θ*(T') = 1`. -/
lemma merge_N3 (hK : KLData G A C m) {T T' : Finset V} (hT : T ⊆ A)
    (h1 : 1 ≤ thetaStar G m C T) (h1' : 1 ≤ thetaStar G m C T')
    (hU : thetaStar G m C (T ∪ T') ≤ 0) (h3 : 3 ≤ #(T ∩ T')) :
    thetaStar G m C (T ∩ T') = 2 ∧ thetaStar G m C T = 1 ∧ thetaStar G m C T' = 1 := by
  have h4 := merge_thetaStar_inter hU
  have h5 := thetaStar_le_two hK.block hK.msum_eq hK.le_delta (inter_subset_left.trans hT) h3
  omega

/-- If `θ*(T ∪ T') ≤ 0` and `T ∩ T' = {a}`, then `m(a) ≥ θ*(T) + θ*(T') + |C'(T) ∩ C'(T')|`
(`theta_singleton` at the pair `({a}, C'(T) ∩ C'(T'))`). -/
lemma merge_N1 {T T' : Finset V} (hU : thetaStar G m C (T ∪ T') ≤ 0) {a : V}
    (ha : T ∩ T' = {a}) :
    thetaStar G m C T + thetaStar G m C T' + #(cpr G C T ∩ cpr G C T') ≤ m a := by
  have h := merge_theta_inter hU
  rw [ha] at h
  have := (theta_singleton (G := G) m a (cpr G C T ∩ cpr G C T')).2
  linarith

/-! ### The family of maximal overloaded sets -/

variable (G) in
/-- `T` is an inclusion-maximal overloaded subset of `A`. -/
def IsMaxOver (m : V → ℕ) (A C T : Finset V) : Prop :=
  T ⊆ A ∧ 1 ≤ thetaStar G m C T ∧ ∀ T' ⊆ A, T ⊆ T' → 1 ≤ thetaStar G m C T' → T' = T

/-- Every overloaded subset of `A` lies in a maximal one. -/
lemma exists_isMaxOver {T : Finset V} (hT : T ⊆ A) (h1 : 1 ≤ thetaStar G m C T) :
    ∃ T', T ⊆ T' ∧ IsMaxOver G m A C T' := by
  obtain ⟨T', hT'mem, hmax⟩ := exists_max_image
    (A.powerset.filter fun T' => T ⊆ T' ∧ 1 ≤ thetaStar G m C T') card
    ⟨T, mem_filter.2 ⟨mem_powerset.2 hT, Subset.rfl, h1⟩⟩
  rw [mem_filter, mem_powerset] at hT'mem
  refine ⟨T', hT'mem.2.1, hT'mem.1, hT'mem.2.2, fun T'' hT'' hsub h1'' => ?_⟩
  have := hmax T'' (mem_filter.2 ⟨mem_powerset.2 hT'', hT'mem.2.1.trans hsub, h1''⟩)
  exact (eq_of_subset_of_card_le hsub this).symm

namespace IsMaxOver

variable {T T' : Finset V}

/-- Two distinct maximal overloaded sets have a union that is not overloaded. -/
lemma union_le (hT : IsMaxOver G m A C T) (hT' : IsMaxOver G m A C T') (hne : T ≠ T') :
    thetaStar G m C (T ∪ T') ≤ 0 := by
  by_contra h
  have h1 : 1 ≤ thetaStar G m C (T ∪ T') := by omega
  have e1 := hT.2.2 (T ∪ T') (union_subset hT.1 hT'.1) subset_union_left h1
  have e2 := hT'.2.2 (T ∪ T') (union_subset hT.1 hT'.1) subset_union_right h1
  exact hne (e1.symm.trans e2)

omit [DecidableEq V] in
/-- A maximal overloaded set is empty, a singleton `{u}` with `m(u) ≥ 1`, or has at least three
vertices (`thetaStar_singleton`, `thetaStar_of_card_eq_two`). -/
lemma cases (hK : KLData G A C m) (hT : IsMaxOver G m A C T) :
    T = ∅ ∨ (∃ u, T = {u} ∧ 1 ≤ m u) ∨ 3 ≤ #T := by
  rcases lt_or_ge #T 3 with h | h
  · have h1 := hT.2.1
    interval_cases hc : #T
    · exact Or.inl (card_eq_zero.1 hc)
    · obtain ⟨u, rfl⟩ := card_eq_one.1 hc
      rw [thetaStar_singleton] at h1
      exact Or.inr (Or.inl ⟨u, rfl, by exact_mod_cast h1⟩)
    · rw [thetaStar_of_card_eq_two m C hc] at h1
      have := hK.msum_le hT.1
      omega
  · exact Or.inr (Or.inr h)

/-- Two distinct maximal overloaded sets sharing fewer than three vertices are disjoint or meet
in one vertex `v` with `m(v) ≥ θ*(T) + θ*(T') + |C'(T) ∩ C'(T')|` (`merge_card_ne_two`,
`merge_N1`). -/
lemma inter_of_lt (hK : KLData G A C m) (hT : IsMaxOver G m A C T)
    (hT' : IsMaxOver G m A C T') (hne : T ≠ T') (h3 : #(T ∩ T') < 3) :
    T ∩ T' = ∅ ∨ ∃ v, T ∩ T' = {v} ∧
      thetaStar G m C T + thetaStar G m C T' + #(cpr G C T ∩ cpr G C T') ≤ m v := by
  have hU := hT.union_le hT' hne
  have h2 := merge_card_ne_two hK hT.1 hT.2.1 hT'.2.1 hU
  interval_cases hc : #(T ∩ T')
  · exact Or.inl (card_eq_zero.1 hc)
  · obtain ⟨v, hv⟩ := card_eq_one.1 hc
    exact Or.inr ⟨v, hv, merge_N1 hU hv⟩
  · exact absurd rfl h2

end IsMaxOver

/-! ### Two maximal overloaded sets that share three vertices -/

/-- Three subsets of `A` that pairwise meet in `{v}` cannot all contain three neighbors of one
`c ∈ C`: that would give `c` at least seven neighbors in `A`. -/
private lemma three_cpr_false (hX : IsBlock G A C) {T₁ T₂ T₃ : Finset V} (h₁ : T₁ ⊆ A)
    (h₂ : T₂ ⊆ A) (h₃ : T₃ ⊆ A) {v c : V} (h12 : T₁ ∩ T₂ = {v}) (h13 : T₁ ∩ T₃ = {v})
    (h23 : T₂ ∩ T₃ = {v}) (hc : c ∈ C) (hc₁ : 3 ≤ dg G T₁ c) (hc₂ : 3 ≤ dg G T₂ c)
    (hc₃ : 3 ≤ dg G T₃ c) : False := by
  have e1 := dg_union_add_dg_inter (G := G) T₁ T₂ c
  have e2 := dg_union_add_dg_inter (G := G) (T₁ ∪ T₂) T₃ c
  have hi : (T₁ ∪ T₂) ∩ T₃ = {v} := by rw [union_inter_distrib_right, h13, h23, union_self]
  rw [h12] at e1
  rw [hi] at e2
  have hv := dg_le_card (G := G) ({v} : Finset V) c
  rw [card_singleton] at hv
  have hA := dg_mono (G := G) (union_subset (union_subset h₁ h₂) h₃) c
  rw [hX.satC c hc] at hA
  omega

/-- Double counting over a family of subsets of `A`. -/
private lemma sum_sum_eq_sum_filter {ℱ : Finset (Finset V)} (hℱ : ∀ T ∈ ℱ, T ⊆ A)
    (F : V → Finset V → ℤ) :
    ∑ T ∈ ℱ, ∑ v ∈ T, F v T = ∑ v ∈ A, ∑ T ∈ ℱ.filter (fun T => v ∈ T), F v T := by
  have h : ∀ T ∈ ℱ, ∑ v ∈ T, F v T = ∑ v ∈ A, if v ∈ T then F v T else 0 := by
    intro T hT
    rw [← sum_filter, filter_mem_eq_inter, inter_eq_right.2 (hℱ T hT)]
  rw [sum_congr rfl h, sum_comm]
  exact sum_congr rfl fun v _ => (sum_filter _ _).symm

/-- If every `c ∈ C` lies in at most `b` of the sets `t T ⊆ C`, then `Σ_T e(v, t T) ≤ b d_v`. -/
private lemma sum_dg_le_mul {ℱ : Finset (Finset V)} (t : Finset V → Finset V)
    (ht : ∀ T ∈ ℱ, t T ⊆ C) (b : ℕ) (hb : ∀ c ∈ C, #(ℱ.filter (fun T => c ∈ t T)) ≤ b)
    (v : V) : ∑ T ∈ ℱ, dg G (t T) v ≤ b * dg G C v := by
  have e1 : ∀ T ∈ ℱ, dg G (t T) v = ∑ c ∈ C.filter (G.Adj v), if c ∈ t T then 1 else 0 := by
    intro T hT
    unfold dg
    rw [← card_filter]
    congr 1
    ext c
    simp only [mem_filter]
    constructor
    · rintro ⟨hc, hadj⟩
      exact ⟨⟨ht T hT hc, hadj⟩, hc⟩
    · rintro ⟨⟨_, hadj⟩, hc⟩
      exact ⟨hc, hadj⟩
  calc ∑ T ∈ ℱ, dg G (t T) v
      = ∑ T ∈ ℱ, ∑ c ∈ C.filter (G.Adj v), if c ∈ t T then 1 else 0 := sum_congr rfl e1
    _ = ∑ c ∈ C.filter (G.Adj v), ∑ T ∈ ℱ, if c ∈ t T then 1 else 0 := sum_comm
    _ = ∑ c ∈ C.filter (G.Adj v), #(ℱ.filter (fun T => c ∈ t T)) :=
        sum_congr rfl fun c _ => (card_filter _ _).symm
    _ ≤ ∑ _c ∈ C.filter (G.Adj v), b := sum_le_sum fun c hc => hb c (mem_filter.1 hc).1
    _ = b * dg G C v := by
        rw [sum_const, smul_eq_mul, mul_comm]
        rfl

omit [DecidableEq V] in
/-- `Σ_{v ∈ T} (3m(v) - 6 + e(v, C'(T))) = 3θ*(T) + g(X'(T)) - 12`. The left side is the term of
`T` in the weight count of `exists_hub_pair`, and it equals `2m(T) - w(T) - ∂_A(X'(T))`. -/
private lemma sum_F_eq (m : V → ℕ) (C T : Finset V) :
    ∑ v ∈ T, (3 * (m v : ℤ) - 6 + dg G (cpr G C T) v) =
      3 * thetaStar G m C T + gv G T (cpr G C T) - 12 := by
  have e1 : (ec G T (cpr G C T) : ℤ) = ∑ v ∈ T, (dg G (cpr G C T) v : ℤ) := by
    unfold ec
    push_cast
    rfl
  have e2 : ∑ v ∈ T, (3 * (m v : ℤ) - 6 + dg G (cpr G C T) v) =
      3 * msum m T - 6 * #T + ∑ v ∈ T, (dg G (cpr G C T) v : ℤ) := by
    unfold msum
    rw [sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_const, nsmul_eq_mul]
    ring
  rw [e2, ← theta_cpr]
  unfold theta gv
  rw [e1]
  ring

/-- Under "no two distinct maximal overloaded sets share three vertices", two distinct ones
containing `v` meet exactly in `{v}`, and `m(v) ≥ θ*(T) + θ*(T') + |C'(T) ∩ C'(T')|`
(`IsMaxOver.inter_of_lt`). -/
private lemma inter_eq_singleton (hK : KLData G A C m)
    (hno : ∀ T₁ T₂, IsMaxOver G m A C T₁ → IsMaxOver G m A C T₂ → T₁ ≠ T₂ → #(T₁ ∩ T₂) < 3)
    {T T' : Finset V} (hT : IsMaxOver G m A C T) (hT' : IsMaxOver G m A C T') (hne : T ≠ T')
    {v : V} (hv : v ∈ T) (hv' : v ∈ T') :
    T ∩ T' = {v} ∧
      thetaStar G m C T + thetaStar G m C T' + #(cpr G C T ∩ cpr G C T') ≤ m v := by
  have hvi : v ∈ T ∩ T' := mem_inter.2 ⟨hv, hv'⟩
  rcases hT.inter_of_lt hK hT' hne (hno T T' hT hT' hne) with h | ⟨w, hw, hle⟩
  · rw [h] at hvi
    simp at hvi
  · rw [hw, mem_singleton] at hvi
    subst hvi
    exact ⟨hw, hle⟩

/-- If every vertex of `A` lies in an overloaded set, a vertex `v` in no maximal overloaded set
with at least three elements lies in the maximal overloaded set `{v}`, so `m(v) ≥ 1`. -/
lemma one_le_m_of_not_big (hK : KLData G A C m)
    (hall : ∀ p ∈ A, ∃ T ⊆ A, p ∈ T ∧ 1 ≤ thetaStar G m C T) {v : V} (hv : v ∈ A)
    (hnb : ∀ T, IsMaxOver G m A C T → 3 ≤ #T → v ∉ T) : 1 ≤ m v := by
  obtain ⟨T, hTA, hvT, h1⟩ := hall v hv
  obtain ⟨T', hsub, hT'⟩ := exists_isMaxOver hTA h1
  have hvT' := hsub hvT
  rcases hT'.cases hK with h | ⟨u, hu, hmu⟩ | h
  · rw [h] at hvT'
    simp at hvT'
  · rw [hu, mem_singleton] at hvT'
    subst hvT'
    exact hmu
  · exact absurd hvT' (hnb T' hT' h)

/-- If every vertex of `A` lies in an overloaded set, two distinct maximal overloaded sets share
at least three vertices. -/
theorem exists_hub_pair (hK : KLData G A C m)
    (hall : ∀ p ∈ A, ∃ T ⊆ A, p ∈ T ∧ 1 ≤ thetaStar G m C T) :
    ∃ T₁ T₂, IsMaxOver G m A C T₁ ∧ IsMaxOver G m A C T₂ ∧ T₁ ≠ T₂ ∧ 3 ≤ #(T₁ ∩ T₂) := by
  classical
  by_contra! hno
  -- the big members of the family
  set ℬ : Finset (Finset V) := A.powerset.filter (fun T => IsMaxOver G m A C T ∧ 3 ≤ #T)
    with hℬ
  have memℬ : ∀ T, T ∈ ℬ ↔ IsMaxOver G m A C T ∧ 3 ≤ #T := fun T => by
    rw [hℬ, mem_filter, mem_powerset]
    exact ⟨fun h => h.2, fun h => ⟨h.1.1, h⟩⟩
  have hℬA : ∀ T ∈ ℬ, T ⊆ A := fun T hT => ((memℬ T).1 hT).1.1
  -- the weight identity: the double count, and `Σ_{v ∈ A} (3m(v) - 6 + d_v) = 0`
  have hid := sum_sum_eq_sum_filter hℬA
    (fun v T => 3 * (m v : ℤ) - 6 + dg G (cpr G C T) v)
  have hf0 := hK.sum_f_eq_zero
  -- lower bound for each big member: 2m(T) - w(T) - ∂_A(X'(T)) ≥ 3 + (g(X'(T)) - 12)
  have hlow : ∀ T ∈ ℬ, 3 + (gv G T (cpr G C T) - 12) ≤
      ∑ v ∈ T, (3 * (m v : ℤ) - 6 + dg G (cpr G C T) v) := by
    intro T hT
    obtain ⟨hTm, hT3⟩ := (memℬ T).1 hT
    have e := sum_F_eq (G := G) m C T
    have h1 := hTm.2.1
    linarith
  have hgnn : ∀ T ∈ ℬ, 0 ≤ gv G T (cpr G C T) - 12 := fun T hT => by
    obtain ⟨hTm, hT3⟩ := (memℬ T).1 hT
    have := hK.block.sparse T hTm.1 (cpr G C T) (cpr_subset C T) (by omega)
    linarith
  -- the bound at a vertex that is not shared by two big members with `m = 3`
  have hvert : ∀ v ∈ A, ¬ (2 ≤ #(ℬ.filter (fun T => v ∈ T)) ∧ m v = 3) →
      ∑ T ∈ ℬ.filter (fun T => v ∈ T), (3 * (m v : ℤ) - 6 + dg G (cpr G C T) v) ≤
        3 * (m v : ℤ) - 6 + dg G C v := by
    intro v hv hnb
    have hd3 := hK.block.three_le v hv
    have hm3 := hK.m_le_three hv
    have hsplit : ∑ T ∈ ℬ.filter (fun T => v ∈ T), (3 * (m v : ℤ) - 6 + dg G (cpr G C T) v) =
        (#(ℬ.filter (fun T => v ∈ T)) : ℤ) * (3 * (m v : ℤ) - 6) +
          ∑ T ∈ ℬ.filter (fun T => v ∈ T), (dg G (cpr G C T) v : ℤ) := by
      rw [sum_add_distrib, sum_const, nsmul_eq_mul]
    rw [hsplit]
    rcases Nat.lt_or_ge #(ℬ.filter (fun T => v ∈ T)) 1 with hk | hk
    · -- `v` lies in no big member, so `m(v) ≥ 1` (`one_le_m_of_not_big`)
      have hk0 : ℬ.filter (fun T => v ∈ T) = ∅ := card_eq_zero.1 (by omega)
      rw [hk0, sum_empty, card_empty]
      have h1 : 1 ≤ m v := one_le_m_of_not_big hK hall hv fun T hT hT3 hvT => by
        have : T ∈ ℬ.filter (fun T => v ∈ T) := mem_filter.2 ⟨(memℬ T).2 ⟨hT, hT3⟩, hvT⟩
        rw [hk0] at this
        simp at this
      push_cast
      omega
    · -- the sets `C'(T)`, `v ∈ T`, are pairwise disjoint (or there is only one)
      have hdisj : ∑ T ∈ ℬ.filter (fun T => v ∈ T), dg G (cpr G C T) v ≤ 1 * dg G C v := by
        refine sum_dg_le_mul (fun T => cpr G C T) (fun T _ => cpr_subset C T) 1
          (fun c _ => ?_) v
        rw [card_le_one]
        intro T₁ h₁ T₂ h₂
        by_contra hne
        rw [mem_filter, mem_filter] at h₁ h₂
        obtain ⟨⟨hT₁ℬ, hvT₁⟩, hc₁⟩ := h₁
        obtain ⟨⟨hT₂ℬ, hvT₂⟩, hc₂⟩ := h₂
        have hT₁m := ((memℬ _).1 hT₁ℬ).1
        have hT₂m := ((memℬ _).1 hT₂ℬ).1
        obtain ⟨-, hle⟩ := inter_eq_singleton hK hno hT₁m hT₂m hne hvT₁ hvT₂
        have hcc : 0 < #(cpr G C T₁ ∩ cpr G C T₂) := card_pos.2 ⟨c, mem_inter.2 ⟨hc₁, hc₂⟩⟩
        have h2 : 1 < #(ℬ.filter (fun T => v ∈ T)) :=
          one_lt_card.2 ⟨T₁, mem_filter.2 ⟨hT₁ℬ, hvT₁⟩, T₂, mem_filter.2 ⟨hT₂ℬ, hvT₂⟩, hne⟩
        have hm2 : m v ≠ 3 := fun h => hnb ⟨h2, h⟩
        have h1 := hT₁m.2.1
        have h1' := hT₂m.2.1
        omega
      have hdisj' : ∑ T ∈ ℬ.filter (fun T => v ∈ T), (dg G (cpr G C T) v : ℤ) ≤ dg G C v := by
        rw [one_mul] at hdisj
        exact_mod_cast hdisj
      have hkm : (#(ℬ.filter (fun T => v ∈ T)) : ℤ) * (3 * (m v : ℤ) - 6) ≤ 3 * (m v : ℤ) - 6 := by
        by_cases hmv : m v = 3
        · have : #(ℬ.filter (fun T => v ∈ T)) = 1 := by
            by_contra h
            exact hnb ⟨by omega, hmv⟩
          rw [this]
          simp
        · have hx : 3 * (m v : ℤ) - 6 ≤ 0 := by omega
          have hk1 : (1 : ℤ) ≤ #(ℬ.filter (fun T => v ∈ T)) := by exact_mod_cast hk
          have := mul_le_mul_of_nonpos_right hk1 hx
          linarith
      linarith
  by_cases hbad : ∃ v₀ ∈ A, 2 ≤ #(ℬ.filter (fun T => v₀ ∈ T)) ∧ m v₀ = 3
  · -- a vertex `v₀` with `m(v₀) = 3` shared by two big members
    obtain ⟨v₀, hv₀, hk₀, hm₀⟩ := hbad
    have hd₀ : dg G C v₀ = 3 := by
      have := hK.le_delta v₀ hv₀
      have := hK.block.three_le v₀ hv₀
      omega
    -- every other vertex has `m ≤ 1`, so the bound applies there
    have hother : ∀ v ∈ A.erase v₀,
        ∑ T ∈ ℬ.filter (fun T => v ∈ T), (3 * (m v : ℤ) - 6 + dg G (cpr G C T) v) ≤
          3 * (m v : ℤ) - 6 + dg G C v := by
      intro v hv
      obtain ⟨hne, hvA⟩ := mem_erase.1 hv
      refine hvert v hvA fun ⟨_, hm⟩ => ?_
      have hsub : ({v, v₀} : Finset V) ⊆ A := by
        intro x hx
        rw [mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact hvA
        · exact hv₀
      have h4 := hK.msum_le hsub
      rw [msum, sum_pair hne] at h4
      omega
    -- every big member contains `v₀`, since it has `m(T) ≥ 2`
    have hall₀ : ∀ T ∈ ℬ, v₀ ∈ T := by
      intro T hT
      obtain ⟨hTm, hT3⟩ := (memℬ T).1 hT
      by_contra hv₀T
      have h2 := (two_le_msum hK.block hK.le_delta hTm.1 hT3 hTm.2.1).1
      have h3 : msum m T ≤ msum m (A.erase v₀) :=
        msum_mono m fun x hx => mem_erase.2 ⟨fun h => hv₀T (h ▸ hx), hTm.1 hx⟩
      have h4 : msum m (A.erase v₀) + m v₀ = msum m A := by
        unfold msum
        exact sum_erase_add A _ hv₀
      have h5 := hK.msum_eq
      rw [hm₀] at h4
      push_cast at h4
      omega
    have hℬv₀ : ℬ.filter (fun T => v₀ ∈ T) = ℬ := filter_true_of_mem hall₀
    rw [hℬv₀] at hk₀
    -- the identity and the bounds at the vertices
    have hsum : ∑ v ∈ A, ∑ T ∈ ℬ.filter (fun T => v ∈ T),
        (3 * (m v : ℤ) - 6 + dg G (cpr G C T) v) ≤
          ∑ T ∈ ℬ, (3 * (m v₀ : ℤ) - 6 + dg G (cpr G C T) v₀) -
            (3 * (m v₀ : ℤ) - 6 + dg G C v₀) := by
      rw [← add_sum_erase A _ hv₀, hℬv₀]
      have h1 := sum_le_sum hother
      have h2 : ∑ v ∈ A.erase v₀, (3 * (m v : ℤ) - 6 + dg G C v) +
          (3 * (m v₀ : ℤ) - 6 + dg G C v₀) = 0 := by
        rw [sum_erase_add A _ hv₀]
        exact hf0
      linarith
    have hF₀ : ∑ T ∈ ℬ, (3 * (m v₀ : ℤ) - 6 + dg G (cpr G C T) v₀) =
        3 * #ℬ + ∑ T ∈ ℬ, (dg G (cpr G C T) v₀ : ℤ) := by
      rw [sum_add_distrib, sum_const, nsmul_eq_mul, hm₀]
      push_cast
      ring
    have hlowsum : ∑ T ∈ ℬ, (3 + (gv G T (cpr G C T) - 12)) =
        3 * #ℬ + ∑ T ∈ ℬ, (gv G T (cpr G C T) - 12) := by
      rw [sum_add_distrib, sum_const, nsmul_eq_mul]
      ring
    -- a neighbor of `v₀` lies in at most two of the sets `C'(T)`
    have hdg2 : ∑ T ∈ ℬ, dg G (cpr G C T) v₀ ≤ 2 * dg G C v₀ := by
      refine sum_dg_le_mul (fun T => cpr G C T) (fun T _ => cpr_subset C T) 2
        (fun c hc => ?_) v₀
      by_contra! h3
      obtain ⟨T₁, h₁, T₂, h₂, T₃, h₃, h12, h13, h23⟩ := two_lt_card.1 h3
      rw [mem_filter] at h₁ h₂ h₃
      have hT₁m := ((memℬ _).1 h₁.1).1
      have hT₂m := ((memℬ _).1 h₂.1).1
      have hT₃m := ((memℬ _).1 h₃.1).1
      exact three_cpr_false hK.block hT₁m.1 hT₂m.1 hT₃m.1
        (inter_eq_singleton hK hno hT₁m hT₂m h12 (hall₀ _ h₁.1) (hall₀ _ h₂.1)).1
        (inter_eq_singleton hK hno hT₁m hT₃m h13 (hall₀ _ h₁.1) (hall₀ _ h₃.1)).1
        (inter_eq_singleton hK hno hT₂m hT₃m h23 (hall₀ _ h₂.1) (hall₀ _ h₃.1)).1
        hc (mem_cpr.1 h₁.2).2 (mem_cpr.1 h₂.2).2 (mem_cpr.1 h₃.2).2
    have hdg2' : ∑ T ∈ ℬ, (dg G (cpr G C T) v₀ : ℤ) ≤ 6 := by
      rw [hd₀] at hdg2
      exact_mod_cast hdg2
    have hlow' := sum_le_sum hlow
    -- so every big member has `g(X'(T)) = 12`
    have hgsum : ∑ T ∈ ℬ, (gv G T (cpr G C T) - 12) ≤ 0 := by
      rw [hd₀] at hsum
      push_cast at hsum
      linarith
    have hg12 : ∀ T ∈ ℬ, gv G T (cpr G C T) = 12 := by
      intro T hT
      have h1 := single_le_sum hgnn hT
      have h2 := hgnn T hT
      linarith
    -- then sparsity at `X'(T) - v₀` puts the three neighbors of `v₀` into every `C'(T)`
    have hdg3 : ∀ T ∈ ℬ, 3 ≤ dg G (cpr G C T) v₀ := by
      intro T hT
      obtain ⟨hTm, hT3⟩ := (memℬ T).1 hT
      have hne := cpr_nonempty (hK.msum_le hTm.1) hT3 hTm.2.1
      have hcard : 3 ≤ #(T.erase v₀) + #(cpr G C T) := by
        rw [card_erase_of_mem (hall₀ T hT)]
        have := hne.card_pos
        omega
      have hsp := hK.block.sparse (T.erase v₀) ((erase_subset v₀ T).trans hTm.1) (cpr G C T)
        (cpr_subset C T) hcard
      rw [gv_erase_left (hall₀ T hT), hg12 T hT] at hsp
      omega
    -- two distinct big members then share three vertices of `C`, against `inter_eq_singleton`
    obtain ⟨T₁, h₁, T₂, h₂, hne⟩ := one_lt_card.1 (by omega : 1 < #ℬ)
    obtain ⟨-, hle⟩ := inter_eq_singleton hK hno ((memℬ _).1 h₁).1 ((memℬ _).1 h₂).1 hne
      (hall₀ _ h₁) (hall₀ _ h₂)
    have e := dg_union_add_dg_inter (G := G) (cpr G C T₁) (cpr G C T₂) v₀
    have hu := dg_mono (G := G)
      (union_subset (cpr_subset (G := G) C T₁) (cpr_subset (G := G) C T₂)) v₀
    have hi := dg_le_card (G := G) (cpr G C T₁ ∩ cpr G C T₂) v₀
    have h3₁ := hdg3 T₁ h₁
    have h3₂ := hdg3 T₂ h₂
    have h1 := ((memℬ _).1 h₁).1.2.1
    have h1' := ((memℬ _).1 h₂).1.2.1
    rw [hm₀] at hle
    push_cast at hle
    omega
  · -- no such vertex: the weight count gives `3 |ℬ| ≤ 0`, and then `m ≥ 1` on all of `A`
    have hall' : ∀ v ∈ A,
        ∑ T ∈ ℬ.filter (fun T => v ∈ T), (3 * (m v : ℤ) - 6 + dg G (cpr G C T) v) ≤
          3 * (m v : ℤ) - 6 + dg G C v :=
      fun v hv => hvert v hv fun h => hbad ⟨v, hv, h⟩
    have h1 := sum_le_sum hall'
    have h2 := sum_le_sum hlow
    have h3 : ∑ T ∈ ℬ, (3 + (gv G T (cpr G C T) - 12)) =
        3 * #ℬ + ∑ T ∈ ℬ, (gv G T (cpr G C T) - 12) := by
      rw [sum_add_distrib, sum_const, nsmul_eq_mul]
      ring
    have h4 : 0 ≤ ∑ T ∈ ℬ, (gv G T (cpr G C T) - 12) := sum_nonneg hgnn
    have hℬ0 : ℬ = ∅ := by
      apply card_eq_zero.1
      have : (#ℬ : ℤ) ≤ 0 := by linarith
      omega
    have hm1 : ∀ v ∈ A, (1 : ℤ) ≤ m v := fun v hv => by
      have := one_le_m_of_not_big hK hall hv fun T hT hT3 hvT => by
        have : T ∈ ℬ := (memℬ T).2 ⟨hT, hT3⟩
        rw [hℬ0] at this
        simp at this
      exact_mod_cast this
    have h5 : ∑ _v ∈ A, (1 : ℤ) ≤ msum m A := sum_le_sum hm1
    rw [sum_const, nsmul_eq_mul, mul_one, hK.msum_eq] at h5
    have := hK.block.six_le
    omega

end Erdos585.QB5
