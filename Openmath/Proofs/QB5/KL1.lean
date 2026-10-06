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
import Openmath.Proofs.QB5.KL1Merge

/-!
# QB(5): the key lemma KL1

KL1 is this project's label for the key lemma proved here as `kl1`: if `(A, C)` is a block
(`IsBlock`) and `m : V → ℕ` has `m(A) = 4` and `4 ≤ d_a + m(a) ≤ 6` for every `a ∈ A`, where `d_a`
is the number of neighbors of `a` in `C`, then some `p ∈ A` has `dem(A1) ≤ m(A1)` for every
`A1 ⊆ A - p`, with `dem(A1) = 4|A1| - Σ_{c ∈ C} min(4, e(c, A1))` (`dem`) and `e(c, A1)` the
number of neighbors of `c` in `A1`. The lower bound `4 ≤ d_a + m(a)` is the covering hypothesis:
as `d_a ≥ 3` in a block, it says that `m(a) ≥ 1` wherever `d_a = 3`. `kl1_thetaStar` proves that
some `p ∈ A` lies in no *overloaded* set, that is, in no `T ⊆ A` with `θ*(T) ≥ 1`, and
`exists_good_of_thetaStar` turns this into `kl1`.

Notation, as in `KL1Merge.lean`: `e(x, S)` is the number of neighbors of a vertex `x` in `S`
(`dg`), `e(T, J)` the number of adjacent pairs in `T × J` (`ec`), `m(T) = Σ_{a ∈ T} m(a)`
(`msum`), `w(T) = Σ_{a ∈ T} (6 - d_a - m(a))` (`wsum`), `θ` (`theta`), `θ*` (`thetaStar`),
`C'(T) = {c ∈ C : e(c, T) ≥ 3}` (`cpr`) and `X'(T) = (T, C'(T))`. For a pair `S = (T, J)` with
`T ⊆ A` and `J ⊆ C`: `κ(S) = |T| - |J|`, `g(S)` (`gv`), `∂_A(S) = e(T, C - J)`,
`∂_C(S) = e(J, A - T)` and `∂ = ∂_A + ∂_C`; `S` is *tight* if `g(S) = 12`. Unions,
intersections and differences of pairs are taken sidewise, and `S - a` deletes the vertex `a`.
A *big member* is a maximal overloaded set (`IsMaxOver`) with at least three vertices, and a
*singleton member* is one with exactly one vertex.

Suppose every vertex of `A` lies in an overloaded set. `exists_hub_pair` gives two maximal
overloaded sets sharing at least three vertices, and their intersection `K` is a *hub* (`IsHub`,
`isHub_of_pair`): `θ*(K) = 2`, no subset of `A` strictly containing `K` has `θ* ≥ 2`,
`m(K) ≥ 3`, every big member contains `K` and has `θ* = 1`, and two distinct big members meet
exactly in `K`. In the proof that every big member contains `K`, `hub_meet_one_false` rules out a
big member `T` with `T ∩ K = {a}`.

With `K⁺ = (K, K⁺_C)`, `K⁺_C = {c ∈ C : e(c, K) ≥ 2}` (`kpC`), each big member `T` has the
*petal* `P_T = (T - K, C'(T) - K⁺_C)`, with `θ(P_T) = 3 - E_T` for the number `E_T` of edges
between `K⁺` and `P_T` (`petal_facts`). Petals of distinct big members are disjoint
(`petal_J_disjoint` for the `C`-parts), and the count in `hub_false` closes the two cases that
`kplus_facts` leaves, case (β) `κ(K⁺) = -1` and case (δ) `κ(K⁺) = 0`. The per-petal inequalities
are the integer lemmas `petal_beta`, `petal_beta_sing` and `petal_delta`; in case (β) the bound
is `7 w(Q) ≤ 5 (E + m(Q))` for `Q = T - K` and `E = E_T`, and the case with a singleton member
ends at a vertex `c₀ ∈ C` whose six neighbors would all lie in the four vertices of `A - K`.

* `kl1_thetaStar`: KL1 in `θ*` form.
* `kl1`: KL1 in demand form, `dem(A1) ≤ m(A1)` for every `A1 ⊆ A - p`.
-/

open Finset

namespace Erdos585.QB5

open QB4

variable {V : Type*} {G : SimpleGraph V} [DecidableRel G.Adj] [DecidableEq V]

/-! ### Per-petal arithmetic -/

/-- Per-petal bound of case (β): `7 w(Q) ≤ 5 (E + m(Q))`. The variables are `q = |Q|`, `j = |J|`,
`e = e(Q, J)` for the petal `P = (Q, J)`, `E` the number of edges between `K⁺` and `P`, and
`κK = κ(K⁺)`. -/
private lemma petal_beta {q j e E mQ wQ mK wK κK : ℤ} (hq : 1 ≤ q) (hj : 0 ≤ j) (he0 : 0 ≤ e)
    (he : e ≤ q * j) (hwQ0 : 0 ≤ wQ)
    (hθ : mQ + 4 - 4 * q - 2 * j + e = 3 - E)
    (hw : wK + wQ ≤ 3 + 2 * (κK + (q - j)))
    (hk : κK + (q - j) ≤ mK + mQ - 3) (hmT : mK + mQ ≤ 4) (hcov : wQ ≤ 2 * q)
    (hsp : 3 ≤ q + j → mQ + 4 - 4 * q - 2 * j + e ≤ mQ - 2 - (q - j))
    (hκ : κK = -1) (hwK : wK = 0) :
    7 * wQ ≤ 5 * (E + mQ) := by
  subst hκ hwK
  by_cases h3 : 3 ≤ q + j
  · have := hsp h3
    linarith
  · have hq2 : q ≤ 2 := by omega
    have hj1 : j ≤ 1 := by omega
    interval_cases q <;> interval_cases j <;> omega

/-- Per-petal bound of case (β) with a singleton member (`m(Q) = 0`, `m(K) = 3`):
`3 w(Q) ≤ 2E`, with equality only for a one-vertex petal `{y}`. -/
private lemma petal_beta_sing {q j e E mQ wQ mK wK κK : ℤ} (hq : 1 ≤ q) (hj : 0 ≤ j)
    (he0 : 0 ≤ e) (he : e ≤ q * j) (hwQ0 : 0 ≤ wQ)
    (hθ : mQ + 4 - 4 * q - 2 * j + e = 3 - E)
    (hw : wK + wQ ≤ 3 + 2 * (κK + (q - j)))
    (hk : κK + (q - j) ≤ mK + mQ - 3) (hcov : wQ ≤ 2 * q)
    (hsp : 3 ≤ q + j → mQ + 4 - 4 * q - 2 * j + e ≤ mQ - 2 - (q - j))
    (hκ : κK = -1) (hwK : wK = 0) (hmQ : mQ = 0) (hmK : mK = 3) :
    3 * wQ ≤ 2 * E ∧ (3 * wQ = 2 * E → q = 1 ∧ j = 0) := by
  subst hκ hwK hmQ hmK
  by_cases h3 : 3 ≤ q + j
  · have := hsp h3
    constructor
    · linarith
    · intro h
      exfalso
      linarith
  · have hq2 : q ≤ 2 := by omega
    have hj1 : j ≤ 1 := by omega
    interval_cases q <;> interval_cases j <;> omega

/-- Per-petal bound of case (δ) (`κ(K⁺) = 0`, `m(K) = 4`): `w(Q) < E`. -/
private lemma petal_delta {q j e E mQ wQ mK wK κK : ℤ} (hq : 1 ≤ q) (hj : 0 ≤ j) (he0 : 0 ≤ e)
    (he : e ≤ q * j) (hwQ0 : 0 ≤ wQ) (hmQ0 : 0 ≤ mQ) (hwK0 : 0 ≤ wK)
    (hθ : mQ + 4 - 4 * q - 2 * j + e = 3 - E)
    (hw : wK + wQ ≤ 3 + 2 * (κK + (q - j)))
    (hk : κK + (q - j) ≤ mK + mQ - 3) (hmT : mK + mQ ≤ 4) (hcov : wQ ≤ 2 * q)
    (hsp : 3 ≤ q + j → mQ + 4 - 4 * q - 2 * j + e ≤ mQ - 2 - (q - j))
    (hκ : κK = 0) (hmK : mK = 4) :
    wQ + 1 ≤ E := by
  subst hκ hmK
  have hmQ : mQ = 0 := by omega
  subst hmQ
  by_cases h3 : 3 ≤ q + j
  · have := hsp h3
    linarith
  · have hq2 : q ≤ 2 := by omega
    have hj1 : j ≤ 1 := by omega
    interval_cases q <;> interval_cases j <;> omega

/-! ### The hub -/

section Hub

variable {A C : Finset V} {m : V → ℕ} {K : Finset V}

variable (G) in
/-- `K⁺_C = {c ∈ C : e(c, K) ≥ 2}`, the `C`-part of the pair `K⁺ = (K, K⁺_C)`. -/
private def kpC (C K : Finset V) : Finset V := {c ∈ C | 2 ≤ dg G K c}

omit [DecidableEq V] in
private lemma kpC_subset (C K : Finset V) : kpC G C K ⊆ C := filter_subset _ _

omit [DecidableEq V] in
/-- `θ(K⁺) = θ*(K)`. -/
private lemma theta_kpC (m : V → ℕ) (C K : Finset V) :
    theta G m K (kpC G C K) = thetaStar G m C K :=
  theta_eq_thetaStar m (kpC_subset C K) (fun c hc h3 => mem_filter.2 ⟨hc, by omega⟩)
    (fun c hc => (mem_filter.1 hc).2)

variable (G) in
/-- `K` is a hub: `K ⊆ A`, `|K| ≥ 3`, `θ*(K) = 2`, no subset of `A` strictly containing `K` has
`θ* ≥ 2`, `m(K) ≥ 3`, every maximal overloaded set with at least three vertices contains `K`, has
`θ* = 1` and differs from `K`, two distinct ones meet exactly in `K`, and one exists. -/
structure IsHub (A C : Finset V) (m : V → ℕ) (K : Finset V) : Prop where
  subset : K ⊆ A
  three_le : 3 ≤ #K
  thetaStar_eq : thetaStar G m C K = 2
  maximal : ∀ K' ⊆ A, K ⊆ K' → 2 ≤ thetaStar G m C K' → K' = K
  msum_ge : 3 ≤ msum m K
  big : ∀ T, IsMaxOver G m A C T → 3 ≤ #T → K ⊆ T ∧ thetaStar G m C T = 1 ∧ T ≠ K
  inter : ∀ T T', IsMaxOver G m A C T → 3 ≤ #T → IsMaxOver G m A C T' → 3 ≤ #T' → T ≠ T' →
    T ∩ T' = K
  exists_big : ∃ T, IsMaxOver G m A C T ∧ 3 ≤ #T

/-- The identities of `K⁺` behind the split into case (β), `κ(K⁺) = -1`, and case (δ),
`κ(K⁺) = 0`, for any `K ⊆ A` with `|K| ≥ 3` and `θ*(K) = 2`: with `κ = κ(K⁺)`,
`w(K) + ∂_A(K⁺) = 2 + 2κ`, `κ ≤ m(K) - 4`, `∂_C(K⁺) = m(K) + 2 - 4κ` and
`g(K⁺) = 2m(K) + 4 - 2κ`. -/
private lemma kplus_facts (hK : KLData G A C m) {K : Finset V} (hKA : K ⊆ A) (hK3 : 3 ≤ #K)
    (hKθ : thetaStar G m C K = 2) :
    wsum G m C K + ec G K (C \ kpC G C K) = 2 + 2 * ((#K : ℤ) - #(kpC G C K)) ∧
      (#K : ℤ) - #(kpC G C K) ≤ msum m K - 4 ∧
      (ec G (kpC G C K) (A \ K) : ℤ) = msum m K + 2 - 4 * ((#K : ℤ) - #(kpC G C K)) ∧
      gv G K (kpC G C K) = 2 * msum m K + 4 - 2 * ((#K : ℤ) - #(kpC G C K)) := by
  have hθ : theta G m K (kpC G C K) = 2 := (theta_kpC m C K).trans hKθ
  have h1 := theta_eq_four_add (G := G) m (kpC_subset (G := G) C K) K
  have h2 := theta_le_of_three_le hK.block m hKA (kpC_subset (G := G) C K) (by omega)
  have h3 := theta_eq_boundary hK.block m hKA (kpC_subset (G := G) C K)
  have h4 := two_mul_theta (G := G) m K (kpC G C K)
  rw [hθ] at h1 h2 h3 h4
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- **One shared vertex**: for `K ⊆ A` with `|K| ≥ 3` and `θ*(K) = 2`, a maximal overloaded set
`T` with `|T| ≥ 3` cannot meet `K` in exactly one vertex `a`. If it did, then `m(a) = 3`, every
neighbor of `a` lies in `K⁺_C`, `C'(T) ∩ K⁺_C = ∅`, so `a` has no neighbor in `C'(T)`, and
`g(X'(T)) ≥ 18` against `g(X'(T)) ≤ 16`. -/
private lemma hub_meet_one_false (hK : KLData G A C m) {K T : Finset V} (hKA : K ⊆ A)
    (hK3 : 3 ≤ #K) (hKθ : thetaStar G m C K = 2) (hT : IsMaxOver G m A C T) (hT3 : 3 ≤ #T)
    {a : V} (ha : T ∩ K = {a}) : False := by
  have haT : a ∈ T := (mem_inter.1 (ha ▸ mem_singleton_self a)).1
  have haK : a ∈ K := (mem_inter.1 (ha ▸ mem_singleton_self a)).2
  have haA := hKA haK
  -- `T ∪ K` strictly contains `T`, so it is not overloaded
  have hKT : ¬ K ⊆ T := fun h => by
    rw [inter_eq_right.2 h] at ha
    rw [ha, card_singleton] at hK3
    omega
  have hU : thetaStar G m C (T ∪ K) ≤ 0 := by
    by_contra h
    have := hT.2.2 (T ∪ K) (union_subset hT.1 hKA) subset_union_left (by omega)
    exact hKT (this ▸ subset_union_right)
  -- `thetaStar_add_le` gives `m(a) ≥ 3`, so `m(a) = 3` and `d_a = 3`
  have h21 := thetaStar_add_le (G := G) m C T K
  rw [ha, thetaStar_singleton] at h21
  have hT1 := hT.2.1
  have hma3 := hK.m_le_three haA
  have hma : m a = 3 := by omega
  have hda : dg G C a = 3 := by
    have := hK.le_delta a haA
    have := hK.block.three_le a haA
    omega
  -- every neighbor of `a` lies in `K⁺_C`
  obtain ⟨hk1, hk2, -, hk4⟩ := kplus_facts hK hKA hK3 hKθ
  have hwK := hK.wsum_nonneg' hKA
  have hmK := hK.msum_le hKA
  have hdL : dg G (kpC G C K) a = 3 := by
    have hle := dg_mono (G := G) (kpC_subset (G := G) C K) a
    have hsplit := dg_sdiff_add (G := G) (kpC_subset (G := G) C K) a
    have hec : (0 : ℤ) ≤ ec G K (C \ kpC G C K) := Nat.cast_nonneg _
    rcases (by omega : (#K : ℤ) - #(kpC G C K) = -1 ∨ (#K : ℤ) - #(kpC G C K) = 0)
      with hκ | hκ
    · -- case (β): `∂_A(K⁺) = 0`
      have h0 : ec G K (C \ kpC G C K) = 0 := by
        have : (ec G K (C \ kpC G C K) : ℤ) = 0 := by linarith
        exact_mod_cast this
      have hle' : dg G (C \ kpC G C K) a ≤ ec G K (C \ kpC G C K) :=
        single_le_sum (f := fun x => dg G (C \ kpC G C K) x) (fun _ _ => Nat.zero_le _) haK
      omega
    · -- case (δ): `K⁺` is tight and `|K⁺ - a| ≥ 3`
      have hg : gv G K (kpC G C K) = 12 := by
        rw [hk4, hκ]
        have : msum m K = 4 := by linarith
        rw [this]
        norm_num
      have hcard : 3 ≤ #(K.erase a) + #(kpC G C K) := by
        rw [card_erase_of_mem haK]
        omega
      have hsp := hK.block.sparse (K.erase a) ((erase_subset a K).trans hKA) (kpC G C K)
        (kpC_subset C K) hcard
      rw [gv_erase_left haK, hg] at hsp
      omega
  -- `theta_union_add_theta_inter` for `X'(T)` and `K⁺` gives `θ({a}, C'(T) ∩ K⁺_C) ≥ 3`, so
  -- `C'(T) ∩ K⁺_C = ∅` by `theta_singleton`
  have hun := theta_union_add_theta_inter (G := G) m T K (cpr G C T) (kpC G C K)
  rw [theta_cpr, theta_kpC, ha, hKθ] at hun
  have hle := theta_le_thetaStar (G := G) m
    (union_subset (cpr_subset (G := G) C T) (kpC_subset (G := G) C K)) (T ∪ K)
  have hsing := (theta_singleton (G := G) m a (cpr G C T ∩ kpC G C K)).2
  have hcross : (0 : ℤ) ≤ (ec G (T \ K) (kpC G C K \ cpr G C T) : ℤ) +
      (ec G (K \ T) (cpr G C T \ kpC G C K) : ℤ) := by positivity
  have hJ0 : #(cpr G C T ∩ kpC G C K) = 0 := by
    rw [hma] at hsing
    push_cast at hsing
    have : (#(cpr G C T ∩ kpC G C K) : ℤ) ≤ 0 := by linarith
    omega
  -- so `a` has no neighbor in `C'(T)`
  have hsub : cpr G C T ⊆ C \ kpC G C K := fun c hc => by
    refine mem_sdiff.2 ⟨cpr_subset C T hc, fun hcL => ?_⟩
    have : c ∈ cpr G C T ∩ kpC G C K := mem_inter.2 ⟨hc, hcL⟩
    rw [card_eq_zero.1 hJ0] at this
    simp at this
  have hda0 : dg G (cpr G C T) a = 0 := by
    have h1 := dg_mono (G := G) hsub a
    have h2 := dg_sdiff_add (G := G) (kpC_subset (G := G) C K) a
    omega
  -- `g(X'(T) - a) ≥ 12` gives `g(X'(T)) ≥ 18`, against `g(X'(T)) ≤ 16`
  have hne := cpr_nonempty (hK.msum_le hT.1) hT3 hT.2.1
  have hcard : 3 ≤ #(T.erase a) + #(cpr G C T) := by
    rw [card_erase_of_mem haT]
    have := hne.card_pos
    omega
  have hsp := hK.block.sparse (T.erase a) ((erase_subset a T).trans hT.1) (cpr G C T)
    (cpr_subset C T) hcard
  rw [gv_erase_left haT, hda0] at hsp
  have h2θ := two_mul_theta (G := G) m T (cpr G C T)
  rw [theta_cpr] at h2θ
  have hκT := (two_le_msum hK.block hK.le_delta hT.1 hT3 hT.2.1).2.1
  have hmT := hK.msum_le hT.1
  push_cast at hsp
  linarith

/-- Two distinct maximal overloaded sets `T₁`, `T₂` sharing at least three vertices meet in a hub
`K = T₁ ∩ T₂`. -/
theorem isHub_of_pair (hK : KLData G A C m) {T₁ T₂ : Finset V} (h₁ : IsMaxOver G m A C T₁)
    (h₂ : IsMaxOver G m A C T₂) (hne : T₁ ≠ T₂) (h3 : 3 ≤ #(T₁ ∩ T₂)) :
    IsHub G A C m (T₁ ∩ T₂) := by
  have hU := h₁.union_le h₂ hne
  obtain ⟨hKθ, hθ₁, hθ₂⟩ := merge_N3 hK h₁.1 h₁.2.1 h₂.2.1 hU h3
  have hKA : T₁ ∩ T₂ ⊆ A := inter_subset_left.trans h₁.1
  -- no subset of `A` strictly containing `K` has `θ* ≥ 2`
  have hmax : ∀ K' ⊆ A, T₁ ∩ T₂ ⊆ K' → 2 ≤ thetaStar G m C K' → K' = T₁ ∩ T₂ := by
    intro K' hK'A hsub h2
    have key : ∀ T, IsMaxOver G m A C T → T₁ ∩ T₂ ⊆ T → thetaStar G m C T = 1 → K' ⊆ T := by
      intro T hT hKT hθT
      have hle := thetaStar_add_le (G := G) m C T K'
      have hi3 : 3 ≤ #(T ∩ K') := h3.trans (card_le_card (subset_inter hKT hsub))
      have hi2 := thetaStar_le_two hK.block hK.msum_eq hK.le_delta
        ((inter_subset_left (s₂ := K')).trans hT.1) hi3
      have hu1 : 1 ≤ thetaStar G m C (T ∪ K') := by linarith
      have := hT.2.2 (T ∪ K') (union_subset hT.1 hK'A) subset_union_left hu1
      rw [← this]
      exact subset_union_right
    exact Subset.antisymm
      (subset_inter (key T₁ h₁ inter_subset_left hθ₁) (key T₂ h₂ inter_subset_right hθ₂)) hsub
  -- `m(K) ≥ 3`
  have hmK : 3 ≤ msum m (T₁ ∩ T₂) := by
    have hθ : theta G m (T₁ ∩ T₂) (cpr G C (T₁ ∩ T₂)) = 2 := (theta_cpr m C _).trans hKθ
    have hk := kappa_bounds hK.block hK.le_delta hKA (cpr_subset (G := G) C (T₁ ∩ T₂))
      (by omega) (by rw [hθ]; norm_num)
    have hsp := theta_le_of_three_le hK.block m hKA (cpr_subset (G := G) C (T₁ ∩ T₂))
      (by omega)
    rw [hθ] at hsp
    linarith [hk.1]
  -- every big member contains `K` and has `θ* = 1`
  have hbig : ∀ T, IsMaxOver G m A C T → 3 ≤ #T →
      T₁ ∩ T₂ ⊆ T ∧ thetaStar G m C T = 1 ∧ T ≠ T₁ ∩ T₂ := by
    intro T hT hT3
    have hsub : T₁ ∩ T₂ ⊆ T := by
      have h2m := (two_le_msum hK.block hK.le_delta hT.1 hT3 hT.2.1).1
      rcases lt_or_ge #(T ∩ (T₁ ∩ T₂)) 2 with hlt | hge
      · exfalso
        interval_cases hc : #(T ∩ (T₁ ∩ T₂))
        · -- `T` misses `K`: then `m(T) ≤ 4 - m(K) ≤ 1`
          have hdisj : Disjoint T (T₁ ∩ T₂) := disjoint_iff_inter_eq_empty.2 (card_eq_zero.1 hc)
          have e := msum_union_of_disjoint m hdisj
          have := hK.msum_le (union_subset hT.1 hKA)
          omega
        · obtain ⟨a, ha⟩ := card_eq_one.1 hc
          exact hub_meet_one_false hK hKA h3 hKθ hT hT3 ha
      · -- `T` shares at least two vertices with `K`: `T ∪ K` is overloaded
        have hle := thetaStar_add_le (G := G) m C T (T₁ ∩ T₂)
        have hi2 : thetaStar G m C (T ∩ (T₁ ∩ T₂)) ≤ 2 := by
          rcases eq_or_lt_of_le hge with h2 | h3'
          · rw [thetaStar_of_card_eq_two m C h2.symm]
            have := hK.msum_le ((inter_subset_left (s₂ := T₁ ∩ T₂)).trans hT.1)
            linarith
          · exact thetaStar_le_two hK.block hK.msum_eq hK.le_delta
              ((inter_subset_left (s₂ := T₁ ∩ T₂)).trans hT.1) h3'
        have hu1 : 1 ≤ thetaStar G m C (T ∪ (T₁ ∩ T₂)) := by linarith [hT.2.1]
        have := hT.2.2 _ (union_subset hT.1 hKA) subset_union_left hu1
        rw [← this]
        exact subset_union_right
    refine ⟨hsub, ?_, ?_⟩
    · by_cases hT1 : T = T₁
      · rw [hT1]
        exact hθ₁
      · have hU' := hT.union_le h₁ hT1
        have h3' : 3 ≤ #(T ∩ T₁) := h3.trans (card_le_card (subset_inter hsub inter_subset_left))
        exact (merge_N3 hK hT.1 hT.2.1 h₁.2.1 hU' h3').2.1
    · intro hTK
      have e1 := hT.2.2 T₁ h₁.1 (hTK ▸ inter_subset_left) h₁.2.1
      have e2 := hT.2.2 T₂ h₂.1 (hTK ▸ inter_subset_right) h₂.2.1
      exact hne (e1.trans e2.symm)
  -- two distinct big members meet exactly in `K`
  have hinter : ∀ T T', IsMaxOver G m A C T → 3 ≤ #T → IsMaxOver G m A C T' → 3 ≤ #T' →
      T ≠ T' → T ∩ T' = T₁ ∩ T₂ := by
    intro T T' hT hT3 hT' hT3' hTT'
    obtain ⟨hs, -, -⟩ := hbig T hT hT3
    obtain ⟨hs', -, -⟩ := hbig T' hT' hT3'
    have h3' : 3 ≤ #(T ∩ T') := h3.trans (card_le_card (subset_inter hs hs'))
    have hU' := hT.union_le hT' hTT'
    have hθ := (merge_N3 hK hT.1 hT.2.1 hT'.2.1 hU' h3').1
    exact hmax (T ∩ T') ((inter_subset_left (s₂ := T')).trans hT.1) (subset_inter hs hs')
      hθ.ge
  have hT₁3 : 3 ≤ #T₁ := h3.trans (card_le_card inter_subset_left)
  exact ⟨hKA, h3, hKθ, hmax, hmK, hbig, hinter, ⟨T₁, h₁, hT₁3⟩⟩

/-! ### The petals -/

/-- For a big member `T`, the pair `S_T = X'(T) ∪ K⁺ = (T, C'(T) ∪ K⁺_C)` has
`θ(S_T) = θ*(T) = 1`. -/
private lemma theta_S (hub : IsHub G A C m K) {T : Finset V} (hT : IsMaxOver G m A C T)
    (hT3 : 3 ≤ #T) : theta G m T (cpr G C T ∪ kpC G C K) = 1 := by
  obtain ⟨hKT, hθT, -⟩ := hub.big T hT hT3
  rw [← hθT]
  refine theta_eq_thetaStar m (union_subset (cpr_subset C T) (kpC_subset C K))
    (fun c hc h3 => mem_union_left _ (mem_cpr.2 ⟨hc, h3⟩)) fun c hc => ?_
  rcases mem_union.1 hc with h | h
  · have := (mem_cpr.1 h).2
    omega
  · exact (mem_filter.1 h).2.trans (dg_mono hKT c)

/-- **The petal facts** for one big member `T` and its petal `P_T = (T - K, C'(T) - K⁺_C)`:
`θ(P_T) = 3 - E_T` with `E_T = e(K, C'(T) - K⁺_C) + e(T - K, K⁺_C)`,
`w(K) + w(T - K) ≤ 3 + 2κ(S_T)` and `κ(S_T) ≤ m(T) - 3`, where
`κ(S_T) = κ(K⁺) + κ(P_T)`, and `T - K ≠ ∅`. -/
private lemma petal_facts (hK : KLData G A C m) (hub : IsHub G A C m K) {T : Finset V}
    (hT : IsMaxOver G m A C T) (hT3 : 3 ≤ #T) :
    theta G m (T \ K) (cpr G C T \ kpC G C K) =
        3 - ((ec G K (cpr G C T \ kpC G C K) : ℤ) + ec G (T \ K) (kpC G C K)) ∧
      wsum G m C K + wsum G m C (T \ K) ≤
        3 + 2 * (((#K : ℤ) - #(kpC G C K)) + ((#(T \ K) : ℤ) - #(cpr G C T \ kpC G C K))) ∧
      ((#K : ℤ) - #(kpC G C K)) + ((#(T \ K) : ℤ) - #(cpr G C T \ kpC G C K)) ≤
        msum m K + msum m (T \ K) - 3 ∧
      1 ≤ #(T \ K) := by
  obtain ⟨hKT, hθT, hTK⟩ := hub.big T hT hT3
  have hS := theta_S hub hT hT3
  have hJ'C : cpr G C T ∪ kpC G C K ⊆ C := union_subset (cpr_subset C T) (kpC_subset C K)
  -- θ(P_T) = 3 - E_T, from `theta_union_add_theta_inter` for the disjoint `K⁺` and `P_T`
  have hun := theta_union_add_theta_inter (G := G) m K (T \ K) (kpC G C K)
    (cpr G C T \ kpC G C K)
  have e1 : K ∪ (T \ K) = T := union_sdiff_of_subset hKT
  have e2 : kpC G C K ∪ (cpr G C T \ kpC G C K) = cpr G C T ∪ kpC G C K := by
    rw [union_sdiff_self_eq_union, union_comm]
  have e3 : K ∩ (T \ K) = ∅ := inter_sdiff_self K T
  have e4 : kpC G C K ∩ (cpr G C T \ kpC G C K) = ∅ := inter_sdiff_self _ _
  have e5 : K \ (T \ K) = K := by
    ext x
    simp only [mem_sdiff]
    tauto
  have e6 : (cpr G C T \ kpC G C K) \ kpC G C K = cpr G C T \ kpC G C K := by
    ext x
    simp only [mem_sdiff]
    tauto
  have e7 : (T \ K) \ K = T \ K := by
    ext x
    simp only [mem_sdiff]
    tauto
  have e8 : kpC G C K \ (cpr G C T \ kpC G C K) = kpC G C K := by
    ext x
    simp only [mem_sdiff]
    tauto
  rw [e1, e2, e3, e4, e5, e6, e7, e8, hS, theta_empty, theta_kpC, hub.thetaStar_eq] at hun
  -- `w(T) ≤ w(T) + ∂_A(S_T) = 3 + 2κ(S_T)` and `κ(S_T) ≤ m(T) - 3`
  have h4 := theta_eq_four_add (G := G) m hJ'C T
  rw [hS] at h4
  have hw := wsum_sdiff_add (G := G) m C hKT
  have hcT := card_sdiff_add_card_eq_card hKT
  have hcJ : #(cpr G C T \ kpC G C K) + #(kpC G C K) = #(cpr G C T ∪ kpC G C K) :=
    card_sdiff_add_card _ _
  have hec : (0 : ℤ) ≤ ec G T (C \ (cpr G C T ∪ kpC G C K)) := Nat.cast_nonneg _
  have hk := kappa_bounds hK.block hK.le_delta hT.1 hJ'C (by omega) (by rw [hS])
  have hmT := msum_sdiff_add m hKT
  have hQ : 1 ≤ #(T \ K) := by
    have : (T \ K).Nonempty := by
      rw [nonempty_iff_ne_empty, Ne, sdiff_eq_empty_iff_subset]
      exact fun h => hTK (Subset.antisymm h hKT)
    exact this.card_pos
  refine ⟨by linarith, ?_, ?_, hQ⟩
  · have : (#T : ℤ) - #(cpr G C T ∪ kpC G C K) =
        ((#K : ℤ) - #(kpC G C K)) + ((#(T \ K) : ℤ) - #(cpr G C T \ kpC G C K)) := by
      push_cast [← hcT, ← hcJ]
      ring
    linarith
  · have : (#T : ℤ) - #(cpr G C T ∪ kpC G C K) =
        ((#K : ℤ) - #(kpC G C K)) + ((#(T \ K) : ℤ) - #(cpr G C T \ kpC G C K)) := by
      push_cast [← hcT, ← hcJ]
      ring
    linarith [hk.2]

/-- The `C`-parts of the petals of two distinct big members are disjoint, since
`θ(S_T ∩ S_T') ≥ 2` and a `C`-vertex outside `K⁺_C` lowers `θ(K⁺)` by at least 1. -/
private lemma petal_J_disjoint (hub : IsHub G A C m K) {T T' : Finset V}
    (hT : IsMaxOver G m A C T) (hT3 : 3 ≤ #T) (hT' : IsMaxOver G m A C T') (hT3' : 3 ≤ #T')
    (hne : T ≠ T') : Disjoint (cpr G C T \ kpC G C K) (cpr G C T' \ kpC G C K) := by
  have hS := theta_S hub hT hT3
  have hS' := theta_S hub hT' hT3'
  have hun := theta_union_add_theta_inter (G := G) m T T' (cpr G C T ∪ kpC G C K)
    (cpr G C T' ∪ kpC G C K)
  have hU := hT.union_le hT' hne
  have hle := theta_le_thetaStar (G := G) m
    (union_subset (union_subset (cpr_subset (G := G) C T) (kpC_subset (G := G) C K))
      (union_subset (cpr_subset (G := G) C T') (kpC_subset (G := G) C K))) (T ∪ T')
  have eZ : (cpr G C T ∪ kpC G C K) ∩ (cpr G C T' ∪ kpC G C K) =
      kpC G C K ∪ ((cpr G C T \ kpC G C K) ∩ (cpr G C T' \ kpC G C K)) := by
    ext x
    simp only [mem_union, mem_inter, mem_sdiff]
    tauto
  have hdisj : Disjoint (kpC G C K) ((cpr G C T \ kpC G C K) ∩ (cpr G C T' \ kpC G C K)) :=
    disjoint_sdiff.mono_right inter_subset_left
  rw [hub.inter T T' hT hT3 hT' hT3' hne, eZ, theta_union_right m K hdisj, theta_kpC,
    hub.thetaStar_eq, hS, hS'] at hun
  -- every `c` in both petals has `e(c, K) ≤ 1`
  have hZ : ∑ c ∈ (cpr G C T \ kpC G C K) ∩ (cpr G C T' \ kpC G C K), ((dg G K c : ℤ) - 2) ≤
      ∑ _c ∈ (cpr G C T \ kpC G C K) ∩ (cpr G C T' \ kpC G C K), (-1 : ℤ) := by
    refine sum_le_sum fun c hc => ?_
    obtain ⟨hcT, hcL⟩ := mem_sdiff.1 (mem_inter.1 hc).1
    have hcC := cpr_subset C T hcT
    have : dg G K c < 2 := by
      by_contra h
      exact hcL (mem_filter.2 ⟨hcC, by omega⟩)
    have : (dg G K c : ℤ) ≤ 1 := by exact_mod_cast (by omega : dg G K c ≤ 1)
    linarith
  rw [sum_const, nsmul_eq_mul, mul_neg_one] at hZ
  have hcross : (0 : ℤ) ≤ (ec G (T \ T') ((cpr G C T' ∪ kpC G C K) \ (cpr G C T ∪ kpC G C K)) :
      ℤ) + (ec G (T' \ T) ((cpr G C T ∪ kpC G C K) \ (cpr G C T' ∪ kpC G C K)) : ℤ) := by
    positivity
  rw [disjoint_iff_inter_eq_empty]
  apply card_eq_zero.1
  have : (#((cpr G C T \ kpC G C K) ∩ (cpr G C T' \ kpC G C K)) : ℤ) ≤ 0 := by linarith
  omega

/-! ### The count over the petals -/

/-- **The count**: if every vertex of `A` lies in an overloaded set and the covering hypothesis
`4 ≤ d_a + m(a)` holds on `A`, a hub is impossible. -/
private lemma hub_false (hK : KLData G A C m) (hcov : ∀ a ∈ A, 4 ≤ dg G C a + m a)
    (hall : ∀ p ∈ A, ∃ T ⊆ A, p ∈ T ∧ 1 ≤ thetaStar G m C T) {K : Finset V}
    (hub : IsHub G A C m K) : False := by
  classical
  -- the identities of `K⁺`
  obtain ⟨hk1, hk2, hk3, -⟩ := kplus_facts hK hub.subset hub.three_le hub.thetaStar_eq
  have hLC : kpC G C K ⊆ C := kpC_subset C K
  set L := kpC G C K with hL
  set ℬ : Finset (Finset V) := A.powerset.filter (fun T => IsMaxOver G m A C T ∧ 3 ≤ #T)
    with hℬ
  have memℬ : ∀ T, T ∈ ℬ ↔ IsMaxOver G m A C T ∧ 3 ≤ #T := fun T => by
    rw [hℬ, mem_filter, mem_powerset]
    exact ⟨fun h => h.2, fun h => ⟨h.1.1, h⟩⟩
  have hwK := hK.wsum_nonneg' hub.subset
  have hmK4 := hK.msum_le hub.subset
  have hmK3 := hub.msum_ge
  have hecK : (0 : ℤ) ≤ ec G K (C \ L) := Nat.cast_nonneg _
  -- the petals are disjoint
  have hdQ : (ℬ : Set (Finset V)).PairwiseDisjoint (fun T => T \ K) := by
    intro T hT T' hT' hne
    obtain ⟨hTm, hT3⟩ := (memℬ T).1 (mem_coe.1 hT)
    obtain ⟨hT'm, hT3'⟩ := (memℬ T').1 (mem_coe.1 hT')
    have hi := hub.inter T T' hTm hT3 hT'm hT3' hne
    show Disjoint (T \ K) (T' \ K)
    rw [disjoint_left]
    intro x hx hx'
    rw [mem_sdiff] at hx hx'
    exact hx.2 (hi ▸ mem_inter.2 ⟨hx.1, hx'.1⟩)
  have hdJ : (ℬ : Set (Finset V)).PairwiseDisjoint (fun T => cpr G C T \ L) := by
    intro T hT T' hT' hne
    obtain ⟨hTm, hT3⟩ := (memℬ T).1 (mem_coe.1 hT)
    obtain ⟨hT'm, hT3'⟩ := (memℬ T').1 (mem_coe.1 hT')
    exact petal_J_disjoint hub hTm hT3 hT'm hT3' hne
  set U := ℬ.biUnion (fun T => T \ K) with hU
  set Jall := ℬ.biUnion (fun T => cpr G C T \ L) with hJall
  have hUA : U ⊆ A \ K := fun x hx => by
    obtain ⟨T, hT, hxT⟩ := mem_biUnion.1 hx
    obtain ⟨hxT, hxK⟩ := mem_sdiff.1 hxT
    exact mem_sdiff.2 ⟨((memℬ T).1 hT).1.1 hxT, hxK⟩
  have hJC : Jall ⊆ C \ L := fun x hx => by
    obtain ⟨T, -, hxT⟩ := mem_biUnion.1 hx
    obtain ⟨hxT, hxL⟩ := mem_sdiff.1 hxT
    exact mem_sdiff.2 ⟨cpr_subset C T hxT, hxL⟩
  -- sums over the petals
  have sW : wsum G m C U = ∑ T ∈ ℬ, wsum G m C (T \ K) := sum_biUnion hdQ
  have sM : msum m U = ∑ T ∈ ℬ, msum m (T \ K) := sum_biUnion hdQ
  have sC : #U = ∑ T ∈ ℬ, #(T \ K) := card_biUnion hdQ
  have sE1 : ∑ T ∈ ℬ, (ec G K (cpr G C T \ L) : ℤ) ≤ ec G K (C \ L) := by
    have h1 : ∑ T ∈ ℬ, ec G K (cpr G C T \ L) = ec G Jall K := by
      rw [show ec G Jall K = ∑ c ∈ Jall, dg G K c from rfl, sum_biUnion hdJ]
      exact sum_congr rfl fun T _ => ec_comm _ _
    have h2 : ec G Jall K ≤ ec G K (C \ L) := by
      rw [ec_comm K]
      exact ec_mono_left hJC K
    exact_mod_cast h1 ▸ h2
  have sE2 : ∑ T ∈ ℬ, (ec G (T \ K) L : ℤ) ≤ ec G L (A \ K) := by
    have h1 : ∑ T ∈ ℬ, ec G (T \ K) L = ec G U L := by
      rw [show ec G U L = ∑ x ∈ U, dg G L x from rfl, sum_biUnion hdQ]
      rfl
    have h2 : ec G U L ≤ ec G L (A \ K) := by
      rw [ec_comm L]
      exact ec_mono_left hUA L
    exact_mod_cast h1 ▸ h2
  -- the partition `A = R ∪ K ∪ U`; every `v ∈ R` lies in no big member, so `m(v) ≥ 1`
  have hKU : Disjoint K U := disjoint_left.2 fun x hxK hxU => (mem_sdiff.1 (hUA hxU)).2 hxK
  have hKUA : K ∪ U ⊆ A := union_subset hub.subset (hUA.trans sdiff_subset)
  have pW := wsum_sdiff_add (G := G) m C hKUA
  rw [wsum_union_of_disjoint m C hKU] at pW
  have pM := msum_sdiff_add m hKUA
  rw [msum_union_of_disjoint m hKU] at pM
  have pC := card_sdiff_add_card_eq_card hKUA
  rw [card_union_of_disjoint hKU] at pC
  set R := A \ (K ∪ U) with hR
  have hRm : (#R : ℤ) ≤ msum m R := by
    have h1 : ∀ v ∈ R, (1 : ℤ) ≤ m v := by
      intro v hv
      obtain ⟨hvA, hvKU⟩ := mem_sdiff.1 hv
      have : 1 ≤ m v := one_le_m_of_not_big hK hall hvA fun T hT hT3 hvT => by
        apply hvKU
        by_cases hvK : v ∈ K
        · exact mem_union_left _ hvK
        · exact mem_union_right _
            (mem_biUnion.2 ⟨T, (memℬ T).2 ⟨hT, hT3⟩, mem_sdiff.2 ⟨hvT, hvK⟩⟩)
      exact_mod_cast this
    have h2 := sum_le_sum h1
    rw [sum_const, nsmul_eq_mul, mul_one] at h2
    exact h2
  have hRw : wsum G m C R ≤ 2 * #R := wsum_le_two_mul hcov sdiff_subset
  have hRw0 : 0 ≤ wsum G m C R := hK.wsum_nonneg' sdiff_subset
  have hRm0 : 0 ≤ msum m R := msum_nonneg m R
  have hUm0 : 0 ≤ msum m U := msum_nonneg m U
  have hW8 := hK.wsum_eq_eight
  have hM4 := hK.msum_eq
  -- the per-petal data, as integers
  have hpet : ∀ T ∈ ℬ,
      msum m (T \ K) + 4 - 4 * (#(T \ K) : ℤ) - 2 * (#(cpr G C T \ L) : ℤ) +
          (ec G (T \ K) (cpr G C T \ L) : ℤ) =
        3 - ((ec G K (cpr G C T \ L) : ℤ) + ec G (T \ K) L) ∧
      wsum G m C K + wsum G m C (T \ K) ≤
        3 + 2 * (((#K : ℤ) - #L) + ((#(T \ K) : ℤ) - #(cpr G C T \ L))) ∧
      ((#K : ℤ) - #L) + ((#(T \ K) : ℤ) - #(cpr G C T \ L)) ≤
        msum m K + msum m (T \ K) - 3 ∧
      (1 : ℤ) ≤ #(T \ K) ∧ (0 : ℤ) ≤ #(cpr G C T \ L) ∧
      (0 : ℤ) ≤ (ec G (T \ K) (cpr G C T \ L) : ℤ) ∧
      (ec G (T \ K) (cpr G C T \ L) : ℤ) ≤ (#(T \ K) : ℤ) * #(cpr G C T \ L) ∧
      0 ≤ wsum G m C (T \ K) ∧ 0 ≤ msum m (T \ K) ∧
      msum m K + msum m (T \ K) ≤ 4 ∧ wsum G m C (T \ K) ≤ 2 * (#(T \ K) : ℤ) ∧
      (3 ≤ (#(T \ K) : ℤ) + #(cpr G C T \ L) →
        msum m (T \ K) + 4 - 4 * (#(T \ K) : ℤ) - 2 * (#(cpr G C T \ L) : ℤ) +
            (ec G (T \ K) (cpr G C T \ L) : ℤ) ≤
          msum m (T \ K) - 2 - ((#(T \ K) : ℤ) - #(cpr G C T \ L))) := by
    intro T hT
    obtain ⟨hTm, hT3⟩ := (memℬ T).1 hT
    obtain ⟨hθQ, hwQ, hkQ, hQ1⟩ := petal_facts hK hub hTm hT3
    have hKT := (hub.big T hTm hT3).1
    have hQA : T \ K ⊆ A := sdiff_subset.trans hTm.1
    have hJC' : cpr G C T \ L ⊆ C := sdiff_subset.trans (cpr_subset C T)
    have hmT := hK.msum_le hTm.1
    have hmTs := msum_sdiff_add m hKT
    have he : ec G (T \ K) (cpr G C T \ L) ≤ #(T \ K) * #(cpr G C T \ L) := ec_le_card_mul _ _
    unfold theta at hθQ
    refine ⟨hθQ, hwQ, hkQ, by exact_mod_cast hQ1, by positivity, by positivity,
      by exact_mod_cast he, hK.wsum_nonneg' hQA, msum_nonneg m _, by linarith,
      wsum_le_two_mul hcov hQA, fun h3 => ?_⟩
    have h := theta_le_of_three_le hK.block m hQA hJC' (by omega)
    unfold theta at h
    exact h
  have sEsplit : ∑ T ∈ ℬ, ((ec G K (cpr G C T \ L) : ℤ) + ec G (T \ K) L) =
      ∑ T ∈ ℬ, (ec G K (cpr G C T \ L) : ℤ) + ∑ T ∈ ℬ, (ec G (T \ K) L : ℤ) := sum_add_distrib
  rcases (by omega : (#K : ℤ) - #L = -1 ∨ (#K : ℤ) - #L = 0) with hβ | hδ
  · -- case (β): `κ(K⁺) = -1`, `w(K) = 0`, `∂_A(K⁺) = 0`, `∂_C(K⁺) = m(K) + 6`
    have hwK0 : wsum G m C K = 0 := by linarith
    have hecK0 : (ec G K (C \ L) : ℤ) = 0 := by linarith
    have hbd : (ec G L (A \ K) : ℤ) = msum m K + 6 := by linarith
    have hβT : ∀ T ∈ ℬ, 7 * wsum G m C (T \ K) ≤
        5 * (((ec G K (cpr G C T \ L) : ℤ) + ec G (T \ K) L) + msum m (T \ K)) := by
      intro T hT
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, -, h10, h11, h12⟩ := hpet T hT
      exact petal_beta h4 h5 h6 h7 h8 h1 h2 h3 h10 h11 h12 hβ hwK0
    have s1 := sum_le_sum hβT
    rw [← mul_sum, ← mul_sum, sum_add_distrib, sEsplit] at s1
    -- so `R` is a singleton `{u}` with `m(u) = 1`, `m(K) = 3`, and all `m(T - K) = 0`
    have hmR1 : 1 ≤ msum m R := by
      have : 6 + 5 * msum m R ≤ 7 * wsum G m C R := by linarith
      linarith
    have hmK3' : msum m K = 3 := by linarith
    have hmU0 : msum m U = 0 := by linarith
    have hmR : msum m R = 1 := by linarith
    have hcR : #R = 1 := by
      have h1 : (#R : ℤ) ≤ 1 := by linarith
      have h2 : R.Nonempty := by
        rw [nonempty_iff_ne_empty]
        intro h
        rw [h, msum_empty] at hmR
        omega
      have := h2.card_pos
      omega
    have hwR : wsum G m C R ≤ 2 := by
      rw [hcR] at hRw
      simpa using hRw
    have hmQ0 : ∀ T ∈ ℬ, msum m (T \ K) = 0 := by
      have h := (sum_eq_zero_iff_of_nonneg (fun T _ => msum_nonneg m (T \ K))).1 (sM ▸ hmU0)
      exact h
    -- per petal: `3 w(Q) ≤ 2E`, with equality only at a one-vertex petal
    have hsT : ∀ T ∈ ℬ, 0 ≤ 2 * ((ec G K (cpr G C T \ L) : ℤ) + ec G (T \ K) L) -
        3 * wsum G m C (T \ K) ∧
        (2 * ((ec G K (cpr G C T \ L) : ℤ) + ec G (T \ K) L) - 3 * wsum G m C (T \ K) = 0 →
          #(T \ K) = 1 ∧ #(cpr G C T \ L) = 0) := by
      intro T hT
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, -, -, h11, h12⟩ := hpet T hT
      obtain ⟨hle, heq⟩ := petal_beta_sing h4 h5 h6 h7 h8 h1 h2 h3 h11 h12 hβ hwK0
        (hmQ0 T hT) hmK3'
      refine ⟨by linarith, fun h => ?_⟩
      obtain ⟨hq, hj⟩ := heq (by linarith)
      exact ⟨by exact_mod_cast hq, by exact_mod_cast hj⟩
    have s2 : ∑ T ∈ ℬ, (2 * ((ec G K (cpr G C T \ L) : ℤ) + ec G (T \ K) L) -
        3 * wsum G m C (T \ K)) = 0 := by
      apply le_antisymm _ (sum_nonneg fun T hT => (hsT T hT).1)
      rw [sum_sub_distrib, ← mul_sum, ← mul_sum, sEsplit]
      linarith
    have heach := (sum_eq_zero_iff_of_nonneg fun T hT => (hsT T hT).1).1 s2
    have hone : ∀ T ∈ ℬ, #(T \ K) = 1 ∧ #(cpr G C T \ L) = 0 := fun T hT =>
      (hsT T hT).2 (heach T hT)
    -- each petal is one vertex `y` with `E = 3`, `w(y) = 2`; so there are three of them
    have hE3 : ∀ T ∈ ℬ, (ec G K (cpr G C T \ L) : ℤ) + ec G (T \ K) L = 3 := by
      intro T hT
      obtain ⟨h1, -, -, -, -, h6, h7, -⟩ := hpet T hT
      obtain ⟨hq, hj⟩ := hone T hT
      rw [hq, hj, hmQ0 T hT] at h1
      rw [hq, hj] at h7
      push_cast at h1 h7
      linarith
    have hw2 : ∀ T ∈ ℬ, wsum G m C (T \ K) = 2 := by
      intro T hT
      have h1 := heach T hT
      rw [hE3 T hT] at h1
      linarith
    have hsumE : ∑ T ∈ ℬ, ((ec G K (cpr G C T \ L) : ℤ) + ec G (T \ K) L) = 3 * #ℬ := by
      rw [sum_congr rfl hE3, sum_const, nsmul_eq_mul]
      ring
    have hsumW : ∑ T ∈ ℬ, wsum G m C (T \ K) = 2 * #ℬ := by
      rw [sum_congr rfl hw2, sum_const, nsmul_eq_mul]
      ring
    have hsumC : #U = #ℬ := by
      rw [sC, sum_congr rfl fun T hT => (hone T hT).1, sum_const, smul_eq_mul, mul_one]
    have hB3 : #ℬ = 3 := by
      have h1 : (#ℬ : ℤ) ≤ 3 := by linarith
      have h2 : (3 : ℤ) ≤ #ℬ := by linarith
      omega
    -- the vertex `c₀ ∈ C - K⁺_C` would have six neighbors in the four vertices of `A - K`
    have hcA : #A = #K + 4 := by omega
    have hcC := hK.block.card
    have hcL : #L = #K + 1 := by omega
    have hcCL : #(C \ L) = 1 := by
      have := card_sdiff_add_card_eq_card hLC
      omega
    obtain ⟨c₀, hc₀⟩ := card_pos.1 (by omega : 0 < #(C \ L))
    have hc₀C := (mem_sdiff.1 hc₀).1
    have hdK : dg G K c₀ = 0 := by
      have h0 : ec G (C \ L) K = 0 := by
        rw [ec_comm]
        exact_mod_cast hecK0
      have := single_le_sum (f := fun x => dg G K x) (fun _ _ => Nat.zero_le _) hc₀
      change dg G K c₀ ≤ ec G (C \ L) K at this
      omega
    have h6 := hK.block.satC c₀ hc₀C
    have hsplit := dg_sdiff_add (G := G) hub.subset c₀
    have hle := dg_le_card (G := G) (A \ K) c₀
    have hcAK := card_sdiff_add_card_eq_card hub.subset
    omega
  · -- case (δ): `κ(K⁺) = 0`, `m(K) = 4`, `R = ∅` (no singleton member), `∂(K⁺) = 8 - w(K)`
    have hmK4' : msum m K = 4 := by linarith
    have hmR0 : msum m R = 0 := by linarith
    have hcR0 : (#R : ℤ) = 0 := by linarith [(Nat.cast_nonneg #R : (0 : ℤ) ≤ #R)]
    have hwR0 : wsum G m C R = 0 := by linarith
    have hδT : ∀ T ∈ ℬ, wsum G m C (T \ K) + 1 ≤
        (ec G K (cpr G C T \ L) : ℤ) + ec G (T \ K) L := by
      intro T hT
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hpet T hT
      exact petal_delta h4 h5 h6 h7 h8 h9 hwK h1 h2 h3 h10 h11 h12 hδ hmK4'
    have s1 := sum_le_sum hδT
    rw [sum_add_distrib, sum_const, nsmul_eq_mul, mul_one, sEsplit] at s1
    obtain ⟨T, hT, hT3⟩ := hub.exists_big
    have hB : (1 : ℤ) ≤ #ℬ := by exact_mod_cast card_pos.2 ⟨T, (memℬ T).2 ⟨hT, hT3⟩⟩
    linarith

end Hub

/-! ### KL1 -/

/-- **KL1** in `θ*` form: under the covering hypothesis (`w ≤ 2` on `A`), some `p ∈ A` lies in no
overloaded set. -/
theorem kl1_thetaStar {A C : Finset V} {m : V → ℕ} (hK : KLData G A C m)
    (hcov : ∀ a ∈ A, 4 ≤ dg G C a + m a) :
    ∃ p ∈ A, ∀ T ⊆ A, p ∈ T → thetaStar G m C T ≤ 0 := by
  by_contra! hall
  have hall' : ∀ p ∈ A, ∃ T ⊆ A, p ∈ T ∧ 1 ≤ thetaStar G m C T := fun p hp => by
    obtain ⟨T, hT, hpT, h⟩ := hall p hp
    exact ⟨T, hT, hpT, by omega⟩
  obtain ⟨T₁, T₂, h₁, h₂, hne, h3⟩ := exists_hub_pair hK hall'
  exact hub_false hK hcov hall' (isHub_of_pair hK h₁ h₂ hne h3)

/-- **KL1**. Here `m(a)` is a multiplicity at each vertex `a` of the larger side `A` (in the
applications, the number of chosen edges at `a` that leave the block), with `m(A) = 4` and
`m(a) ≤ δ_a = 6 - d_a`; the covering hypothesis `hcov` says that every `a` with `d_a = 3` has
`m(a) ≥ 1` (`w = δ - m ≤ 2`). Then some `p ∈ A` lies in no overloaded set: no `A1 ⊆ A - p` is
under-supplied (`m(A1) < dem(A1)`). -/
theorem kl1 {A C : Finset V} (hX : IsBlock G A C) (m : V → ℕ)
    (hm : ∑ a ∈ A, m a = 4) (hmδ : ∀ a ∈ A, m a + dg G C a ≤ 6)
    (hcov : ∀ a ∈ A, 4 ≤ dg G C a + m a) :
    ∃ p ∈ A, ∀ A1 ⊆ A.erase p, dem G C A1 ≤ ∑ a ∈ A1, (m a : ℤ) := by
  have hm' : msum m A = 4 := by
    unfold msum
    exact_mod_cast hm
  exact exists_good_of_thetaStar hX hm' (kl1_thetaStar ⟨hX, hm', hmδ⟩ hcov)

end Erdos585.QB5
