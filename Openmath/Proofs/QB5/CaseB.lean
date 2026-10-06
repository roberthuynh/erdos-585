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
# QB(5): case (b) of the E5 assembly is rigid

Case (b) is the case of the E5 argument (`exists_good_vertex` in `E5.lean`) in which the chosen set
`M` of four cut edges misses exactly one in-degree-3 vertex `a` of a 2-block (in the other case `M`
covers every in-degree-3 vertex and `kl1` applies). The labels (2-block, in-block degree, supply,
demand, under-supplied, overloaded, weight) are defined in the module docstring of `Defs.lean`.

The setting is one 2-block `X = (A, C)` (`IsBlock`) and a supply `m : V → ℕ` on `A` (the number of
chosen cut edges at each vertex) with `m(A) = 4` and `m ≤ δ = 6 - d`, where `d_v = e(v, C)` is the
in-block degree; `dem(A1)` is `dem G C A1`. In case (b), `a` has `d_a = 3` and `m(a) = 0`, every
other vertex `v` has weight `w(v) = δ_v - m(v) ≤ 2` (for `v` with `d_v = 3` this says that `v` is
an end of `M`), and some `A1 ⊆ A - a` is under-supplied, `m(A1) < dem(A1)`; its complement
`T = A - A1` is then overloaded. Then (`caseb_rigid`) every `v ∈ T - a` has `m(v) = δ_v` (in
`E5.lean`: `v` has degree six and all its cut edges are chosen) and `m(T) ∈ {3, 4}`.

The proof uses `C' = {c ∈ C : e(c, T) ≥ 3}`, `C'' = C - C'`, `κ = |T| - |C'|`, `k = dem(A1)` and
`e'' = e(C'', T)`:

* `|A1| ≥ 5`: otherwise `e(c, A1) ≤ 4` for every `c`, so `dem(A1) = Σ_{A1} (4 - d_v) ≤ m(A1)`.
* `|T| ≥ 3`: otherwise `C' = ∅` and `dem(A1) = 8 - 4 |T| ≤ 4 - m(T) = m(A1)`.
* Counting at the split of `C`: `e(C', A1) = 8 - 4κ - k`; `w(T) + θ(T) + e'' = 2κ + 4` with
  `θ(T) = k - m(A1) ≥ 1`; the bound `g ≥ 12` of the block at `(T, C')` gives `κ + k ≤ 2`, and at
  `(A1, C'')` it gives `e'' ≥ 3κ`.
* The final count: `w(T) = 3 + w(T - a)` (`w(a) = 3`), so `κ ≥ 0`; `κ = 1` would need `k = 1`
  and `e'' ≥ 3`, too much; so `κ = 0`, `w(T - a) = e'' = 0`, `θ = 1`, `k ∈ {1, 2}` and
  `m(T) = 5 - k`.
-/

open Finset

namespace Erdos585.QB5

open QB4

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- **Case (b) is rigid.** In a 2-block `(A, C)` with a supply `m` (`m(A) = 4`, `m ≤ 6 - d`), let
`a ∈ A` have in-block degree 3 and `m(a) = 0`, let every other vertex `v` have `d_v + m(v) ≥ 4`,
and let `A1 ⊆ A - a` be under-supplied. Then every vertex `v ≠ a` of the overloaded set `A - A1`
has `m(v) + d_v = 6`, and `m(A - A1) ∈ {3, 4}`. -/
theorem caseb_rigid {A C : Finset V} (hX : IsBlock G A C) (m : V → ℕ)
    (hm : ∑ a ∈ A, m a = 4) (hmδ : ∀ a ∈ A, m a + dg G C a ≤ 6)
    {a : V} (ha : a ∈ A) (hda : dg G C a = 3) (hma : m a = 0)
    (hcov : ∀ v ∈ A, v ≠ a → 4 ≤ dg G C v + m v)
    {A1 : Finset V} (hA1 : A1 ⊆ A.erase a) (hunder : ∑ v ∈ A1, (m v : ℤ) < dem G C A1) :
    (∀ v ∈ A \ A1, v ≠ a → m v + dg G C v = 6) ∧
      3 ≤ ∑ v ∈ A \ A1, m v ∧ ∑ v ∈ A \ A1, m v ≤ 4 := by
  have hA1A : A1 ⊆ A := hA1.trans (erase_subset a A)
  have haA1 : a ∉ A1 := fun h => (mem_erase.1 (hA1 h)).1 rfl
  set T := A \ A1 with hTdef
  have haT : a ∈ T := mem_sdiff.2 ⟨ha, haA1⟩
  have hTA : T ⊆ A := sdiff_subset
  -- every `c ∈ C` has its six neighbors in `T` and `A1`
  have hsplit : ∀ c ∈ C, dg G T c + dg G A1 c = 6 := fun c hc => by
    rw [dg_sdiff_add hA1A c]
    exact hX.satC c hc
  have hcardA : #T + #A1 = #A := card_sdiff_add_card_eq_card hA1A
  have hcardAC := hX.card
  have hmsplit : ∑ v ∈ T, m v + ∑ v ∈ A1, m v = 4 := by
    rw [sum_sdiff hA1A]
    exact hm
  have hmA1 : (∑ v ∈ A1, (m v : ℤ)) = ((∑ v ∈ A1, m v : ℕ) : ℤ) := by push_cast; rfl
  unfold dem at hunder
  -- `|A1| ≥ 5`
  have hA15 : 5 ≤ #A1 := by
    by_contra hlt
    have hmin : ∑ c ∈ C, (min 4 (dg G A1 c) : ℤ) = ∑ c ∈ C, (dg G A1 c : ℤ) :=
      sum_congr rfl fun c _ => min_eq_right (by have := dg_le_card (G := G) A1 c; omega)
    have hcovA1 : ∑ _v ∈ A1, (4 : ℤ) ≤ ∑ v ∈ A1, ((dg G C v : ℤ) + m v) :=
      sum_le_sum fun v hv => by
        have := hcov v (hA1A hv) (fun h => haA1 (h ▸ hv))
        omega
    have hec : ∑ v ∈ A1, (dg G C v : ℤ) = ∑ c ∈ C, (dg G A1 c : ℤ) := by
      have := ec_comm (G := G) A1 C
      unfold ec at this
      exact_mod_cast this
    rw [sum_add_distrib, sum_const, nsmul_eq_mul] at hcovA1
    rw [hmin] at hunder
    linarith
  -- `m ≤ 3` on `A`
  have hm3 : ∀ v ∈ A, m v ≤ 3 := fun v hv => by
    have := hmδ v hv
    have := hX.three_le v hv
    omega
  -- `|T| ≥ 3`
  have hT3 : 3 ≤ #T := by
    by_contra hlt
    have hmin : ∑ c ∈ C, (min 4 (dg G A1 c) : ℤ) = ∑ _c ∈ C, (4 : ℤ) :=
      sum_congr rfl fun c hc => min_eq_left (by
        have := hsplit c hc
        have := dg_le_card (G := G) T c
        omega)
    have hmT : ∑ v ∈ T, m v ≤ 3 * #(T.erase a) := by
      rw [← add_sum_erase T m haT, hma, zero_add]
      calc ∑ v ∈ T.erase a, m v ≤ ∑ _v ∈ T.erase a, 3 :=
            sum_le_sum fun v hv => hm3 v (hTA (erase_subset a T hv))
        _ = 3 * #(T.erase a) := by rw [sum_const, smul_eq_mul, mul_comm]
    have hTe := card_erase_add_one haT
    rw [hmin, sum_const, nsmul_eq_mul] at hunder
    rw [hmA1] at hunder
    have hcast : ((∑ v ∈ A1, m v : ℕ) : ℤ) < 4 * #A1 - #C * 4 := hunder
    omega
  -- the split of `C` at `T`
  set C' := {c ∈ C | 3 ≤ dg G T c} with hC'def
  set C'' := {c ∈ C | ¬ 3 ≤ dg G T c} with hC''def
  have hcC : #C' + #C'' = #C := card_filter_add_card_filter_not _
  have hmin : ∑ c ∈ C, (min 4 (dg G A1 c) : ℤ) = 4 * #C'' + ∑ c ∈ C', (dg G A1 c : ℤ) := by
    rw [← sum_filter_add_sum_filter_not C (fun c => 3 ≤ dg G T c)]
    have h1 : ∑ c ∈ C', (min 4 (dg G A1 c) : ℤ) = ∑ c ∈ C', (dg G A1 c : ℤ) :=
      sum_congr rfl fun c hc => by
        obtain ⟨hcC, h3⟩ := mem_filter.1 hc
        have := hsplit c hcC
        exact min_eq_right (by omega)
    have h2 : ∑ c ∈ C'', (min 4 (dg G A1 c) : ℤ) = ∑ _c ∈ C'', (4 : ℤ) :=
      sum_congr rfl fun c hc => by
        obtain ⟨hcC, h3⟩ := mem_filter.1 hc
        have := hsplit c hcC
        exact min_eq_left (by omega)
    rw [h1, h2, sum_const, nsmul_eq_mul]
    ring
  have h6 : ∀ S ⊆ C, ∑ c ∈ S, (dg G T c : ℤ) + ∑ c ∈ S, (dg G A1 c : ℤ) = 6 * #S := by
    intro S hS
    rw [← sum_add_distrib, sum_congr rfl fun c hc => (by
      have := hsplit c (hS hc)
      omega : (dg G T c : ℤ) + dg G A1 c = 6), sum_const, nsmul_eq_mul]
    ring
  have h6' := h6 C' (filter_subset _ _)
  have h6'' := h6 C'' (filter_subset _ _)
  have hdT : ∑ v ∈ T, (dg G C v : ℤ) =
      ∑ c ∈ C', (dg G T c : ℤ) + ∑ c ∈ C'', (dg G T c : ℤ) := by
    have := ec_comm (G := G) T C
    unfold ec at this
    rw [← sum_filter_add_sum_filter_not C (fun c => 3 ≤ dg G T c)] at this
    exact_mod_cast this
  -- the bound `g ≥ 12` of the block at `(T, C')` and at `(A1, C'')`
  have hsp1 := hX.sparse T hTA C' (filter_subset _ _) (by omega)
  have hsp2 := hX.sparse A1 hA1A C'' (filter_subset _ _) (by omega)
  have hec1 : (ec G T C' : ℤ) = ∑ c ∈ C', (dg G T c : ℤ) := by
    rw [ec_comm]
    unfold ec
    push_cast
    rfl
  have hec2 : (ec G A1 C'' : ℤ) = ∑ c ∈ C'', (dg G A1 c : ℤ) := by
    rw [ec_comm]
    unfold ec
    push_cast
    rfl
  unfold gv at hsp1 hsp2
  -- the weight of `T`, with `w(a) = 3`
  have hw : ∑ v ∈ T, ((6 : ℤ) - dg G C v - m v) =
      3 + ∑ v ∈ T.erase a, ((6 : ℤ) - dg G C v - m v) := by
    rw [← add_sum_erase T _ haT, hda, hma]
    norm_num
  have hwT : ∑ v ∈ T, ((6 : ℤ) - dg G C v - m v) =
      6 * #T - ∑ v ∈ T, (dg G C v : ℤ) - ∑ v ∈ T, (m v : ℤ) := by
    rw [sum_sub_distrib, sum_sub_distrib, sum_const, nsmul_eq_mul]
    ring
  have hwnn : ∀ v ∈ T.erase a, 0 ≤ (6 : ℤ) - dg G C v - m v := fun v hv => by
    have := hmδ v (hTA (erase_subset a T hv))
    omega
  have hw0 := sum_nonneg hwnn
  have he''0 : 0 ≤ ∑ c ∈ C'', (dg G T c : ℤ) := sum_nonneg fun c _ => by positivity
  have hmT : (∑ v ∈ T, (m v : ℤ)) = ((∑ v ∈ T, m v : ℕ) : ℤ) := by push_cast; rfl
  rw [hmin] at hunder
  rw [hmA1] at hunder
  rw [hmT] at hwT
  have hmsplit' : ((∑ v ∈ T, m v : ℕ) : ℤ) + ((∑ v ∈ A1, m v : ℕ) : ℤ) = 4 := by
    exact_mod_cast hmsplit
  -- the final count: `w(T - a) = 0` and `3 ≤ m(T) ≤ 4`
  have key : ∑ v ∈ T.erase a, ((6 : ℤ) - dg G C v - m v) = 0 ∧
      3 ≤ ((∑ v ∈ T, m v : ℕ) : ℤ) ∧ ((∑ v ∈ T, m v : ℕ) : ℤ) ≤ 4 := by
    omega
  obtain ⟨hw', h3, h4⟩ := key
  refine ⟨fun v hv hva => ?_, by exact_mod_cast h3, by exact_mod_cast h4⟩
  have := (sum_eq_zero_iff_of_nonneg hwnn).1 hw' v (mem_erase.2 ⟨hva, hv⟩)
  omega

end Erdos585.QB5
