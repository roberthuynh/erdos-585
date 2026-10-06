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
import Openmath.Proofs.QB5.CaseB
import Openmath.Proofs.QB5.Cover
import Openmath.Proofs.QB5.KL1
import Openmath.Proofs.QB5.PairCriterion

/-!
# QB(5): a sparse E5 instance has a quartic subgraph

The E5 half of the proof of QB(5). The labels (E5 instance, sparse, 2-block, cut edges, supply,
under-supplied, in-degree-3 vertex, covers, rigid set, `GoodSide`, KL1) are defined in the module
docstring of `Defs.lean`.

`quartic_of_sparse_e5`: a sparse E5 instance has a quartic subgraph. If it had none, it would
have no 4-factor, hence a violated cut (`exists_violation_of_not_quartic`), which splits it into
two 2-blocks joined by seven cut edges (`e5_blocks`, in `PairCriterion.lean`). Index the seven cut
edges by `Fin 7`; `refined_cover` (`Cover.lean`) picks four of them, `M`. On each side, KL1
(`kl1`, when `M` covers every in-degree-3 vertex) or `caseb_rigid` (when `M` misses one, against
the rigid-set clause of `GoodSide`) gives a vertex at which no set is under-supplied by `M`:
`p ∈ A` with no under-supplied subset of `A - p`, and `q ∈ D = Q - C` with none in `D - q`. The
pair criterion (`cut_condition_of_good_pair`) and the 4-factor criterion (`exists_four_factor`)
then give a 4-factor of `(P - p, Q - q)`, which is a quartic subgraph of `(P, Q)`.
-/

open Finset

namespace Erdos585.QB5

open QB4

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ### The assembly -/

/-- Summing the fibers of `r` over `A1` counts the members of `M` that `r` maps into `A1`. -/
private lemma sum_card_fiber_eq {ι : Type*} [DecidableEq ι] (M : Finset ι) (r : ι → V)
    (A1 : Finset V) : ∑ v ∈ A1, #{i ∈ M | r i = v} = #{i ∈ M | r i ∈ A1} := by
  have := card_eq_sum_card_fiberwise (s := {i ∈ M | r i ∈ A1}) (t := A1) (f := r)
    (fun i hi => (mem_filter.1 hi).2)
  rw [this]
  refine sum_congr rfl fun v hv => ?_
  rw [filter_filter]
  refine congrArg card (filter_congr fun i _ => ?_)
  constructor
  · intro h
    exact ⟨h ▸ hv, h⟩
  · exact fun h => h.2

/-- **One block of the assembly.** Let `(A, C)` be a 2-block, and let `r i ∈ A` be the ends of
seven cut edges `i : Fin 7`, with `c_v + d_v ≤ 6` at every `v ∈ A` (`c_v` cut edges, in-block
degree `d_v`). If a 4-set `M` of cut edges satisfies `GoodSide` on this side, with `L` the
in-degree-3 vertices, then some `p ∈ A` has no under-supplied set in `A - p`. If `M` covers `L`,
this is KL1 (`kl1`). Otherwise `M` misses exactly one `a ∈ L`, and `p = a`: an under-supplied
`A1 ⊆ A - a` would make the cut ends in `(A - A1) - a` a rigid set (`caseb_rigid`), which
`GoodSide` excludes. -/
private lemma exists_good_vertex {A C : Finset V} (hX : IsBlock G A C) (r : Fin 7 → V)
    (hr : ∀ i, r i ∈ A) (hdeg : ∀ v ∈ A, #{j | r j = v} + dg G C v ≤ 6)
    {M : Finset (Fin 7)} (hM : #M = 4) (hgood : GoodSide r {v ∈ A | dg G C v = 3} M) :
    ∃ p ∈ A, ∀ A1 ⊆ A.erase p, dem G C A1 ≤ (#{i ∈ M | r i ∈ A1} : ℤ) := by
  set m : V → ℕ := fun v => #{i ∈ M | r i = v} with hmdef
  have hmc : ∀ v, m v ≤ #{j | r j = v} := fun v =>
    card_le_card (filter_subset_filter _ (subset_univ M))
  have hm : ∑ v ∈ A, m v = 4 := by
    rw [← hM]
    exact (card_eq_sum_card_fiberwise (s := M) (t := A) (f := r) fun i _ => hr i).symm
  have hmδ : ∀ v ∈ A, m v + dg G C v ≤ 6 := fun v hv => by
    have := hmc v
    have := hdeg v hv
    omega
  have hsum : ∀ A1 : Finset V, ∑ v ∈ A1, (m v : ℤ) = (#{i ∈ M | r i ∈ A1} : ℤ) := fun A1 => by
    rw [← sum_card_fiber_eq M r A1]
    push_cast
    rfl
  have hpos : ∀ v, (∃ i ∈ M, r i = v) ↔ 1 ≤ m v := fun v => by
    constructor
    · rintro ⟨i, hi, hiv⟩
      exact card_pos.2 ⟨i, mem_filter.2 ⟨hi, hiv⟩⟩
    · intro h1
      obtain ⟨i, hi⟩ := card_pos.1 h1
      exact ⟨i, (mem_filter.1 hi).1, (mem_filter.1 hi).2⟩
  by_cases hcovL : ∀ v ∈ {v ∈ A | dg G C v = 3}, ∃ i ∈ M, r i = v
  · -- `M` covers every in-degree-3 vertex: KL1 (`kl1`)
    obtain ⟨p, hp, hpgood⟩ := kl1 hX m hm hmδ fun v hv => by
      by_cases h3 : dg G C v = 3
      · have := (hpos v).1 (hcovL v (mem_filter.2 ⟨hv, h3⟩))
        omega
      · have := hX.three_le v hv
        omega
    exact ⟨p, hp, fun A1 hA1 => (hpgood A1 hA1).trans (hsum A1).le⟩
  · -- `M` misses exactly one in-degree-3 vertex `a`: case (b), `caseb_rigid`
    push Not at hcovL
    obtain ⟨a, haL, hamiss⟩ := hcovL
    obtain ⟨ha, hda⟩ := mem_filter.1 haL
    have hma : m a = 0 := by
      by_contra h0
      obtain ⟨i, hi, hia⟩ := (hpos a).2 (by omega)
      exact hamiss i hi hia
    have hcov' : ∀ v ∈ A, v ≠ a → 4 ≤ dg G C v + m v := fun v hv hva => by
      by_cases h3 : dg G C v = 3
      · by_contra hlt
        have hvmiss : ∀ i ∈ M, r i ≠ v := fun i hi hiv => by
          have := (hpos v).1 ⟨i, hi, hiv⟩
          omega
        exact hva (hgood.1 v (mem_filter.2 ⟨hv, h3⟩) a haL hvmiss hamiss)
      · have := hX.three_le v hv
        omega
    refine ⟨a, ha, fun A1 hA1 => ?_⟩
    rw [← hsum A1]
    by_contra hunder
    push Not at hunder
    obtain ⟨hrig, h3, h4⟩ := caseb_rigid hX m hm hmδ ha hda hma hcov' hA1 hunder
    set T := A \ A1 with hTdef
    have haT : a ∈ T := mem_sdiff.2 ⟨ha, fun h => (mem_erase.1 (hA1 h)).1 rfl⟩
    -- every cut edge at a vertex of `T - a` lies in `M`
    have hfull : ∀ v ∈ T.erase a,
        ({i ∈ M | r i = v} : Finset (Fin 7)) = ({j | r j = v} : Finset (Fin 7)) := fun v hv => by
      obtain ⟨hva, hvT⟩ := mem_erase.1 hv
      have h1 := hrig v hvT hva
      have h2 := hdeg v (sdiff_subset hvT)
      refine eq_of_subset_of_card_le (filter_subset_filter _ (subset_univ M)) ?_
      change #{j | r j = v} ≤ m v
      omega
    have hinM : ∀ j, r j ∈ T.erase a → j ∈ M := fun j hj => by
      have hj' : j ∈ ({j' | r j' = r j} : Finset (Fin 7)) := mem_filter.2 ⟨mem_univ j, rfl⟩
      rw [← hfull (r j) hj] at hj'
      exact (mem_filter.1 hj').1
    -- the rigid set: the cut ends in `T - a`
    set K := (univ.filter fun j => r j ∈ T.erase a).image r with hKdef
    have hmemK : ∀ v, v ∈ K ↔ v ∈ T.erase a ∧ ∃ j, r j = v := fun v => by
      simp only [hKdef, mem_image, mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨j, hj, rfl⟩
        exact ⟨hj, j, rfl⟩
      · rintro ⟨hv, j, rfl⟩
        exact ⟨j, hv, rfl⟩
    have haK : a ∉ K := fun h => (mem_erase.1 ((hmemK a).1 h).1).1 rfl
    have hKM : ∀ v ∈ K, ∃ i ∈ M, r i = v := fun v hv => by
      obtain ⟨hvT, j, rfl⟩ := (hmemK v).1 hv
      exact ⟨j, hinM j hvT, rfl⟩
    refine hgood.2 a haL hamiss K haK hKM ⟨fun v hvK hvL => ?_, fun j hj => ?_, ?_⟩
    · obtain ⟨hvT, -⟩ := (hmemK v).1 hvK
      have h1 := hrig v (mem_erase.1 hvT).2 (mem_erase.1 hvT).1
      have h2 := (mem_filter.1 hvL).2
      rw [← hfull v hvT]
      change m v = 3
      omega
    · exact hinM j ((hmemK (r j)).1 hj).1
    · have hcK : #{j | r j ∈ K} = ∑ v ∈ T.erase a, m v := by
        have hset : ({j | r j ∈ K} : Finset (Fin 7)) = {i ∈ M | r i ∈ T.erase a} := by
          ext j
          simp only [mem_filter, mem_univ, true_and, hmemK]
          constructor
          · rintro ⟨hj, -⟩
            exact ⟨hinM j hj, hj⟩
          · rintro ⟨-, hj⟩
            exact ⟨hj, j, rfl⟩
        rw [hset, ← sum_card_fiber_eq M r (T.erase a)]
      have hTa : ∑ v ∈ T, m v = ∑ v ∈ T.erase a, m v := by
        rw [← add_sum_erase T m haT, hma, zero_add]
      rw [hcK, ← hTa]
      omega

omit [DecidableEq V] in
/-- Indexing a finset `E` of pairs by `Fin n`: the indices `j` whose pair `f.symm j` has a property
are as many as the pairs of `E` with that property. -/
private lemma card_filter_equivFin {E : Finset (V × V)} {n : ℕ} (f : E ≃ Fin n)
    (φ : V × V → Prop) [DecidablePred φ] :
    #{j : Fin n | φ (f.symm j).1} = #{x ∈ E | φ x} := by
  refine card_bij (fun j _ => (f.symm j).1) (fun j hj => ?_) (fun j _ j' _ hjj => ?_)
    (fun x hx => ?_)
  · exact mem_filter.2 ⟨(f.symm j).2, (mem_filter.1 hj).2⟩
  · exact f.symm.injective (Subtype.ext hjj)
  · obtain ⟨hxE, hφ⟩ := mem_filter.1 hx
    exact ⟨f ⟨x, hxE⟩, mem_filter.2 ⟨mem_univ _, by simpa using hφ⟩, by simp⟩

/-- **A sparse E5 instance is never quartic-free.** Otherwise it has no 4-factor, so a violated
cut splits it into two 2-blocks joined by seven cut edges (`e5_blocks`); `refined_cover` chooses
four of them, `M`; each block has a vertex at which no set is under-supplied by `M`
(`exists_good_vertex`, through `kl1` or `caseb_rigid`), `p ∈ A` and `q ∈ Q - C`; and
`cut_condition_of_good_pair` with `exists_four_factor` gives a 4-factor of `(P - p, Q - q)`. -/
theorem quartic_of_sparse_e5 {P Q : Finset V} {a : ℕ} (h : IsE5 G P Q a)
    (hsp : Sparse5 G P Q) : Quartic G P Q := by
  by_contra hq
  have h5 := h.five_le
  have hgv := h.gv_eq
  have hcP := h.cardP
  have hcQ := h.cardQ
  obtain ⟨A, hA, C, hC, hviol⟩ := exists_violation_of_not_quartic (h.cardP.trans h.cardQ.symm)
    (card_pos.1 (by rw [h.cardQ]; omega)) hq
  obtain ⟨-, hcardB, -, hsatB, hcut, hDA, hDD, -, -, hXb, hYb⟩ := e5_blocks h hsp hA hC hviol
  have hδP : ∀ x ∈ P, 4 ≤ dg G Q x := fun x hx =>
    four_le_dg_of_sparse5_left hsp (by rw [hgv]) (by omega) hx
  have hδQ : ∀ y ∈ Q, 4 ≤ dg G P y := fun y hy =>
    four_le_dg_of_sparse5_right hsp (by rw [hgv]) (by omega) hy
  -- in-block degrees and cut degrees
  have hdQ : ∀ v ∈ A, dg G (Q \ C) v + dg G C v = dg G Q v := fun v _ => dg_sdiff_add hC v
  have hdP : ∀ w ∈ Q \ C, dg G (P \ A) w + dg G A w = dg G P w := fun w _ => dg_sdiff_add hA w
  -- the seven cut edges, indexed by `Fin 7`
  obtain ⟨f⟩ : Nonempty (adjPairs G A (Q \ C) ≃ Fin 7) :=
    ⟨equivFinOfCardEq (by rw [card_adjPairs, hcut])⟩
  obtain ⟨ra, hra⟩ : ∃ ra : Fin 7 → V, ∀ i, ra i = (f.symm i).1.1 := ⟨_, fun _ => rfl⟩
  obtain ⟨rd, hrd⟩ : ∃ rd : Fin 7 → V, ∀ i, rd i = (f.symm i).1.2 := ⟨_, fun _ => rfl⟩
  have hfE : ∀ i, (f.symm i).1 ∈ adjPairs G A (Q \ C) := fun i => (f.symm i).2
  have hraA : ∀ i, ra i ∈ A := fun i => by
    rw [hra]
    exact (mem_product.1 (mem_filter.1 (hfE i)).1).1
  have hrdD : ∀ i, rd i ∈ Q \ C := fun i => by
    rw [hrd]
    exact (mem_product.1 (mem_filter.1 (hfE i)).1).2
  have hcA : ∀ v ∈ A, #{j | ra j = v} = dg G (Q \ C) v := fun v hv => by
    simp only [hra]
    rw [card_filter_equivFin f (fun x => x.1 = v)]
    exact card_adjPairs_filter_fst hv
  have hcD : ∀ w ∈ Q \ C, #{j | rd j = w} = dg G A w := fun w hw => by
    simp only [hrd]
    rw [card_filter_equivFin f (fun x => x.2 = w)]
    exact card_adjPairs_filter_snd hw
  -- the hypotheses of `refined_cover`, with `L_A`, `L_D` the in-degree-3 vertices and `c` the
  -- number of cut edges at an end: `c ≤ 3`, and `c = 3` only in `L` (in-block degree at least 3);
  -- every vertex of `L` is an end (degree at least 4); and `Σ_L (3 - c) = D(L) ≤ 5`
  have hsimple : ∀ i j, ra i = ra j → rd i = rd j → i = j := fun i j h1 h2 => by
    rw [hra, hra] at h1
    rw [hrd, hrd] at h2
    exact f.symm.injective (Subtype.ext (Prod.ext h1 h2))
  have hca : ∀ i, #{j | ra j = ra i} ≤ 3 := fun i => by
    have := hcA (ra i) (hraA i)
    have := hdQ (ra i) (hraA i)
    have := hXb.three_le (ra i) (hraA i)
    have := h.degP (ra i) (hA (hraA i))
    omega
  have hcd : ∀ i, #{j | rd j = rd i} ≤ 3 := fun i => by
    have := hcD (rd i) (hrdD i)
    have := hdP (rd i) (hrdD i)
    have := hYb.three_le (rd i) (hrdD i)
    have := h.degQ (rd i) (sdiff_subset (hrdD i))
    omega
  have hLA : ∀ v ∈ {v ∈ A | dg G C v = 3}, ∃ i, ra i = v := fun v hv => by
    obtain ⟨hvA, hv3⟩ := mem_filter.1 hv
    have := hcA v hvA
    have := hdQ v hvA
    have := hδP v (hA hvA)
    obtain ⟨j, hj⟩ := card_pos.1 (by omega : 0 < #{j | ra j = v})
    exact ⟨j, (mem_filter.1 hj).2⟩
  have hLD : ∀ w ∈ {w ∈ Q \ C | dg G (P \ A) w = 3}, ∃ i, rd i = w := fun w hw => by
    obtain ⟨hwD, hw3⟩ := mem_filter.1 hw
    have := hcD w hwD
    have := hdP w hwD
    have := hδQ w (sdiff_subset hwD)
    obtain ⟨j, hj⟩ := card_pos.1 (by omega : 0 < #{j | rd j = w})
    exact ⟨j, (mem_filter.1 hj).2⟩
  have hLA3 : ∀ i, #{j | ra j = ra i} = 3 → ra i ∈ {v ∈ A | dg G C v = 3} := fun i hi => by
    have := hcA (ra i) (hraA i)
    have := hdQ (ra i) (hraA i)
    have := hXb.three_le (ra i) (hraA i)
    have := h.degP (ra i) (hA (hraA i))
    exact mem_filter.2 ⟨hraA i, by omega⟩
  have hLD3 : ∀ i, #{j | rd j = rd i} = 3 → rd i ∈ {w ∈ Q \ C | dg G (P \ A) w = 3} :=
    fun i hi => by
      have := hcD (rd i) (hrdD i)
      have := hdP (rd i) (hrdD i)
      have := hYb.three_le (rd i) (hrdD i)
      have := h.degQ (rd i) (sdiff_subset (hrdD i))
      exact mem_filter.2 ⟨hrdD i, by omega⟩
  have hbA : ∑ v ∈ {v ∈ A | dg G C v = 3}, (3 - #{j | ra j = v}) ≤ 5 := by
    have h1 : ((∑ v ∈ {v ∈ A | dg G C v = 3}, (3 - #{j | ra j = v}) : ℕ) : ℤ) =
        df G Q {v ∈ A | dg G C v = 3} := by
      push_cast [df]
      refine sum_congr rfl fun v hv => ?_
      obtain ⟨hvA, hv3⟩ := mem_filter.1 hv
      have := hcA v hvA
      have := hdQ v hvA
      have := h.degP v (hA hvA)
      omega
    have h2 := df_le_of_subset (G := G) (S := Q) (filter_subset (fun v => dg G C v = 3) A)
      fun v hv => h.degP v (hA hv)
    have h3 : ((∑ v ∈ {v ∈ A | dg G C v = 3}, (3 - #{j | ra j = v}) : ℕ) : ℤ) ≤ 5 := by
      rw [h1]
      exact h2.trans hDA.le
    exact_mod_cast h3
  have hbD : ∑ w ∈ {w ∈ Q \ C | dg G (P \ A) w = 3}, (3 - #{j | rd j = w}) ≤ 5 := by
    have h1 : ((∑ w ∈ {w ∈ Q \ C | dg G (P \ A) w = 3}, (3 - #{j | rd j = w}) : ℕ) : ℤ) =
        df G P {w ∈ Q \ C | dg G (P \ A) w = 3} := by
      push_cast [df]
      refine sum_congr rfl fun w hw => ?_
      obtain ⟨hwD, hw3⟩ := mem_filter.1 hw
      have := hcD w hwD
      have := hdP w hwD
      have := h.degQ w (sdiff_subset hwD)
      omega
    have h2 := df_le_of_subset (G := G) (S := P)
      (filter_subset (fun w => dg G (P \ A) w = 3) (Q \ C))
      fun w hw => h.degQ w (sdiff_subset hw)
    have h3 : ((∑ w ∈ {w ∈ Q \ C | dg G (P \ A) w = 3}, (3 - #{j | rd j = w}) : ℕ) : ℤ) ≤ 5 := by
      rw [h1]
      exact h2.trans hDD.le
    exact_mod_cast h3
  obtain ⟨M7, hM7, hgA, hgD⟩ := refined_cover ra rd hsimple hca hcd _ _ hLA hLD hLA3 hLD3 hbA hbD
  -- `exists_good_vertex` in each block: `p ∈ A` and `q ∈ Q - C`
  obtain ⟨p, hp, hpgood⟩ := exists_good_vertex hXb ra hraA (fun v hv => by
    have := hcA v hv
    have := hdQ v hv
    have := h.degP v (hA hv)
    omega) hM7 hgA
  obtain ⟨q, hq', hqgood⟩ := exists_good_vertex hYb rd hrdD (fun w hw => by
    have := hcD w hw
    have := hdP w hw
    have := h.degQ w (sdiff_subset hw)
    omega) hM7 hgD
  -- the chosen cut edges as adjacent pairs
  set M := M7.image fun i => (f.symm i).1 with hMdef
  have hginj : Function.Injective fun i => (f.symm i).1 := fun i j hij =>
    f.symm.injective (Subtype.ext hij)
  have hMadj : ∀ x ∈ M, G.Adj x.1 x.2 := fun x hx => by
    obtain ⟨i, -, rfl⟩ := mem_image.1 hx
    exact (mem_filter.1 (hfE i)).2
  have hM4 : #M ≤ 4 := card_image_le.trans hM7.le
  have hX : ∀ A1 ⊆ A.erase p, dem G C A1 ≤ (#{x ∈ M | x.1 ∈ A1} : ℤ) := fun A1 hA1 => by
    rw [hMdef, filter_image, card_image_of_injective _ hginj]
    have := hpgood A1 hA1
    simp only [hra] at this
    exact this
  have hY : ∀ D1 ⊆ (Q \ C).erase q, dem G (P \ A) D1 ≤ (#{x ∈ M | x.2 ∈ D1} : ℤ) :=
    fun D1 hD1 => by
      rw [hMdef, filter_image, card_image_of_injective _ hginj]
      have := hqgood D1 hD1
      simp only [hrd] at this
      exact this
  -- the cut condition of `(P - p, Q - q)`, Hall, and the quartic subgraph
  have hcutPQ := cut_condition_of_good_pair hC hcardB hsatB
    (fun b hb => h.degP b (sdiff_subset hb)) M hMadj hM4 hq' hX hY
  have hpP : p ∈ P := hA hp
  have hqQ : q ∈ Q := sdiff_subset hq'
  obtain ⟨F, hF, hadj, hFP, hFQ⟩ := exists_four_factor (P.erase p) (Q.erase q)
    (by rw [card_erase_of_mem hpP, card_erase_of_mem hqQ, h.cardP, h.cardQ]) hcutPQ
  have hQne : (Q.erase q).Nonempty := card_pos.1 (by rw [card_erase_of_mem hqQ, h.cardQ]; omega)
  exact hq ((quartic_of_four_factor (erase_subset p P) hQne hF hadj hFP hFQ).mono
    (erase_subset q Q) Subset.rfl).swap

end Erdos585.QB5
