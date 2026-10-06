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
import Openmath.Proofs.QB5.CoverCheck1
import Openmath.Proofs.QB5.CoverCheck2
import Openmath.Proofs.QB5.CoverCheck3
import Mathlib.Data.Fin.Tuple.Sort

/-!
# QB(5): the covering lemma for seven cut edges

`refined_cover`, the covering lemma, is a statement about seven edges `i : Fin 7`, the *cut edges*:
edge `i` joins its end `ra i` on the `A` side to its end `rd i` on the `D` side. Write `c` for the
number of cut edges at an end. Suppose that no two cut edges have the same two ends (the cut is
*simple*), that every end has `c ≤ 3`, and that `L_A`, `L_D` are sets of ends on the two sides that
contain every end with `c = 3` and have `Σ_L (3 - c) ≤ 5`. Then some four-set `M` of cut edges
satisfies `GoodSide` (`Defs.lean`) on both sides. Say that `M` *covers* an end if some edge of `M`
is at it, and *misses* it otherwise. On one side, `GoodSide` says that `M` misses at most one end in
`L`, and that if it misses one, `a`, then no rigid set consists of ends covered by `M` other than
`a`. A set `K` is *rigid* for `M` (`IsRigid`) if its members in `L` have three cut edges, every cut
edge at a member of `K` lies in `M`, and exactly three or four cut edges are at members of `K`.
`quartic_of_sparse_e5` (`E5.lean`) applies the lemma to the seven cut edges that join the two blocks
(`IsBlock`) of an E5 instance (`IsE5`), in the proof of QB(5) (`Erdos585.qb5`, `Statement.lean`).

The proof is a finite check that runs in the kernel: `CoverCheck.lean` defines the checker,
`CoverCheck1.lean` to `CoverCheck3.lean` run it with `decide +kernel` (kernel reduction only, no
compiled code), and this file proves that the runs imply `refined_cover`.

* Relabeling. Sorting the edges with `Tuple.sort` by the key of their `A` end, "more cut edges
  first, then least edge" (`key`), makes the edges at each end of the `A` side consecutive, with
  the number of edges per end non-increasing, so the code of the `A` side is one of the eight
  codes of `canonA` (`checkCanon`). The conclusion transfers back along the permutation
  (`goodSide_perm`).
* Codes. A side is coded by recording, for each edge, the least edge with the same end (`repF`,
  `codeOf`), and `L` by a mask over these representatives (`lmask`); the hypotheses on `L` make
  the mask admissible (`admissible_lmask`).
* Good masks. Call a cut edge *counted* for `M` if its end is outside `L` or has three cut edges,
  and every cut edge at that end lies in `M` (`zM`). For a side and an admissible `L`, the 35-bit
  mask `good` marks the four-sets that miss at most one end in `L` and, if they miss one, have at
  most two counted edges. `goodSide_of_testBit` proves that a marked four-set satisfies
  `GoodSide`: every edge at a rigid set is counted, and a rigid set is at three or four cut edges.
  Only this implication is proved, and it is all that the proof needs.
* The kernel runs say that for every canonical `A` code and every compatible `D` code (`compat`),
  every good mask of `A` shares a bit with every good mask of `D`. A common bit is the four-set
  `M`.
-/

open Finset

namespace Erdos585.QB5

namespace CoverCheck

/-! ### Primitive operations -/

/-- `Nat.land` is `&&&`. -/
private theorem land_eq (a b : ℕ) : Nat.land a b = a &&& b := rfl

/-- `Nat.lor` is `|||`. -/
private theorem lor_eq (a b : ℕ) : Nat.lor a b = a ||| b := rfl

/-- `Nat.xor` is `^^^`. -/
private theorem xor_eq (a b : ℕ) : Nat.xor a b = a ^^^ b := rfl

/-- `Nat.beq` decides equality. -/
private theorem beq_eq (a b : ℕ) : Nat.beq a b = decide (a = b) := by
  cases h : Nat.beq a b
  · simp [Nat.ne_of_beq_eq_false h]
  · simp [Nat.eq_of_beq_eq_true h]

/-- `Nat.ble` decides `≤`. -/
private theorem ble_eq (a b : ℕ) : Nat.ble a b = decide (a ≤ b) := by
  cases h : Nat.ble a b
  · have : ¬ a ≤ b := fun h' => by simp [Nat.ble_eq_true_of_le h'] at h
    simp [this]
  · simp [Nat.le_of_ble_eq_true h]

/-- `bitB` is `Nat.testBit`. -/
private theorem bitB_eq (m i : ℕ) : bitB m i = m.testBit i := by
  have h : Nat.land (Nat.shiftRight m i) 1 = m / 2 ^ i % 2 := by
    show (m >>> i) &&& 1 = _
    rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  rw [bitB, h, beq_eq, Nat.testBit_eq_decide_div_mod_eq]

/-- `dig g i` is the base-8 digit `i` of `g`. -/
private theorem dig_eq (g i : ℕ) : dig g i = g / 8 ^ i % 8 := by
  show (g >>> (3 * i)) &&& (2 ^ 3 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, pow_mul]
  norm_num

/-- The bits of `ALL` are the `k < 35`. -/
private theorem testBit_ALL (k : ℕ) : ALL.testBit k = decide (k < 35) := by
  rw [show ALL = 2 ^ 35 - 1 by rfl, Nat.testBit_two_pow_sub_one]

/-! ### Loops -/

/-- A successful `allBelow n f` gives `f i` for every `i < n`. -/
private theorem allBelow_eq_true {n : ℕ} {f : ℕ → Bool} (h : allBelow n f = true) :
    ∀ i < n, f i = true := by
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    intro i hi
    simp only [allBelow, Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact ih h.2 i hi
    · exact h.1

/-- `allBelow n f` succeeds when `f i` holds for every `i < n`. -/
private theorem allBelow_of_forall {n : ℕ} {f : ℕ → Bool} (h : ∀ i < n, f i = true) :
    allBelow n f = true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [allBelow, Bool.and_eq_true]
    exact ⟨h n (by omega), ih fun i hi => h i (by omega)⟩

/-! ### Masks and counts -/

/-- The bits of `maskOf p n` are the `i < n` with `p i`. -/
private theorem testBit_maskOf (p : ℕ → Bool) (n i : ℕ) :
    (maskOf p n).testBit i = (decide (i < n) && p i) := by
  induction n with
  | zero => simp [maskOf]
  | succ n ih =>
    rw [maskOf, lor_eq, Nat.testBit_or, ih]
    cases hp : p n
    · simp only [cond_false, Nat.zero_testBit, Bool.or_false]
      by_cases hin : i = n
      · subst hin; simp [hp]
      · by_cases hi : i < n
        · simp [hi, show i < n + 1 by omega]
        · simp [hi, show ¬ i < n + 1 by omega]
    · simp only [cond_true]
      rw [show Nat.shiftLeft 1 n = 2 ^ n from Nat.one_shiftLeft n, Nat.testBit_two_pow]
      by_cases hin : i = n
      · subst hin; simp [hp]
      · by_cases hi : i < n
        · simp [hi, show i < n + 1 by omega, Ne.symm hin]
        · simp [hi, show ¬ i < n + 1 by omega, Ne.symm hin]

/-- `maskOf p n` has no bit at `n` or above. -/
private theorem maskOf_lt (p : ℕ → Bool) (n : ℕ) : maskOf p n < 2 ^ n :=
  Nat.lt_pow_two_of_testBit _ fun i hi => by simp [testBit_maskOf, show ¬ i < n by omega]

/-- `cnt g v n` counts the edges `j < n` with representative `v`. -/
private theorem cnt_eq (g v n : ℕ) : cnt g v n = #{j ∈ range n | dig g j = v} := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [cnt, range_add_one, filter_insert, ih, beq_eq]
    by_cases h : dig g n = v
    · rw [if_pos h, card_insert_of_notMem (by simp)]
      simp [h]
    · rw [if_neg h]
      simp [h]

/-- Counting in `range 7` is counting in `Fin 7`. -/
private theorem card_range_seven (p : ℕ → Prop) [DecidablePred p] :
    #{j ∈ range 7 | p j} = #{j : Fin 7 | p j} := by
  symm
  apply Finset.card_bij (fun (j : Fin 7) _ => (j : ℕ))
  · intro j hj
    simp only [mem_filter, mem_univ, true_and] at hj
    simp [j.isLt, hj]
  · intro a _ b _ h
    exact Fin.ext h
  · intro b hb
    simp only [mem_filter, mem_range] at hb
    exact ⟨⟨b, hb.1⟩, by simpa using hb.2, rfl⟩

/-! ### The bit-parallel counters -/

/-- A four-set lies in the AND of the masks `t e` over the edges of an end if it lies in
each of them. -/
private theorem testBit_andBlk {g v k : ℕ} {t : ℕ → ℕ} (hk : k < 35) :
    ∀ n, (∀ e < n, dig g e = v → (t e).testBit k = true) → (andBlk g v t n).testBit k = true
  | 0, _ => by simp [andBlk, testBit_ALL, hk]
  | n + 1, h => by
    have ih := testBit_andBlk hk n fun e he => h e (by omega)
    rw [andBlk]
    cases hb : Nat.beq (dig g n) v
    · simpa using ih
    · have := h n (by omega) (Nat.eq_of_beq_eq_true hb)
      simp [Nat.testBit_and, this, ih]

/-- `u1` marks every four-set that misses the end of some `L`-representative (a representative
whose end is in `L`, `isLRep`). -/
private theorem testBit_u1 {g l k : ℕ} : ∀ n, ∀ r < n, isLRep g l r = true →
    (missR g r).testBit k = true → (u1 g l n).testBit k = true
  | 0, r, hr, _, _ => absurd hr (Nat.not_lt_zero _)
  | n + 1, r, hr, hL, hm => by
    rw [u1]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hr with hr | rfl
    · have ih := testBit_u1 n r hr hL hm
      cases isLRep g l n <;> simp [Nat.testBit_or, ih]
    · simp [hL, Nat.testBit_or, hm]

/-- `u2` marks every four-set that misses the ends of two different `L`-representatives. -/
private theorem testBit_u2 {g l k : ℕ} : ∀ n, ∀ r < n, ∀ r' < n, r ≠ r' →
    isLRep g l r = true → isLRep g l r' = true → (missR g r).testBit k = true →
    (missR g r').testBit k = true → (u2 g l n).testBit k = true
  | 0, r, hr, _, _, _, _, _, _, _ => absurd hr (Nat.not_lt_zero _)
  | n + 1, r, hr, r', hr', hne, hL, hL', hm, hm' => by
    rw [u2]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hr with hr | rfl
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hr' with hr' | rfl
      · have ih := testBit_u2 n r hr r' hr' hne hL hL' hm hm'
        cases isLRep g l n <;> simp [Nat.testBit_or, ih]
      · have h1 := testBit_u1 r' r hr hL hm
        simp [hL', Nat.testBit_or, Nat.testBit_and, h1, hm']
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hr' with hr' | rfl
      · have h1 := testBit_u1 r r' hr' hL' hm'
        simp [hL, Nat.testBit_or, Nat.testBit_and, h1, hm]
      · exact absurd rfl hne

/-- `f1`, `f2`, `f3` mark every four-set with at least one, two, three counted edges. -/
private theorem testBit_f {g l k : ℕ} : ∀ n,
    (1 ≤ #{j ∈ range n | (zM g l j).testBit k = true} → (f1 g l n).testBit k = true) ∧
    (2 ≤ #{j ∈ range n | (zM g l j).testBit k = true} → (f2 g l n).testBit k = true) ∧
    (3 ≤ #{j ∈ range n | (zM g l j).testBit k = true} → (f3 g l n).testBit k = true)
  | 0 => by simp
  | n + 1 => by
    obtain ⟨ih1, ih2, ih3⟩ := testBit_f (g := g) (l := l) (k := k) n
    rw [range_add_one, filter_insert]
    simp only [f1, f2, f3, lor_eq, land_eq, Nat.testBit_or, Nat.testBit_and]
    by_cases hz : (zM g l n).testBit k = true
    · rw [if_pos hz, card_insert_of_notMem (by simp)]
      refine ⟨fun _ => by simp [hz], fun h => ?_, fun h => ?_⟩
      · simp [hz, ih1 (by omega)]
      · simp [hz, ih2 (by omega)]
    · rw [if_neg hz]
      exact ⟨fun h => by simp [ih1 h], fun h => by simp [ih2 h], fun h => by simp [ih3 h]⟩

/-- A good four-set has number below 35, misses at most one end in `L`, and if it misses one,
has fewer than three counted edges. -/
private theorem testBit_good {g l k : ℕ} (h : (good g l).testBit k = true) :
    k < 35 ∧ (u2 g l 7).testBit k = false ∧
      ((u1 g l 7).testBit k = false ∨ (f3 g l 7).testBit k = false) := by
  simp only [good, xor_eq, land_eq, lor_eq, Nat.testBit_xor, Nat.testBit_and, Nat.testBit_or,
    testBit_ALL] at h
  by_cases hk : k < 35
  · simp only [hk, decide_true, Bool.true_and] at h
    refine ⟨hk, ?_, ?_⟩
    · cases h2 : (u2 g l 7).testBit k <;> simp_all
    · cases h1 : (u1 g l 7).testBit k <;> cases h3 : (f3 g l 7).testBit k <;> simp_all
  · simp [hk] at h

/-- The good mask of an admissible `l < n` is listed by `masksAux g n`. -/
private theorem mem_masksAux {g l : ℕ} (ha : admissible g l = true) :
    ∀ n, l < n → good g l ∈ masksAux g n
  | 0, h => absurd h (Nat.not_lt_zero _)
  | n + 1, h => by
    rw [masksAux]
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | rfl
    · have ih := mem_masksAux ha n h
      cases admissible g n <;> simp [ih]
    · simp [ha]

/-- `pairOK` gives a common four-set of any two listed masks. -/
private theorem exists_of_pairOK {xs ys : List ℕ} (h : pairOK xs ys = true) {x y : ℕ}
    (hx : x ∈ xs) (hy : y ∈ ys) : ∃ k, x.testBit k = true ∧ y.testBit k = true := by
  simp only [pairOK, List.all_eq_true] at h
  have hxy := h x hx y hy
  have hne : x &&& y ≠ 0 := by simpa [beq_eq, land_eq] using hxy
  obtain ⟨k, hk⟩ := Nat.exists_testBit_of_ne_zero hne
  exact ⟨k, by simpa [Nat.testBit_and] using hk⟩

/-! ### The tables of four-sets -/

/-- The four-set of edges with number `k`. -/
private def Mset (k : ℕ) : Finset (Fin 7) := {e | (Mk k).testBit e}

/-- The table `cM` lists the four-sets that contain each edge (kernel evaluation). -/
private theorem testBit_cM : ∀ k < 35, ∀ e < 7, (cM e).testBit k = (Mk k).testBit e := by
  decide +kernel

/-- The table `ncM` lists the four-sets that miss each edge (kernel evaluation). -/
private theorem testBit_ncM : ∀ k < 35, ∀ e < 7, (ncM e).testBit k = !(Mk k).testBit e := by
  decide +kernel

/-- Each four-set `Mset k`, `k < 35`, has four edges (kernel evaluation). -/
private theorem card_Mset : ∀ k < 35, #(Mset k) = 4 := by
  decide +kernel

/-- `size g j` is the number of edges with the same representative as `j`. -/
private theorem size_eq (g : ℕ) (j : Fin 7) : size g j = #{j' : Fin 7 | dig g j' = dig g j} := by
  rw [size, cnt_eq, card_range_seven]

/-! ### One side -/

/-- A set bit `k` of `good c l` gives `GoodSide` for the four-set `Mset k` on one side, for every
`r` whose ends are coded by `c` and every `L` coded by `l`. -/
private theorem goodSide_of_testBit {α : Type*} [DecidableEq α] {r : Fin 7 → α} {L : Finset α}
    {c l k : ℕ} (hc : ∀ i j : Fin 7, r i = r j ↔ dig c i = dig c j)
    (hlt : ∀ i : Fin 7, dig c i < 7) (hidem : ∀ i : Fin 7, dig c (dig c i) = dig c i)
    (hl : ∀ i : Fin 7, r i ∈ L ↔ l.testBit (dig c i) = true) (hL : ∀ v ∈ L, ∃ i, r i = v)
    (hk : (good c l).testBit k = true) : GoodSide r L (Mset k) := by
  obtain ⟨hk35, hu2, hu1f3⟩ := testBit_good hk
  have hmiss : ∀ i : Fin 7, (∀ j ∈ Mset k, r j ≠ r i) →
      (missR c (dig c i)).testBit k = true := by
    intro i hi
    refine testBit_andBlk hk35 7 fun e he hde => ?_
    rw [testBit_ncM k hk35 e he]
    have hre : r ⟨e, he⟩ = r i := (hc _ _).2 hde
    have hnot : (⟨e, he⟩ : Fin 7) ∉ Mset k := fun hm => hi _ hm hre
    simpa [Mset] using hnot
  have hrep : ∀ i : Fin 7, r i ∈ L → isLRep c l (dig c i) = true := by
    intro i hi
    simp [isLRep, hidem i, bitB_eq, (hl i).1 hi]
  refine ⟨fun a ha b hb hua hub => ?_, fun a ha hua K _ _ hrig => ?_⟩
  · obtain ⟨i, rfl⟩ := hL a ha
    obtain ⟨j, rfl⟩ := hL b hb
    by_contra hne
    have hd : dig c i ≠ dig c j := fun h => hne ((hc i j).2 h)
    have h2 := testBit_u2 7 (dig c i) (hlt i) (dig c j) (hlt j) hd (hrep i ha) (hrep j hb)
      (hmiss i hua) (hmiss j hub)
    rw [h2] at hu2
    exact Bool.noConfusion hu2
  · obtain ⟨i, rfl⟩ := hL a ha
    have hu1 := testBit_u1 7 (dig c i) (hlt i) (hrep i ha) (hmiss i hua)
    have hf3 : (f3 c l 7).testBit k = false := by
      rcases hu1f3 with h | h
      · rw [hu1] at h
        exact Bool.noConfusion h
      · exact h
    have hcount : #{j ∈ range 7 | (zM c l j).testBit k = true} ≤ 2 := by
      by_contra h
      have h3 := (testBit_f (g := c) (l := l) (k := k) 7).2.2 (by omega)
      rw [h3] at hf3
      exact Bool.noConfusion hf3
    obtain ⟨hK1, hK2, hK3⟩ := hrig
    have hz : ∀ j : Fin 7, r j ∈ K → (zM c l j).testBit k = true := by
      intro j hj
      have hcond : (!bitB l (dig c j) || Nat.beq (size c j) 3) = true := by
        cases hb : bitB l (dig c j)
        · rfl
        · have hjL : r j ∈ L := (hl j).2 (by rw [← bitB_eq]; exact hb)
          have hs : size c j = 3 := by
            rw [size_eq, ← hK1 (r j) hj hjL]
            congr 1
            ext j'
            simp [hc]
          simp [hs]
      rw [zM, hcond, cond_true]
      refine testBit_andBlk hk35 7 fun e he hde => ?_
      rw [testBit_cM k hk35 e he]
      have hre : r ⟨e, he⟩ = r j := (hc _ _).2 hde
      have hm : (⟨e, he⟩ : Fin 7) ∈ Mset k := hK2 _ (hre ▸ hj)
      simpa [Mset] using hm
    have hle : #{j | r j ∈ K} ≤ #{j ∈ range 7 | (zM c l j).testBit k = true} := by
      rw [card_range_seven]
      exact card_le_card fun j hj => by
        simp only [mem_filter, mem_univ, true_and] at hj ⊢
        exact hz j hj
    omega

/-! ### Codes of the two sides -/

section Codes

variable {α : Type*} [DecidableEq α]

/-- The least edge with the same end as edge `i`. -/
private def repF (r : Fin 7 → α) (i : Fin 7) : Fin 7 :=
  ({j | r j = r i} : Finset (Fin 7)).min' ⟨i, by simp⟩

/-- Edge `repF r i` has the same end as edge `i`. -/
private theorem repF_spec (r : Fin 7 → α) (i : Fin 7) : r (repF r i) = r i := by
  have h := min'_mem ({j | r j = r i} : Finset (Fin 7)) ⟨i, by simp⟩
  simp only [mem_filter, mem_univ, true_and] at h
  exact h

/-- `repF r i` is at most `i`. -/
private theorem repF_le (r : Fin 7 → α) (i : Fin 7) : repF r i ≤ i :=
  min'_le _ _ (by simp)

/-- Two edges have the same least edge if and only if they have the same end. -/
private theorem repF_eq_iff (r : Fin 7 → α) (i j : Fin 7) :
    repF r i = repF r j ↔ r i = r j := by
  refine ⟨fun h => by rw [← repF_spec r i, h, repF_spec r j], fun h => le_antisymm ?_ ?_⟩
  · exact min'_le _ _ (by simp [repF_spec, h])
  · exact min'_le _ _ (by simp [repF_spec, h])

/-- `repF r` is idempotent. -/
private theorem repF_repF (r : Fin 7 → α) (i : Fin 7) : repF r (repF r i) = repF r i :=
  (repF_eq_iff r _ _).2 (repF_spec r i)

/-- The digits of `mkCode`. -/
private theorem dig_mkCode {d1 d2 d3 d4 d5 d6 : ℕ} (h1 : d1 < 8) (h2 : d2 < 8) (h3 : d3 < 8)
    (h4 : d4 < 8) (h5 : d5 < 8) (h6 : d6 < 8) (i : Fin 7) :
    dig (mkCode d1 d2 d3 d4 d5 d6) i = ![0, d1, d2, d3, d4, d5, d6] i := by
  simp only [dig_eq, mkCode, Nat.add_eq, Nat.mul_eq]
  fin_cases i <;> simp <;> omega

/-- The side code of `r`: digit `i` is the least edge with the same end as edge `i`. -/
private def codeOf (r : Fin 7 → α) : ℕ :=
  mkCode (repF r 1) (repF r 2) (repF r 3) (repF r 4) (repF r 5) (repF r 6)

/-- Digit `i` of `codeOf r` is `repF r i`. -/
private theorem dig_codeOf (r : Fin 7 → α) (i : Fin 7) : dig (codeOf r) i = repF r i := by
  have hb : ∀ j : Fin 7, (repF r j : ℕ) < 8 := fun j => by have := (repF r j).isLt; omega
  rw [codeOf, dig_mkCode (hb 1) (hb 2) (hb 3) (hb 4) (hb 5) (hb 6)]
  have h0 : (repF r 0 : ℕ) = 0 := by
    have := repF_le r 0
    rw [Fin.le_def] at this
    simpa using this
  fin_cases i <;> simp [h0]

/-- Two edges have the same end if and only if their digits in `codeOf r` agree. -/
private theorem codeOf_iff (r : Fin 7 → α) (i j : Fin 7) :
    r i = r j ↔ dig (codeOf r) i = dig (codeOf r) j := by
  rw [dig_codeOf, dig_codeOf, Fin.val_inj, repF_eq_iff]

/-- The digits of `codeOf r` are edges. -/
private theorem codeOf_lt (r : Fin 7 → α) (i : Fin 7) : dig (codeOf r) i < 7 := by
  rw [dig_codeOf]
  exact (repF r i).isLt

/-- The digits of `codeOf r` are representatives. -/
private theorem codeOf_idem (r : Fin 7 → α) (i : Fin 7) :
    dig (codeOf r) (dig (codeOf r) i) = dig (codeOf r) i := by
  rw [dig_codeOf r i, dig_codeOf r (repF r i), repF_repF]

/-- `size (codeOf r) i` is the number of cut edges at the end of edge `i`. -/
private theorem size_codeOf (r : Fin 7 → α) (i : Fin 7) :
    size (codeOf r) i = #{j | r j = r i} := by
  rw [size_eq]
  congr 1
  ext j
  simp [codeOf_iff]

/-- The `L`-mask of `L`: the representatives whose end lies in `L`. -/
private def lmask (r : Fin 7 → α) (L : Finset α) : ℕ :=
  maskOf (fun i => decide (∃ j : Fin 7, (j : ℕ) = i ∧ repF r j = j ∧ r j ∈ L)) 7

/-- The bits of `lmask r L`. -/
private theorem testBit_lmask (r : Fin 7 → α) (L : Finset α) (i : ℕ) :
    (lmask r L).testBit i = true ↔ ∃ j : Fin 7, (j : ℕ) = i ∧ repF r j = j ∧ r j ∈ L := by
  rw [lmask, testBit_maskOf]
  constructor
  · intro h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.2
  · rintro ⟨j, rfl, h⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨j.isLt, j, rfl, h⟩

/-- The bits of `lmask r L` at the edges. -/
private theorem testBit_lmask_fin (r : Fin 7 → α) (L : Finset α) (i : Fin 7) :
    (lmask r L).testBit i = true ↔ repF r i = i ∧ r i ∈ L := by
  rw [testBit_lmask]
  constructor
  · rintro ⟨j, hj, h⟩
    obtain rfl : j = i := Fin.ext hj
    exact h
  · intro h
    exact ⟨i, rfl, h⟩

/-- An end lies in `L` if and only if the bit of its representative is set in `lmask r L`. -/
private theorem mem_iff_lmask (r : Fin 7 → α) (L : Finset α) (i : Fin 7) :
    r i ∈ L ↔ (lmask r L).testBit (dig (codeOf r) i) = true := by
  rw [dig_codeOf, testBit_lmask_fin, repF_repF, repF_spec r i]
  simp

/-- `budget` as a sum. -/
private theorem budget_eq (g l n : ℕ) :
    budget g l n = ∑ i ∈ range n, cond (bitB l i) (3 - size g i) 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [budget, sum_range_succ, ih]; rfl

/-- Under the hypotheses of `refined_cover` on `L` (its members are ends, it contains every end
with three cut edges, and `Σ_L (3 - c) ≤ 5`), `lmask r L` is admissible for `codeOf r`. -/
private theorem admissible_lmask {r : Fin 7 → α} {L : Finset α}
    (hL : ∀ v ∈ L, ∃ i, r i = v) (hL3 : ∀ i, #{j | r j = r i} = 3 → r i ∈ L)
    (hb : ∑ v ∈ L, (3 - #{j | r j = v}) ≤ 5) :
    admissible (codeOf r) (lmask r L) = true := by
  simp only [admissible, Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [beq_eq, decide_eq_true_eq, land_eq, xor_eq]
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit]
    cases h : (lmask r L).testBit i
    · simp
    · obtain ⟨j, rfl, hj, -⟩ := (testBit_lmask r L _).1 h
      have hrep : (repMask (codeOf r)).testBit j = true := by
        rw [repMask, testBit_maskOf]
        simp [j.isLt, dig_codeOf, hj]
      rw [hrep, show (127 : ℕ) = 2 ^ 7 - 1 from rfl, Nat.testBit_two_pow_sub_one]
      simp [j.isLt]
  · refine allBelow_of_forall fun i hi => ?_
    have hdi : dig (codeOf r) i = repF r ⟨i, hi⟩ := dig_codeOf r ⟨i, hi⟩
    have hsi : size (codeOf r) i = #{j | r j = r ⟨i, hi⟩} := size_codeOf r ⟨i, hi⟩
    cases hc : (Nat.beq (dig (codeOf r) i) i && Nat.beq (size (codeOf r) i) 3)
    · rfl
    · simp only [Bool.and_eq_true, beq_eq, decide_eq_true_eq] at hc
      have hrep : repF r ⟨i, hi⟩ = ⟨i, hi⟩ := Fin.ext (hdi ▸ hc.1)
      have hin : r ⟨i, hi⟩ ∈ L := hL3 _ (hsi ▸ hc.2)
      simp only [Bool.not_true, Bool.false_or, bitB_eq]
      exact (testBit_lmask_fin r L ⟨i, hi⟩).2 ⟨hrep, hin⟩
  · rw [ble_eq, decide_eq_true_eq]
    let S : Finset (Fin 7) := {i | repF r i = i ∧ r i ∈ L}
    have himg : S.image r = L := by
      ext v
      simp only [S, mem_image, mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨i, ⟨-, hi⟩, rfl⟩
        exact hi
      · intro hv
        obtain ⟨i, rfl⟩ := hL v hv
        exact ⟨repF r i, ⟨repF_repF r i, by rw [repF_spec r i]; exact hv⟩, repF_spec r i⟩
    have hinj : ∀ x ∈ S, ∀ y ∈ S, r x = r y → x = y := by
      intro x hx y hy hxy
      simp only [S, mem_filter, mem_univ, true_and] at hx hy
      rw [← hx.1, ← hy.1]
      exact (repF_eq_iff r x y).2 hxy
    have hsum : ∑ v ∈ L, (3 - #{j | r j = v}) = ∑ i ∈ S, (3 - #{j | r j = r i}) := by
      calc ∑ v ∈ L, (3 - #{j | r j = v}) = ∑ v ∈ S.image r, (3 - #{j | r j = v}) := by
            rw [himg]
        _ = ∑ i ∈ S, (3 - #{j | r j = r i}) := sum_image hinj
    have hbud : budget (codeOf r) (lmask r L) 7 = ∑ i ∈ S, (3 - #{j | r j = r i}) := by
      rw [budget_eq, Finset.sum_range, sum_filter]
      refine sum_congr rfl fun i _ => ?_
      rw [bitB_eq, size_codeOf]
      by_cases h : repF r i = i ∧ r i ∈ L
      · rw [(testBit_lmask_fin r L i).2 h, if_pos h]
        rfl
      · have h' : (lmask r L).testBit i = false := by
          cases h'' : (lmask r L).testBit i
          · rfl
          · exact absurd ((testBit_lmask_fin r L i).1 h'') h
        rw [h', if_neg h]
        rfl
    rw [hbud, ← hsum]
    exact hb

/-- `codeOf r` passes `validSide` when every end has at most three cut edges. -/
private theorem validSide_codeOf {r : Fin 7 → α} (h3 : ∀ i, #{j | r j = r i} ≤ 3) :
    validSide (codeOf r) = true := by
  refine allBelow_of_forall fun i hi => ?_
  simp only [Bool.and_eq_true, beq_eq, ble_eq, decide_eq_true_eq]
  exact ⟨codeOf_idem r ⟨i, hi⟩, by rw [size_codeOf r ⟨i, hi⟩]; exact h3 _⟩

/-- The codes of the two sides of a simple cut (no two edges with the same two ends) are
compatible. -/
private theorem compat_codeOf {β : Type*} [DecidableEq β] {ra : Fin 7 → α} {rd : Fin 7 → β}
    (hsimple : ∀ i j, ra i = ra j → rd i = rd j → i = j) :
    compat (codeOf ra) (codeOf rd) = true := by
  refine allBelow_of_forall fun i hi => allBelow_of_forall fun j hj => ?_
  have h := hsimple ⟨j, by omega⟩ ⟨i, hi⟩
  rw [codeOf_iff ra, codeOf_iff rd] at h
  cases hc : (Nat.beq (dig (codeOf ra) j) (dig (codeOf ra) i) &&
      Nat.beq (dig (codeOf rd) j) (dig (codeOf rd) i))
  · rfl
  · simp only [Bool.and_eq_true, beq_eq, decide_eq_true_eq] at hc
    have := h hc.1 hc.2
    simp only [Fin.mk.injEq] at this
    omega

/-- `codeOf r` is canonical when the edges are sorted by a key `κ` whose level sets are the
ends and along which the number of cut edges does not increase. -/
private theorem canonical_codeOf {r : Fin 7 → α} (h3 : ∀ i, #{j | r j = r i} ≤ 3)
    {κ : Fin 7 → ℕ} (hmono : Monotone κ) (hκ : ∀ i j, κ i = κ j ↔ r i = r j)
    (hsz : ∀ i j, κ i ≤ κ j → #{l | r l = r j} ≤ #{l | r l = r i}) :
    canonical (codeOf r) = true := by
  simp only [canonical, Bool.and_eq_true]
  refine ⟨⟨validSide_codeOf h3, allBelow_of_forall fun i hi => ?_⟩,
    allBelow_of_forall fun i hi => ?_⟩
  · have hab : (⟨i, by omega⟩ : Fin 7) ≤ ⟨i + 1, by omega⟩ := Fin.mk_le_mk.2 (by omega)
    have hda : dig (codeOf r) i = repF r ⟨i, by omega⟩ := dig_codeOf r ⟨i, by omega⟩
    have hdb : dig (codeOf r) (i + 1) = repF r ⟨i + 1, by omega⟩ := dig_codeOf r ⟨i + 1, by omega⟩
    simp only [Bool.or_eq_true, beq_eq, decide_eq_true_eq]
    by_cases hr : r ⟨i, by omega⟩ = r ⟨i + 1, by omega⟩
    · right
      rw [hda, hdb, (repF_eq_iff r _ _).2 hr.symm]
    · left
      rw [hdb]
      have hle := repF_le r ⟨i + 1, by omega⟩
      rw [Fin.le_def] at hle
      by_contra hne
      have hlt : repF r ⟨i + 1, by omega⟩ ≤ ⟨i, by omega⟩ := by
        rw [Fin.le_def]
        simp only at hle hne ⊢
        omega
      have h1 : κ (repF r ⟨i + 1, by omega⟩) = κ ⟨i + 1, by omega⟩ :=
        (hκ _ _).2 (repF_spec r _)
      have h2 := hmono hlt
      have h4 := hmono hab
      exact hr ((hκ _ _).1 (by omega))
  · simp only [ble_eq, decide_eq_true_eq]
    rw [size_codeOf r ⟨i + 1, by omega⟩, size_codeOf r ⟨i, by omega⟩]
    exact hsz _ _ (hmono (Fin.mk_le_mk.2 (by omega)))

end Codes

/-! ### Relabeling the edges -/

/-- Relabeling the edges by a permutation keeps counts. -/
private theorem card_filter_perm (σ : Equiv.Perm (Fin 7)) (p : Fin 7 → Prop) [DecidablePred p] :
    #{j | p (σ j)} = #{j | p j} := by
  apply card_bij (fun j _ => σ j)
  · intro j hj
    simpa using hj
  · intro a _ b _ h
    exact σ.injective h
  · intro b hb
    exact ⟨σ.symm b, by simpa using hb, by simp⟩

/-- `GoodSide` transfers back along a relabeling of the edges. -/
private theorem goodSide_perm {α : Type*} [DecidableEq α] (σ : Equiv.Perm (Fin 7))
    {r : Fin 7 → α} {L : Finset α} {M : Finset (Fin 7)} (h : GoodSide (r ∘ σ) L M) :
    GoodSide r L (M.map σ.toEmbedding) := by
  obtain ⟨h1, h2⟩ := h
  have hmem : ∀ i, i ∈ M → σ i ∈ M.map σ.toEmbedding := fun i hi => mem_map_of_mem _ hi
  refine ⟨fun a ha b hb hua hub =>
    h1 a ha b hb (fun i hi => hua _ (hmem i hi)) (fun i hi => hub _ (hmem i hi)), ?_⟩
  intro a ha hua K haK hK hrig
  refine h2 a ha (fun i hi => hua _ (hmem i hi)) K haK (fun v hv => ?_) ?_
  · obtain ⟨i, hi, rfl⟩ := hK v hv
    obtain ⟨i', hi', rfl⟩ := mem_map.1 hi
    exact ⟨i', hi', rfl⟩
  · obtain ⟨hr1, hr2, hr3⟩ := hrig
    refine ⟨fun v hv hvL => ?_, fun j hj => ?_, ?_⟩
    · exact (card_filter_perm σ (fun j => r j = v)).trans (hr1 v hv hvL)
    · obtain ⟨j', hj', hjj⟩ := mem_map.1 (hr2 (σ j) hj)
      have hjj' : j' = j := σ.injective (by simpa using hjj)
      rwa [hjj'] at hj'
    · rw [show #{j | (r ∘ σ) j ∈ K} = #{j | r j ∈ K} from
        card_filter_perm σ (fun j => r j ∈ K)]
      exact hr3

/-- The sort key of an edge: ends with more cut edges first, then by least edge. -/
private def key {α : Type*} [DecidableEq α] (r : Fin 7 → α) (i : Fin 7) : ℕ :=
  8 * (7 - #{j | r j = r i}) + repF r i

/-- Two edges have the same key if and only if they have the same end. -/
private theorem key_eq_iff {α : Type*} [DecidableEq α] (r : Fin 7 → α) (i j : Fin 7) :
    key r i = key r j ↔ r i = r j := by
  constructor
  · intro h
    have hi := (repF r i).isLt
    have hj := (repF r j).isLt
    have hij : (repF r i : ℕ) = repF r j := by
      unfold key at h
      omega
    exact (repF_eq_iff r i j).1 (Fin.ext hij)
  · intro h
    unfold key
    rw [(repF_eq_iff r i j).2 h, h]

/-! ### `refined_cover` from the kernel runs -/

/-- The kernel runs give `checkD` on every side code with digits `dᵢ ≤ i`. -/
private theorem checkD_of_digits (hpre : ∀ d1 < 2, ∀ d2 < 3, checkPre d1 d2 = true)
    {d1 d2 d3 d4 d5 d6 : ℕ} (h1 : d1 < 2) (h2 : d2 < 3) (h3 : d3 < 4) (h4 : d4 < 5)
    (h5 : d5 < 6) (h6 : d6 < 7) : checkD (mkCode d1 d2 d3 d4 d5 d6) = true := by
  have h0 : allBelow 4 (fun d3 => checkPre3 d1 d2 d3) = true := hpre d1 h1 d2 h2
  have h := allBelow_eq_true h0 d3 h3
  rw [checkPre3] at h
  exact allBelow_eq_true (allBelow_eq_true (allBelow_eq_true h d4 h4) d5 h5) d6 h6

/-- The kernel run `checkCanon` puts every canonical code into `canonA`. -/
private theorem mem_canonA_of_digits (hcan : checkCanon = true)
    {d1 d2 d3 d4 d5 d6 : ℕ} (h1 : d1 < 2) (h2 : d2 < 3) (h3 : d3 < 4) (h4 : d4 < 5)
    (h5 : d5 < 6) (h6 : d6 < 7) (hc : canonical (mkCode d1 d2 d3 d4 d5 d6) = true) :
    mkCode d1 d2 d3 d4 d5 d6 ∈ canonA := by
  rw [checkCanon] at hcan
  have h := allBelow_eq_true (allBelow_eq_true (allBelow_eq_true (allBelow_eq_true
    (allBelow_eq_true (allBelow_eq_true hcan d1 h1) d2 h2) d3 h3) d4 h4) d5 h5) d6 h6
  rw [hc] at h
  simp only [Bool.not_true, Bool.false_or, List.any_eq_true, beq_eq, decide_eq_true_eq] at h
  obtain ⟨a, ha, rfl⟩ := h
  exact ha

/-- The digits of `codeOf r` obey the bounds of the enumeration. -/
private theorem repF_digits {γ : Type*} [DecidableEq γ] (r : Fin 7 → γ) :
    (repF r 1 : ℕ) < 2 ∧ (repF r 2 : ℕ) < 3 ∧ (repF r 3 : ℕ) < 4 ∧ (repF r 4 : ℕ) < 5 ∧
      (repF r 5 : ℕ) < 6 ∧ (repF r 6 : ℕ) < 7 := by
  have h : ∀ i : Fin 7, (repF r i : ℕ) ≤ i := fun i => Fin.le_def.1 (repF_le r i)
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  have h5 := h 5
  have h6 := h 6
  simp only [Fin.isValue, Fin.val_one, Fin.val_two] at h1 h2 h3 h4 h5 h6
  exact ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩

/-- `refined_cover` when the edges are sorted by a key `κ` whose level sets are the ends of the
`A` side and along which the number of cut edges at the `A` end does not increase. -/
private theorem refined_cover_sorted {α β : Type*} [DecidableEq α] [DecidableEq β]
    (hpre : ∀ d1 < 2, ∀ d2 < 3, checkPre d1 d2 = true) (hcan : checkCanon = true)
    (ra : Fin 7 → α) (rd : Fin 7 → β) (hsimple : ∀ i j, ra i = ra j → rd i = rd j → i = j)
    (hca : ∀ i, #{j | ra j = ra i} ≤ 3) (hcd : ∀ i, #{j | rd j = rd i} ≤ 3)
    (LA : Finset α) (LD : Finset β) (hLA : ∀ v ∈ LA, ∃ i, ra i = v)
    (hLD : ∀ v ∈ LD, ∃ i, rd i = v) (hLA3 : ∀ i, #{j | ra j = ra i} = 3 → ra i ∈ LA)
    (hLD3 : ∀ i, #{j | rd j = rd i} = 3 → rd i ∈ LD)
    (hbA : ∑ v ∈ LA, (3 - #{j | ra j = v}) ≤ 5) (hbD : ∑ v ∈ LD, (3 - #{j | rd j = v}) ≤ 5)
    {κ : Fin 7 → ℕ} (hmono : Monotone κ) (hκ : ∀ i j, κ i = κ j ↔ ra i = ra j)
    (hsz : ∀ i j, κ i ≤ κ j → #{l | ra l = ra j} ≤ #{l | ra l = ra i}) :
    ∃ M : Finset (Fin 7), #M = 4 ∧ GoodSide ra LA M ∧ GoodSide rd LD M := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := repF_digits ra
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := repF_digits rd
  have hcanA : codeOf ra ∈ canonA :=
    mem_canonA_of_digits hcan a1 a2 a3 a4 a5 a6 (canonical_codeOf hca hmono hκ hsz)
  have hD : checkD (codeOf rd) = true := checkD_of_digits hpre b1 b2 b3 b4 b5 b6
  rw [checkD, validSide_codeOf hcd, Bool.not_true, Bool.false_or, List.all_eq_true] at hD
  have hp := hD _ hcanA
  rw [compat_codeOf hsimple, Bool.not_true, Bool.false_or] at hp
  obtain ⟨k, hka, hkd⟩ := exists_of_pairOK hp
    (mem_masksAux (admissible_lmask hLA hLA3 hbA) 128 (maskOf_lt _ 7))
    (mem_masksAux (admissible_lmask hLD hLD3 hbD) 128 (maskOf_lt _ 7))
  exact ⟨Mset k, card_Mset k (testBit_good hka).1,
    goodSide_of_testBit (codeOf_iff ra) (codeOf_lt ra) (codeOf_idem ra) (mem_iff_lmask ra LA)
      hLA hka,
    goodSide_of_testBit (codeOf_iff rd) (codeOf_lt rd) (codeOf_idem rd) (mem_iff_lmask rd LD)
      hLD hkd⟩

/-- `refined_cover` from the kernel runs: sort the edges by `key` (`Tuple.sort`), apply the
sorted case, and map the four-set back. -/
private theorem refined_cover_of_checks {α β : Type*} [DecidableEq α] [DecidableEq β]
    (hpre : ∀ d1 < 2, ∀ d2 < 3, checkPre d1 d2 = true) (hcan : checkCanon = true)
    (ra : Fin 7 → α) (rd : Fin 7 → β) (hsimple : ∀ i j, ra i = ra j → rd i = rd j → i = j)
    (hca : ∀ i, #{j | ra j = ra i} ≤ 3) (hcd : ∀ i, #{j | rd j = rd i} ≤ 3)
    (LA : Finset α) (LD : Finset β) (hLA : ∀ v ∈ LA, ∃ i, ra i = v)
    (hLD : ∀ v ∈ LD, ∃ i, rd i = v) (hLA3 : ∀ i, #{j | ra j = ra i} = 3 → ra i ∈ LA)
    (hLD3 : ∀ i, #{j | rd j = rd i} = 3 → rd i ∈ LD)
    (hbA : ∑ v ∈ LA, (3 - #{j | ra j = v}) ≤ 5) (hbD : ∑ v ∈ LD, (3 - #{j | rd j = v}) ≤ 5) :
    ∃ M : Finset (Fin 7), #M = 4 ∧ GoodSide ra LA M ∧ GoodSide rd LD M := by
  set σ := Tuple.sort (key ra)
  have hA : ∀ (v : α), #{j | (ra ∘ σ) j = v} = #{j | ra j = v} := fun v =>
    card_filter_perm σ (fun j => ra j = v)
  have hDc : ∀ (v : β), #{j | (rd ∘ σ) j = v} = #{j | rd j = v} := fun v =>
    card_filter_perm σ (fun j => rd j = v)
  have hcard : ∀ i, #{j | ra j = ra i} ≤ 7 := fun i => by
    simpa using card_le_univ ({j | ra j = ra i} : Finset (Fin 7))
  obtain ⟨M, hM, hgA, hgD⟩ := refined_cover_sorted hpre hcan (ra ∘ σ) (rd ∘ σ)
    (fun i j h1 h2 => σ.injective (hsimple _ _ h1 h2))
    (fun i => (hA _).trans_le (hca (σ i))) (fun i => (hDc _).trans_le (hcd (σ i))) LA LD
    (fun v hv => by
      obtain ⟨i, rfl⟩ := hLA v hv
      exact ⟨σ.symm i, by simp⟩)
    (fun v hv => by
      obtain ⟨i, rfl⟩ := hLD v hv
      exact ⟨σ.symm i, by simp⟩)
    (fun i h => hLA3 (σ i) ((hA _).symm.trans h)) (fun i h => hLD3 (σ i) ((hDc _).symm.trans h))
    (by simpa only [hA] using hbA) (by simpa only [hDc] using hbD)
    (κ := key ra ∘ σ) (Tuple.monotone_sort _) (fun i j => key_eq_iff ra (σ i) (σ j))
    (fun i j hij => by
      rw [hA, hA]
      have hi := (repF ra (σ i)).isLt
      have hj := (repF ra (σ j)).isLt
      have hci := hcard (σ i)
      have hcj := hcard (σ j)
      simp only [Function.comp_apply, key] at hij ⊢
      omega)
  exact ⟨M.map σ.toEmbedding, by rw [card_map]; exact hM, goodSide_perm σ hgA,
    goodSide_perm σ hgD⟩

/-- The kernel runs of `CoverCheck1.lean` to `CoverCheck3.lean` give `checkPre d1 d2` for every
`d1 < 2` and `d2 < 3`, the hypothesis of `checkD_of_digits`. -/
private theorem checkPre_all : ∀ d1 < 2, ∀ d2 < 3, checkPre d1 d2 = true := by
  intro d1 h1 d2 h2
  interval_cases d1 <;> interval_cases d2
  · exact checkPre_0_0
  · exact checkPre_0_1
  · exact checkPre_0_2
  · exact checkPre_1_0
  · exact checkPre_1_1
  · refine allBelow_of_forall fun d3 h3 => ?_
    interval_cases d3
    · exact checkPre3_1_2_0
    · exact checkPre3_1_2_1
    · exact checkPre3_1_2_2
    · exact checkPre3_1_2_3

end CoverCheck

open CoverCheck in
/-- **The covering lemma**, for a cut of 7 edges `Fin 7` with ends `ra i` on the `A` side and
`rd i` on the `D` side: simple (`(ra, rd)` injective), every end in at most 3 edges, `L` sets of
ends (so `c ≥ 1` on `L`, where `c` is the number of edges at an end), containing every end with
`c = 3`, with `Σ_L (3 - c) ≤ 5`. Then some four-set `M` of edges satisfies `GoodSide` on both
sides. The finite check runs in the kernel (`CoverCheck1.lean` to `CoverCheck3.lean`). -/
theorem refined_cover {α β : Type*} [DecidableEq α] [DecidableEq β] (ra : Fin 7 → α)
    (rd : Fin 7 → β) (hsimple : ∀ i j, ra i = ra j → rd i = rd j → i = j)
    (hca : ∀ i, #{j | ra j = ra i} ≤ 3) (hcd : ∀ i, #{j | rd j = rd i} ≤ 3)
    (LA : Finset α) (LD : Finset β) (hLA : ∀ v ∈ LA, ∃ i, ra i = v)
    (hLD : ∀ v ∈ LD, ∃ i, rd i = v) (hLA3 : ∀ i, #{j | ra j = ra i} = 3 → ra i ∈ LA)
    (hLD3 : ∀ i, #{j | rd j = rd i} = 3 → rd i ∈ LD)
    (hbA : ∑ v ∈ LA, (3 - #{j | ra j = v}) ≤ 5) (hbD : ∑ v ∈ LD, (3 - #{j | rd j = v}) ≤ 5) :
    ∃ M : Finset (Fin 7), #M = 4 ∧ GoodSide ra LA M ∧ GoodSide rd LD M :=
  refined_cover_of_checks checkPre_all checkCanon_eq ra rd hsimple hca hcd LA LD hLA hLD hLA3
    hLD3 hbA hbD

end Erdos585.QB5
