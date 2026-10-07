import Mathlib.FieldTheory.ChevalleyWarning
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Mixed-modulus selection in a bounded bipartite incidence graph

This is the polynomial selection step of the twin-quotient forcing argument.
It selects actual incidence edges with left degrees zero or four and right
degrees zero or two. The separate cycle-lifting argument is not assumed here.
-/

namespace Erdos585.TwinZeroSum

noncomputable section

open Finset MvPolynomial

private def linearPoly {E : Type*} (s : Finset E) : MvPolynomial E (ZMod 2) :=
  ∑ e ∈ s, X e

private def quadraticPoly {E : Type*} (s : Finset E) : MvPolynomial E (ZMod 2) :=
  ∑ t ∈ s.powersetCard 2, ∏ e ∈ t, X e

private lemma degree_linearPoly {E : Type*} (s : Finset E) :
    (linearPoly s).totalDegree ≤ 1 := by
  apply totalDegree_finsetSum_le
  intro e he
  simp

private lemma degree_quadraticPoly {E : Type*} (s : Finset E) :
    (quadraticPoly s).totalDegree ≤ 2 := by
  apply totalDegree_finsetSum_le
  intro t ht
  calc
    (∏ e ∈ t, (X e : MvPolynomial E (ZMod 2))).totalDegree ≤
        ∑ e ∈ t, (X e : MvPolynomial E (ZMod 2)).totalDegree :=
      totalDegree_finsetProd t _
    _ = t.card := by simp
    _ = 2 := (mem_powersetCard.mp ht).2

private lemma zmod_two_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  have hx : x.val < 2 := ZMod.val_lt x
  have hcases : x.val = 0 ∨ x.val = 1 := by omega
  rcases hcases with h | h
  · exact Or.inl ((ZMod.val_eq_zero x).mp h)
  · right
    apply ZMod.val_injective 2
    calc
      x.val = 1 := h
      _ = (1 : ZMod 2).val := by rw [ZMod.val_one_eq_one_mod]

private lemma eval_linearPoly {E : Type*} [DecidableEq E]
    (s : Finset E) (x : E → ZMod 2) :
    eval x (linearPoly s) = ((s.filter (fun e => x e = 1)).card : ZMod 2) := by
  classical
  simp only [linearPoly, map_sum, eval_X]
  rw [← sum_filter_ne_zero]
  have hfilter : s.filter (fun e => x e ≠ 0) = s.filter (fun e => x e = 1) := by
    ext e
    rcases zmod_two_eq_zero_or_one (x e) with h | h <;> simp [h]
  rw [hfilter]
  calc
    ∑ e ∈ s.filter (fun e => x e = 1), x e =
        ∑ _e ∈ s.filter (fun e => x e = 1), (1 : ZMod 2) :=
      sum_congr rfl (fun e he => (mem_filter.mp he).2)
    _ = _ := by simp

private lemma eval_quadraticPoly {E : Type*} [DecidableEq E]
    (s : Finset E) (x : E → ZMod 2) :
    eval x (quadraticPoly s) =
      (Nat.choose (s.filter (fun e => x e = 1)).card 2 : ZMod 2) := by
  classical
  simp only [quadraticPoly, map_sum, map_prod, eval_X]
  have hprod (t : Finset E) :
      (∏ e ∈ t, x e) = if ∀ e ∈ t, x e = 1 then 1 else 0 := by
    split_ifs with ht
    · exact prod_eq_one ht
    · push Not at ht
      obtain ⟨e, he, hx⟩ := ht
      apply prod_eq_zero he
      exact (zmod_two_eq_zero_or_one (x e)).resolve_right hx
  simp_rw [hprod]
  rw [← sum_filter]
  have hfilter : (s.powersetCard 2).filter (fun t => ∀ e ∈ t, x e = 1) =
      (s.filter (fun e => x e = 1)).powersetCard 2 := by
    ext t
    simp only [mem_filter, mem_powersetCard]
    constructor
    · rintro ⟨⟨hts, htcard⟩, ht⟩
      exact ⟨fun e he => mem_filter.mpr ⟨hts he, ht e he⟩, htcard⟩
    · rintro ⟨ht, htcard⟩
      exact ⟨⟨fun e he => (mem_filter.mp (ht he)).1, htcard⟩,
        fun e he => (mem_filter.mp (ht he)).2⟩
  rw [hfilter]
  simp

private lemma left_degree_of_equations (k : ℕ) (hk : k ≤ 6)
    (hlinear : (k : ZMod 2) = 0) (hquadratic : (Nat.choose k 2 : ZMod 2) = 0) :
    k = 0 ∨ k = 4 := by
  rw [ZMod.natCast_eq_zero_iff] at hlinear hquadratic
  interval_cases k <;> norm_num [Nat.choose] at *

private lemma right_degree_of_equation (k : ℕ) (hk : k ≤ 3)
    (hlinear : (k : ZMod 2) = 0) : k = 0 ∨ k = 2 := by
  rw [ZMod.natCast_eq_zero_iff] at hlinear
  interval_cases k <;> norm_num at *

private lemma sum_eval_linear_fibers {E V : Type*} [Fintype E] [Fintype V]
    [DecidableEq E] [DecidableEq V] (a : E → V) (x : E → ZMod 2) :
    (∑ v, eval x (linearPoly (univ.filter (fun e => a e = v)))) = ∑ e, x e := by
  simp only [linearPoly, map_sum, eval_X]
  exact sum_fiberwise_of_maps_to (fun _ _ => mem_univ _) x

private lemma exists_nonzero_solution {E I R : Type*}
    [Fintype E] [Fintype I] [Fintype R]
    [DecidableEq E] [DecidableEq I] [DecidableEq R] [Nonempty R]
    (left : E → I) (right : E → R)
    (hsize : 3 * Fintype.card I + Fintype.card R ≤ Fintype.card E) :
    ∃ x : E → ZMod 2, x ≠ 0 ∧
      (∀ i, eval x (linearPoly (univ.filter (fun e => left e = i))) = 0) ∧
      (∀ i, eval x (quadraticPoly (univ.filter (fun e => left e = i))) = 0) ∧
      (∀ r, eval x (linearPoly (univ.filter (fun e => right e = r))) = 0) := by
  classical
  let r₀ : R := Classical.choice inferInstance
  let T := {r : R // r ≠ r₀}
  let f : ((I ⊕ I) ⊕ T) → MvPolynomial E (ZMod 2) := fun a =>
    match a with
    | .inl (.inl i) => linearPoly (univ.filter (fun e => left e = i))
    | .inl (.inr i) => quadraticPoly (univ.filter (fun e => left e = i))
    | .inr r => linearPoly (univ.filter (fun e => right e = r.val))
  have hlin : (∑ i : I,
      (linearPoly (univ.filter (fun e => left e = i))).totalDegree) ≤ Fintype.card I := by
    calc
      _ ≤ ∑ _i : I, 1 := sum_le_sum (fun i _ => degree_linearPoly _)
      _ = _ := by simp
  have hquad : (∑ i : I,
      (quadraticPoly (univ.filter (fun e => left e = i))).totalDegree) ≤
        2 * Fintype.card I := by
    calc
      _ ≤ ∑ _i : I, 2 := sum_le_sum (fun i _ => degree_quadraticPoly _)
      _ = _ := by simp [Nat.mul_comm]
  have hright : (∑ r : T,
      (linearPoly (univ.filter (fun e => right e = r.val))).totalDegree) ≤ Fintype.card T := by
    calc
      _ ≤ ∑ _r : T, 1 := sum_le_sum (fun r _ => degree_linearPoly _)
      _ = _ := by simp
  have hT : Fintype.card T = Fintype.card R - 1 := by
    simpa [T] using Fintype.card_subtype_compl (fun r : R => r = r₀)
  have hRpos : 0 < Fintype.card R := Fintype.card_pos
  have hdeg : (∑ a, (f a).totalDegree) < Fintype.card E := by
    simp only [Fintype.sum_sum_type, f]
    omega
  have hdvd := char_dvd_card_solutions_of_fintype_sum_lt
    (K := ZMod 2) 2 hdeg
  have hzero : ∀ a, eval (0 : E → ZMod 2) (f a) = 0 := by
    rintro ((i | i) | r)
    · change eval _ (linearPoly _) = 0
      rw [eval_linearPoly]
      simp
    · change eval _ (quadraticPoly _) = 0
      rw [eval_quadraticPoly]
      simp
    · change eval _ (linearPoly _) = 0
      rw [eval_linearPoly]
      simp
  obtain ⟨x, hfx, hx⟩ : ∃ x : E → ZMod 2, (∀ a, eval x (f a) = 0) ∧ x ≠ 0 := by
    by_contra! hnone
    have hcard : Fintype.card {x : E → ZMod 2 // ∀ a, eval x (f a) = 0} = 1 := by
      apply Fintype.card_eq_one_iff.mpr
      refine ⟨⟨0, hzero⟩, ?_⟩
      intro z
      apply Subtype.ext
      exact hnone z.val z.property
    rw [hcard] at hdvd
    norm_num at hdvd
  have hleft : ∀ i, eval x (linearPoly (univ.filter (fun e => left e = i))) = 0 :=
    fun i => hfx (.inl (.inl i))
  have hquadratic : ∀ i,
      eval x (quadraticPoly (univ.filter (fun e => left e = i))) = 0 :=
    fun i => hfx (.inl (.inr i))
  have hright' : ∀ r : R, r ≠ r₀ →
      eval x (linearPoly (univ.filter (fun e => right e = r))) = 0 :=
    fun r hr => hfx (.inr ⟨r, hr⟩)
  have htotal : ∑ e, x e = 0 := by
    rw [← sum_eval_linear_fibers left x]
    exact sum_eq_zero (fun i _ => hleft i)
  have hrightsum : (∑ r, eval x (linearPoly (univ.filter (fun e => right e = r)))) = 0 := by
    rw [sum_eval_linear_fibers, htotal]
  have h₀ : eval x (linearPoly (univ.filter (fun e => right e = r₀))) = 0 := by
    rw [sum_eq_single r₀] at hrightsum
    · exact hrightsum
    · intro r _ hr
      exact hright' r hr
    · simp
  refine ⟨x, hx, hleft, hquadratic, ?_⟩
  intro r
  by_cases hr : r = r₀
  · simpa [hr] using h₀
  · exact hright' r hr

private lemma selection_fiber {E V : Type*} [Fintype E]
    [DecidableEq E] [DecidableEq V] (x : E → ZMod 2) (a : E → V) (v : V) :
    (univ.filter (fun e => x e = 1)).filter (fun e => a e = v) =
      (univ.filter (fun e => a e = v)).filter (fun e => x e = 1) := by
  classical
  ext e
  simp [and_comm]

private lemma exists_selected_subtype {E I R : Type*}
    [Fintype E] [Fintype I] [Fintype R]
    [DecidableEq E] [DecidableEq I] [DecidableEq R] [Nonempty R]
    (left : E → I) (right : E → R)
    (hleft : ∀ i, (univ.filter (fun e => left e = i)).card ≤ 6)
    (hright : ∀ r, (univ.filter (fun e => right e = r)).card ≤ 3)
    (hsize : 3 * Fintype.card I + Fintype.card R ≤ Fintype.card E) :
    ∃ S : Finset E, S.Nonempty ∧
      (∀ i, (S.filter (fun e => left e = i)).card = 0 ∨
        (S.filter (fun e => left e = i)).card = 4) ∧
      (∀ r, (S.filter (fun e => right e = r)).card = 0 ∨
        (S.filter (fun e => right e = r)).card = 2) := by
  classical
  obtain ⟨x, hx, hlin, hquad, hr⟩ := exists_nonzero_solution left right hsize
  let S : Finset E := univ.filter (fun e => x e = 1)
  have hS : S.Nonempty := by
    obtain ⟨e, he⟩ : ∃ e, x e = 1 := by
      by_contra! h
      apply hx
      funext e
      exact (zmod_two_eq_zero_or_one (x e)).resolve_right (h e)
    exact ⟨e, mem_filter.mpr ⟨mem_univ _, he⟩⟩
  refine ⟨S, hS, ?_, ?_⟩
  · intro i
    change ((univ.filter (fun e => x e = 1)).filter (fun e => left e = i)).card = 0 ∨ _
    rw [selection_fiber x left i]
    apply left_degree_of_equations
    · exact (card_le_card (filter_subset _ _)).trans (hleft i)
    · rw [← eval_linearPoly]
      exact hlin i
    · rw [← eval_quadraticPoly]
      exact hquad i
  · intro r
    change ((univ.filter (fun e => x e = 1)).filter (fun e => right e = r)).card = 0 ∨ _
    rw [selection_fiber x right r]
    apply right_degree_of_equation
    · exact (card_le_card (filter_subset _ _)).trans (hright r)
    · rw [← eval_linearPoly]
      exact hr r

private lemma subtype_filter_card {A : Type*} [DecidableEq A]
    (J : Finset A) (p : A → Prop) [DecidablePred p] :
    ((univ : Finset {a // a ∈ J}).filter (fun a => p a.val)).card = (J.filter p).card := by
  classical
  have himage :
      (((univ : Finset {a // a ∈ J}).filter (fun a => p a.val)).image Subtype.val) =
        J.filter p := by
    ext a
    constructor
    · intro ha
      obtain ⟨b, hb, rfl⟩ := mem_image.mp ha
      exact mem_filter.mpr ⟨b.property, (mem_filter.mp hb).2⟩
    · intro ha
      obtain ⟨haJ, hp⟩ := mem_filter.mp ha
      exact mem_image.mpr ⟨⟨a, haJ⟩, mem_filter.mpr ⟨mem_univ _, hp⟩, rfl⟩
  calc
    _ = ((((univ : Finset {a // a ∈ J}).filter (fun a => p a.val)).image
        Subtype.val)).card := (card_image_of_injective _ Subtype.val_injective).symm
    _ = _ := congrArg Finset.card himage

/-- An actual bounded bipartite incidence graph above the mixed-modulus
threshold has a nonempty actual edge subset of left degrees zero or four and
right degrees zero or two. No auxiliary solution or cycle assumption is used. -/
theorem exists_nonempty_selected_incidence {I R : Type*}
    [Fintype I] [Fintype R] [DecidableEq I] [DecidableEq R] [Nonempty R]
    (J : Finset (I × R))
    (hleft : ∀ i, (J.filter (fun e => e.1 = i)).card ≤ 6)
    (hright : ∀ r, (J.filter (fun e => e.2 = r)).card ≤ 3)
    (hsize : 3 * Fintype.card I + Fintype.card R ≤ J.card) :
    ∃ K : Finset (I × R), K ⊆ J ∧ K.Nonempty ∧
      (∀ i, (K.filter (fun e => e.1 = i)).card = 0 ∨
        (K.filter (fun e => e.1 = i)).card = 4) ∧
      (∀ r, (K.filter (fun e => e.2 = r)).card = 0 ∨
        (K.filter (fun e => e.2 = r)).card = 2) := by
  classical
  let E := {e // e ∈ J}
  let left : E → I := fun e => e.val.1
  let right : E → R := fun e => e.val.2
  have hleft' : ∀ i, (univ.filter (fun e => left e = i)).card ≤ 6 := by
    intro i
    change ((univ : Finset {e // e ∈ J}).filter (fun e => e.val.1 = i)).card ≤ 6
    rw [subtype_filter_card J (fun e : I × R => e.1 = i)]
    exact hleft i
  have hright' : ∀ r, (univ.filter (fun e => right e = r)).card ≤ 3 := by
    intro r
    change ((univ : Finset {e // e ∈ J}).filter (fun e => e.val.2 = r)).card ≤ 3
    rw [subtype_filter_card J (fun e : I × R => e.2 = r)]
    exact hright r
  have hsize' : 3 * Fintype.card I + Fintype.card R ≤ Fintype.card E := by
    simpa [E] using hsize
  obtain ⟨S, hS, hSL, hSR⟩ := exists_selected_subtype left right hleft' hright' hsize'
  let K : Finset (I × R) := S.image Subtype.val
  have hKL (i : I) : (K.filter (fun e => e.1 = i)).card =
      (S.filter (fun e => left e = i)).card := by
    change ((S.image Subtype.val).filter (fun e => e.1 = i)).card = _
    rw [filter_image]
    exact card_image_of_injective _ Subtype.val_injective
  have hKR (r : R) : (K.filter (fun e => e.2 = r)).card =
      (S.filter (fun e => right e = r)).card := by
    change ((S.image Subtype.val).filter (fun e => e.2 = r)).card = _
    rw [filter_image]
    exact card_image_of_injective _ Subtype.val_injective
  refine ⟨K, ?_, hS.image Subtype.val, ?_, ?_⟩
  · intro e he
    obtain ⟨a, _ha, rfl⟩ := mem_image.mp he
    exact a.property
  · intro i
    simpa only [hKL] using hSL i
  · intro r
    simpa only [hKR] using hSR r

end

end Erdos585.TwinZeroSum
