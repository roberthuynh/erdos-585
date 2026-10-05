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
import Openmath.Proofs.SmallExact

/-!
# Matching subdivisions joined to two universal vertices

Original matching edges are retained; every other base edge receives one subdivision vertex.
The two hubs are adjacent. The proof excludes every nonempty subgraph whose degrees are 0 or 4.
-/

open SimpleGraph Finset

namespace Erdos585
namespace MatchingSubdivision

variable {V B : Type*}

abbrev Vertex (V B : Type*) := V ⊕ (B ⊕ Fin 2)
abbrev original (v : V) : Vertex V B := Sum.inl v
abbrev middle (b : B) : Vertex V B := Sum.inr (Sum.inl b)
abbrev hub (i : Fin 2) : Vertex V B := Sum.inr (Sum.inr i)

/-- Number of neighbors in a specified vertex class. -/
def row [Fintype B] (F : SimpleGraph V) [DecidableRel F.Adj] (v : V) (f : B → V) : ℕ :=
  (univ.filter (fun b => F.Adj v (f b))).card

lemma row_eq_sum [Fintype B] (F : SimpleGraph V) [DecidableRel F.Adj] (v : V) (f : B → V) :
    row F v f = ∑ b, if F.Adj v (f b) then 1 else 0 := by
  simp [row]

lemma row_le [Fintype B] (F : SimpleGraph V) [DecidableRel F.Adj] (v : V) (f : B → V) :
    row F v f ≤ Fintype.card B := card_le_univ _

lemma row_mono [Fintype B] {F G : SimpleGraph V} [DecidableRel F.Adj]
    [DecidableRel G.Adj] (h : F ≤ G) (v : V) (f : B → V) : row F v f ≤ row G v f :=
  card_le_card (by intro b hb; exact mem_filter.mpr ⟨mem_univ _, h (mem_filter.mp hb).2⟩)

lemma row_zero_of_degree_zero [Fintype V] [Fintype B] (F : SimpleGraph V)
    [DecidableRel F.Adj] (v : V) (f : B → V) (h : F.degree v = 0) : row F v f = 0 := by
  have hn : ∀ w, ¬ F.Adj v w := by
    intro w hw
    have := (F.degree_pos_iff_exists_adj v).2 ⟨w, hw⟩
    omega
  simp only [row, hn, filter_false, card_empty]

lemma degree_parts [Fintype V] [Fintype B] (F : SimpleGraph (Vertex V B))
    [DecidableRel F.Adj] (v : Vertex V B) :
    F.degree v = row F v original + row F v middle + row F v hub := by
  have he : F.degree v = ∑ w, if F.Adj v w then 1 else 0 := by
    rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter, sum_boole]
    rfl
  rw [he, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [row_eq_sum, original, middle, hub]
  omega

lemma cross_symm {A C : Type*} [Fintype A] [Fintype C]
    (F : SimpleGraph V) [DecidableRel F.Adj] (f : A → V) (g : C → V) :
    ∑ a, row F (f a) g = ∑ c, row F (g c) f := by
  simp only [row_eq_sum]
  rw [sum_comm]
  simp only [F.adj_comm]

variable [DecidableEq V]

/-- The two-hub join of a matching and distinct subdivided edges. -/
def graph (M : SimpleGraph V) (R : Finset (Sym2 V)) : SimpleGraph (Vertex V R) where
  Adj x y := match x, y with
    | .inl a, .inl b => M.Adj a b
    | .inl a, .inr (.inl e) => a ∈ e.val
    | .inr (.inl e), .inl a => a ∈ e.val
    | .inr (.inl _), .inr (.inl _) => False
    | .inr (.inr i), .inr (.inr j) => i ≠ j
    | _, _ => True
  symm := ⟨by rintro (a | (e | i)) (b | (f | j)) <;> simp_all [M.adj_comm, ne_comm]⟩
  loopless := ⟨by rintro (a | (e | i)) <;> simp⟩

instance (M : SimpleGraph V) [DecidableRel M.Adj] (R : Finset (Sym2 V)) :
    DecidableRel (graph M R).Adj := fun x y => by
  cases x with
  | inl a => cases y with
    | inl b => exact inferInstanceAs (Decidable (M.Adj a b))
    | inr y => cases y <;> unfold graph <;> dsimp <;> infer_instance
  | inr x => cases x <;> cases y with
    | inl b => unfold graph; dsimp; infer_instance
    | inr y => cases y <;> unfold graph <;> dsimp <;> infer_instance

variable [Fintype V] (M : SimpleGraph V) [DecidableRel M.Adj] (R : Finset (Sym2 V))

lemma row_original_original (v : V) : row (graph M R) (original v) original = M.degree v := by
  rw [← M.card_neighborFinset_eq_degree, neighborFinset_eq_filter]
  rfl

lemma row_middle_original (e : R) : row (graph M R) (middle e) original = e.val.toFinset.card := by
  change (univ.filter (fun v => v ∈ e.val)).card = e.val.toFinset.card
  congr 1
  ext v
  simp only [mem_filter, mem_univ, true_and, Sym2.mem_toFinset]

omit [Fintype V] in
lemma row_middle_middle (e : R) : row (graph M R) (middle e) middle = 0 := by
  change (univ.filter (fun _ : R => False)).card = 0
  simp only [filter_false, card_empty]

omit [Fintype V] in
lemma row_middle_hub (e : R) : row (graph M R) (middle e) hub = 2 := by
  change (univ.filter (fun _ : Fin 2 => True)).card = 2
  simp only [filter_true, card_univ, Fintype.card_fin]

lemma degree_middle (hR : ∀ e ∈ R, ¬ e.IsDiag) (e : R) :
    (graph M R).degree (middle e) = 4 := by
  rw [degree_parts, row_middle_original, row_middle_middle, row_middle_hub,
    Sym2.card_toFinset_of_not_isDiag _ (hR e e.property)]

/-- At a subdivision vertex, selecting all four neighbors is forced. -/
lemma middle_full {F : SimpleGraph (Vertex V R)} [DecidableRel F.Adj]
    (hFG : F ≤ graph M R) (hR : ∀ e ∈ R, ¬ e.IsDiag) (e : R)
    (he : F.degree (middle e) = 4) :
    F.neighborFinset (middle e) = (graph M R).neighborFinset (middle e) := by
  apply eq_of_subset_of_card_le
  · intro w hw
    exact (mem_neighborFinset _ _ _).2 (hFG ((mem_neighborFinset _ _ _).1 hw))
  · rw [card_neighborFinset_eq_degree, card_neighborFinset_eq_degree, he,
      degree_middle M R hR]

lemma middle_balance {F : SimpleGraph (Vertex V R)} [DecidableRel F.Adj]
    (hFG : F ≤ graph M R) (hR : ∀ e ∈ R, ¬ e.IsDiag)
    (hreg : ∀ v, F.degree v = 0 ∨ F.degree v = 4) (e : R) :
    row F (middle e) original = row F (middle e) hub := by
  rcases hreg (middle e) with he | he
  · rw [row_zero_of_degree_zero F _ _ he, row_zero_of_degree_zero F _ _ he]
  · have hf := middle_full M R hFG hR e he
    have ha : ∀ w, F.Adj (middle e) w ↔ (graph M R).Adj (middle e) w := by
      intro w
      simpa only [mem_neighborFinset] using Iff.of_eq (congrArg (w ∈ ·) hf)
    simp only [row, ha]
    change row (graph M R) (middle e) original = row (graph M R) (middle e) hub
    rw [row_middle_original, row_middle_hub,
      Sym2.card_toFinset_of_not_isDiag _ (hR e e.property)]

/-- The two hubs have eight available incidences, allowing at most two original vertices. -/
lemma active_originals_le_two {F : SimpleGraph (Vertex V R)} [DecidableRel F.Adj]
    (hFG : F ≤ graph M R) (hR : ∀ e ∈ R, ¬ e.IsDiag)
    (hM : ∀ v, M.degree v ≤ 1)
    (hreg : ∀ v, F.degree v = 0 ∨ F.degree v = 4) :
    (univ.filter (fun a : V => F.degree (original a) = 4)).card ≤ 2 := by
  let A := univ.filter (fun a : V => F.degree (original a) = 4)
  have hs : ∑ a : V, F.degree (original a) = 4 * A.card := by
    calc
      _ = ∑ a : V, if F.degree (original a) = 4 then 4 else 0 := by
        apply sum_congr rfl
        intro a _
        rcases hreg (original a) with h | h <;> simp only [h] <;> decide
      _ = 4 * A.card := by
        rw [← sum_filter, sum_const, smul_eq_mul]
        exact Nat.mul_comm _ _
  have haa : ∑ a : V, row F (original a) original ≤ A.card := by
    calc
      _ ≤ ∑ a : V, if F.degree (original a) = 4 then 1 else 0 := by
        apply sum_le_sum
        intro a _
        rcases hreg (original a) with h | h
        · rw [row_zero_of_degree_zero F _ _ h, h]; decide
        · rw [h, if_pos rfl]
          exact (row_mono hFG _ _).trans ((row_original_original M R a).le.trans (hM a))
      _ = A.card := by rw [sum_boole]; rfl
  have hab : ∑ a : V, row F (original a) middle = ∑ i : Fin 2, row F (hub i) middle := by
    rw [cross_symm F original middle, cross_symm F hub middle]
    exact sum_congr rfl (fun e _ => middle_balance M R hFG hR hreg e)
  have hah := cross_symm F (original : V → Vertex V R) hub
  have hh : ∑ i : Fin 2, F.degree (hub i) ≤ 8 := by
    calc
      _ ≤ ∑ _ : Fin 2, 4 := sum_le_sum (fun i _ => (hreg (hub i)).elim (by omega) (by omega))
      _ = 8 := by decide
  have hda : ∑ a : V, F.degree (original a) =
      (∑ a : V, row F (original a) original) +
      (∑ a : V, row F (original a) middle) + ∑ a : V, row F (original a) hub := by
    simp only [degree_parts, sum_add_distrib]
  have hdh : ∑ i : Fin 2, F.degree (hub i) =
      (∑ i : Fin 2, row F (hub i) original) +
      (∑ i : Fin 2, row F (hub i) middle) + ∑ i : Fin 2, row F (hub i) hub := by
    simp only [degree_parts, sum_add_distrib]
  change A.card ≤ 2
  omega

/-- The construction has no nonempty subgraph with all degrees zero or four. -/
theorem no_four_regular {F : SimpleGraph (Vertex V R)} [DecidableRel F.Adj]
    (hFG : F ≤ graph M R) (hR : ∀ e ∈ R, ¬ e.IsDiag)
    (hM : ∀ v, M.degree v ≤ 1) (hdis : ∀ e ∈ R, e ∉ M.edgeSet)
    (hreg : ∀ v, F.degree v = 0 ∨ F.degree v = 4) : F = ⊥ := by
  classical
  let A := univ.filter (fun a : V => F.degree (original a) = 4)
  have hAc : A.card ≤ 2 := active_originals_le_two M R hFG hR hM hreg
  have four {x y : Vertex V R} (hxy : F.Adj x y) : F.degree x = 4 := by
    rcases hreg x with h | h
    · have := (F.degree_pos_iff_exists_adj x).2 ⟨y, hxy⟩
      omega
    · exact h
  have ends : ∀ e : R, F.degree (middle e) = 4 → e.val.toFinset = A := by
    intro e he
    have hf := middle_full M R hFG hR e he
    apply eq_of_subset_of_card_le
    · intro a ha
      have hga : (graph M R).Adj (middle e) (original a) := (Sym2.mem_toFinset.mp ha)
      have hfa : F.Adj (middle e) (original a) := by
        have hm := (mem_neighborFinset _ _ _).2 hga
        rw [← hf] at hm
        exact (mem_neighborFinset _ _ _).1 hm
      exact mem_filter.mpr ⟨mem_univ _, four hfa.symm⟩
    · rw [Sym2.card_toFinset_of_not_isDiag _ (hR e e.property)]
      exact hAc
  have no_mid : ∀ e : R, F.degree (middle e) = 0 := by
    intro e
    rcases hreg (middle e) with he | he
    · exact he
    exfalso
    have hAe := ends e he
    obtain ⟨a, b, habrep⟩ : ∃ a b, e.val = s(a,b) := by
      induction e.val using Sym2.inductionOn with | _ a b => exact ⟨a,b,rfl⟩
    have hab : a ≠ b := by simpa [habrep] using hR e e.property
    have hA : A = {a,b} := by rw [← hAe, habrep, Sym2.toFinset_mk_eq]
    have ha : F.degree (original a) = 4 := by
      have hm : a ∈ A := by rw [hA]; simp
      exact (mem_filter.mp hm).2
    have hn : F.neighborFinset (original a) ⊆ {middle e, hub 0, hub 1} := by
      intro x hx
      have hax : F.Adj (original a) x := (mem_neighborFinset _ _ _).1 hx
      rcases x with c | (f | i)
      · have hc : c ∈ A := mem_filter.mpr ⟨mem_univ _, four hax.symm⟩
        rw [hA, mem_insert, mem_singleton] at hc
        rcases hc with hc | hc
        · subst c
          exact (F.ne_of_adj hax rfl).elim
        · subst c
          have hm : M.Adj a b := hFG hax
          exact (hdis e e.property (by simpa [habrep] using hm)).elim
      · have hf := ends f (four hax.symm)
        have hfe : f = e := by
          apply Subtype.ext
          apply Sym2.eq_of_ne_mem hab
          · apply Sym2.mem_toFinset.mp
            rw [hf, hA]; simp
          · apply Sym2.mem_toFinset.mp
            rw [hf, hA]; simp
          · simp [habrep]
          · simp [habrep]
        subst f
        simp
      · fin_cases i <;> simp [hub]
    have hc := card_le_card hn
    rw [card_neighborFinset_eq_degree, ha] at hc
    have ht := card_le_three (a := middle (V := V) e) (b := hub (V := V) (B := R) 0)
      (c := hub (V := V) (B := R) 1)
    omega
  have no_orig : ∀ a : V, F.degree (original a) = 0 := by
    intro a
    have hm : row F (original a) middle = 0 := by
      apply card_eq_zero.mpr
      apply eq_empty_iff_forall_notMem.mpr
      intro e he
      have he' : F.Adj (original a) (middle e) := (mem_filter.mp he).2
      have := four he'.symm
      have := no_mid e
      omega
    have hsmall := (row_mono hFG (original a) original).trans
      ((row_original_original M R a).le.trans (hM a))
    have hh := row_le F (original a) (hub (V := V) (B := R))
    have hd := degree_parts F (original a)
    have hr := hreg (original a)
    simp only [Fintype.card_fin] at hh
    omega
  ext x y
  simp only [bot_adj, iff_false]
  intro hxy
  rcases x with a | (e | i)
  · have h4 : F.degree (original a) = 4 := four hxy
    rw [no_orig a] at h4
    omega
  · have h4 : F.degree (middle e) = 4 := four hxy
    rw [no_mid e] at h4
    omega
  · have ho : row F (hub i) original = 0 := by
      apply card_eq_zero.mpr
      apply eq_empty_iff_forall_notMem.mpr
      intro a ha
      have := four ((mem_filter.mp ha).2).symm
      have := no_orig a
      omega
    have hm : row F (hub i) middle = 0 := by
      apply card_eq_zero.mpr
      apply eq_empty_iff_forall_notMem.mpr
      intro e he
      have := four ((mem_filter.mp he).2).symm
      have := no_mid e
      omega
    have hh := row_le F (hub i) (hub (V := V) (B := R))
    have hd := degree_parts F (hub i)
    have h4 : F.degree (hub i) = 4 := four hxy
    simp only [Fintype.card_fin] at hh
    omega

/-- In particular, the construction has no pair (`HasPairF`). -/
theorem not_hasPair (hR : ∀ e ∈ R, ¬ e.IsDiag) (hM : ∀ v, M.degree v ≤ 1)
    (hdis : ∀ e ∈ R, e ∉ M.edgeSet) : ¬ HasPairF (graph M R) := by
  classical
  rintro ⟨u, v, p, q, hp, hq, hS, hE⟩
  let F : SimpleGraph (Vertex V R) := {
    Adj x y := y ∈ pairNbrs p q x
    symm := ⟨fun _ _ => mem_pairNbrs_symm⟩
    loopless := ⟨fun _ hx => (graph M R).ne_of_adj (adj_of_mem_pairNbrs hx) rfl⟩ }
  have hn : ∀ x, F.neighborFinset x = pairNbrs p q x := by
    intro x
    ext y
    simp only [mem_neighborFinset]
    rfl
  have hFG : F ≤ graph M R := fun _ _ hx => adj_of_mem_pairNbrs hx
  have hreg : ∀ x, F.degree x = 0 ∨ F.degree x = 4 := by
    intro x
    rw [← card_neighborFinset_eq_degree, hn]
    by_cases he : (pairNbrs p q x).Nonempty
    · obtain ⟨y, hy⟩ := he
      exact Or.inr (card_pairNbrs hp hq hS hE (mem_support_of_mem_pairNbrs hS hy))
    · exact Or.inl (card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp he))
  have hf := no_four_regular M R hFG hR hM hdis hreg
  have hu := card_pairNbrs hp hq hS hE p.start_mem_support
  obtain ⟨w, hw⟩ := card_pos.mp (by omega : 0 < (pairNbrs p q u).card)
  have hw' : F.Adj u w := hw
  simp only [hf, bot_adj] at hw'

omit [DecidableEq V] in
lemma vertex_count : Fintype.card (Vertex V R) = Fintype.card V + R.card + 2 := by
  simp only [Vertex, Fintype.card_sum, Fintype.card_coe, Fintype.card_fin]
  omega

omit [Fintype V] in
lemma row_original_hub (v : V) : row (graph M R) (original v) hub = 2 := by
  change (univ.filter (fun _ : Fin 2 => True)).card = 2
  simp only [filter_true, card_univ, Fintype.card_fin]

lemma degree_hub (i : Fin 2) :
    (graph M R).degree (hub i) = Fintype.card V + R.card + 1 := by
  rw [degree_parts]
  have h1 : row (graph M R) (hub i) original = Fintype.card V := by
    change (univ.filter (fun _ : V => True)).card = Fintype.card V
    simp only [filter_true, card_univ]
  have h2 : row (graph M R) (hub i) middle = R.card := by
    change (univ.filter (fun _ : R => True)).card = R.card
    simp only [filter_true, card_univ, Fintype.card_coe]
  have h3 : row (graph M R) (hub i) hub = 1 := by
    change (univ.filter (fun j : Fin 2 => i ≠ j)).card = 1
    fin_cases i <;> decide
  rw [h1, h2, h3]

/-- Count the retained matching edges, four edges per subdivision, and hub-to-original edges. -/
theorem edge_count (hR : ∀ e ∈ R, ¬ e.IsDiag) :
    (graph M R).edgeFinset.card = M.edgeFinset.card + 4 * R.card + 2 * Fintype.card V + 1 := by
  have hAB : ∑ a : V, row (graph M R) (original a) middle = 2 * R.card := by
    rw [cross_symm]
    simp only [row_middle_original, Sym2.card_toFinset_of_not_isDiag _ (hR _ (Subtype.prop _)),
      sum_const, card_univ, Fintype.card_coe, smul_eq_mul]
    omega
  have hA : ∑ a : V, (graph M R).degree (original a) =
      2 * M.edgeFinset.card + 2 * R.card + 2 * Fintype.card V := by
    simp only [degree_parts, row_original_original, row_original_hub, sum_add_distrib,
      M.sum_degrees_eq_twice_card_edges, hAB, sum_const, card_univ, smul_eq_mul]
    omega
  have hB : ∑ e : R, (graph M R).degree (middle e) = 4 * R.card := by
    simp only [degree_middle M R hR, sum_const, card_univ, Fintype.card_coe, smul_eq_mul]
    omega
  have hH : ∑ i : Fin 2, (graph M R).degree (hub i) =
      2 * (Fintype.card V + R.card + 1) := by
    simp only [degree_hub, sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
  have hs := (graph M R).sum_degrees_eq_twice_card_edges
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type] at hs
  change (∑ a : V, (graph M R).degree (original a)) +
    ((∑ e : R, (graph M R).degree (middle e)) +
    (∑ i : Fin 2, (graph M R).degree (hub i))) = _ at hs
  rw [hA, hB, hH] at hs
  omega

/-- The construction applied to a base graph H and its retained matching M. -/
abbrev ofBase (H M : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel M.Adj] :=
  graph M (H.edgeFinset \ M.edgeFinset)

variable (H : SimpleGraph V) [DecidableRel H.Adj]

lemma remainder_nondiag : ∀ e ∈ H.edgeFinset \ M.edgeFinset, ¬ e.IsDiag :=
  fun _ he => H.not_isDiag_of_mem_edgeFinset (mem_sdiff.mp he).1

lemma remainder_disjoint : ∀ e ∈ H.edgeFinset \ M.edgeFinset, e ∉ M.edgeSet := by
  intro e he
  simpa only [mem_edgeFinset] using (mem_sdiff.mp he).2

/-- The matching-subdivision construction is pair-free for every finite simple base graph. -/
theorem ofBase_not_hasPair (hM : ∀ v, M.degree v ≤ 1) : ¬ HasPairF (ofBase H M) :=
  not_hasPair M _ (remainder_nondiag M H) hM (remainder_disjoint M H)

/-- N = t + e - m + 2. -/
theorem ofBase_vertex_count (hle : M ≤ H) :
    Fintype.card (Vertex V ↥(H.edgeFinset \ M.edgeFinset)) =
      Fintype.card V + H.edgeFinset.card - M.edgeFinset.card + 2 := by
  rw [vertex_count, card_sdiff_of_subset (edgeFinset_mono hle)]
  have := card_le_card (edgeFinset_mono hle)
  omega

/-- E = 2t + 4e - 3m + 1. -/
theorem ofBase_edge_count (hle : M ≤ H) :
    (ofBase H M).edgeFinset.card =
      2 * Fintype.card V + 4 * H.edgeFinset.card - 3 * M.edgeFinset.card + 1 := by
  rw [edge_count M _ (remainder_nondiag M H), card_sdiff_of_subset (edgeFinset_mono hle)]
  have := card_le_card (edgeFinset_mono hle)
  omega

/-- The resulting lower bound on `maxEdges`. -/
theorem lower_bound (hle : M ≤ H) (hM : ∀ v, M.degree v ≤ 1) :
    2 * Fintype.card V + 4 * H.edgeFinset.card - 3 * M.edgeFinset.card + 1 ≤
      maxEdges (Fintype.card V + H.edgeFinset.card - M.edgeFinset.card + 2) := by
  have h := card_edges_le_maxEdges (ofBase H M) (ofBase_not_hasPair M H hM)
    (ofBase_vertex_count M H hle)
  rwa [ofBase_edge_count M H hle] at h

/-- A perfect matching on 2k vertices, paired by their first coordinate. -/
def perfect (k : ℕ) : SimpleGraph (Fin k × Fin 2) where
  Adj a b := a.1 = b.1 ∧ a.2 ≠ b.2
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.2 rfl⟩

instance (k : ℕ) : DecidableRel (perfect k).Adj := fun _ _ =>
  inferInstanceAs (Decidable (_ = _ ∧ _ ≠ _))

lemma perfect_degree (k : ℕ) (a : Fin k × Fin 2) : (perfect k).degree a = 1 := by
  rw [← card_neighborFinset_eq_degree]
  have hfin : ∀ i j : Fin 2, i ≠ j ↔ j = Fin.rev i := by decide
  have hn : (perfect k).neighborFinset a = {(a.1, Fin.rev a.2)} := by
    ext b
    rw [mem_neighborFinset, mem_singleton]
    change (a.1 = b.1 ∧ a.2 ≠ b.2) ↔ b = (a.1, Fin.rev a.2)
    rw [hfin, Prod.ext_iff]
    exact and_congr eq_comm Iff.rfl
  rw [hn, card_singleton]

lemma perfect_edges (k : ℕ) : (perfect k).edgeFinset.card = k := by
  have h := (perfect k).sum_degrees_eq_twice_card_edges
  simp only [perfect_degree, sum_const, card_univ, Fintype.card_prod,
    Fintype.card_fin, smul_eq_mul, mul_one] at h
  omega

/-- Complete bases with perfect matchings yield 8k² - 3k + 1 edges on 2k² + 2 vertices. -/
theorem complete_even_lower_bound (k : ℕ) :
    8 * k ^ 2 - 3 * k + 1 ≤ maxEdges (2 * k ^ 2 + 2) := by
  have h := lower_bound (perfect k) (⊤ : SimpleGraph (Fin k × Fin 2)) le_top
    (fun a => (perfect_degree k a).le)
  rw [card_edgeFinset_top_eq_card_choose_two, Fintype.card_prod,
    Fintype.card_fin, Fintype.card_fin, perfect_edges] at h
  have hc : (k * 2).choose 2 = k * (2*k-1) := by
    rw [Nat.choose_two_right]
    rw [show k * 2 * (k * 2 - 1) = k * (2*k-1) * 2 by rw [mul_comm k 2]; ring,
      Nat.mul_div_cancel _ (by decide : 0 < 2)]
  rw [hc] at h
  have hs : k * (2*k-1) + k = 2*k^2 := by
    by_cases hk : k = 0
    · subst k; decide
    · have ht : 1 ≤ 2*k := by omega
      nlinarith [Nat.sub_add_cancel ht]
  have hn : k * 2 + k * (2*k-1) - k + 2 = 2*k^2+2 := by omega
  rw [hn] at h
  convert h using 1; omega

end MatchingSubdivision
end Erdos585
