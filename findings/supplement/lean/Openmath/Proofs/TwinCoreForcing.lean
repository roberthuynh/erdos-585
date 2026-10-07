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
import Openmath.Proofs.BipartiteObstruction
import Openmath.Proofs.TwinZeroSum
import Openmath.Proofs.TwinDoubleCycle
import Mathlib.Combinatorics.SimpleGraph.Bipartite

/-!
# Faithful forcing from a twin incidence quotient

All host conclusions use the original Erdős 585 predicate. The represented-core
class below specifies every vertex and every adjacency. It does not assume that
an arbitrary host has already been partitioned into maximal twin classes.
-/

namespace Erdos585.TwinCoreForcing

open SimpleGraph Finset

variable {I R : Type*} [Fintype I] [Fintype R] [DecidableEq I] [DecidableEq R]

/-- Transport the original predicate through an injective actual graph map. -/
theorem faithfulPair_map {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (h : HasTwoEdgeDisjointCyclesSameVertexSet G) (f : G →g H)
    (hf : Function.Injective f) : HasTwoEdgeDisjointCyclesSameVertexSet H := by
  classical
  exact (hasPairF_iff H).mp (((hasPairF_iff G).mpr h).map f hf)

omit [Fintype I] in
/-- Counting incidences at a group agrees with counting its right neighbors. -/
theorem card_filter_fst (J : Finset (I × R)) (i : I) :
    (J.filter (fun e => e.1 = i)).card =
      (univ.filter (fun r => (i, r) ∈ J)).card := by
  apply Finset.card_bij (fun e _ => e.2)
  · intro e he
    obtain ⟨he, hi⟩ := mem_filter.mp he
    exact mem_filter.mpr ⟨mem_univ _, by simpa only [← hi] using he⟩
  · intro e he f hf hef
    obtain ⟨_, hi⟩ := mem_filter.mp he
    obtain ⟨_, hj⟩ := mem_filter.mp hf
    exact Prod.ext (hi.trans hj.symm) hef
  · intro r hr
    exact ⟨(i, r), by simpa using hr, rfl⟩

omit [Fintype R] in
/-- Counting incidences at a right vertex agrees with counting its groups. -/
theorem card_filter_snd (J : Finset (I × R)) (r : R) :
    (J.filter (fun e => e.2 = r)).card =
      (univ.filter (fun i => (i, r) ∈ J)).card := by
  apply Finset.card_bij (fun e _ => e.1)
  · intro e he
    obtain ⟨he, hr⟩ := mem_filter.mp he
    exact mem_filter.mpr ⟨mem_univ _, by simpa only [← hr] using he⟩
  · intro e he f hf hef
    obtain ⟨_, hi⟩ := mem_filter.mp he
    obtain ⟨_, hj⟩ := mem_filter.mp hf
    exact Prod.ext hef (hi.trans hj.symm)
  · intro i hi
    exact ⟨(i, r), by simpa using hi, rfl⟩

theorem sum_left_card (J : Finset (I × R)) :
    ∑ i, (univ.filter (fun r => (i, r) ∈ J)).card = J.card := by
  simp_rw [← card_filter_fst]
  simpa using sum_card_fiberwise_eq_card_filter J univ Prod.fst

/-- Replace group `i` by exactly `k i` false twins, with right vertices retained. -/
def groupedGraph (J : Finset (I × R)) (k : I → ℕ) :
    SimpleGraph ((Σ i, Fin (k i)) ⊕ R) where
  Adj a b := match a, b with
    | .inl i, .inr r => (i.1, r) ∈ J
    | .inr r, .inl i => (i.1, r) ∈ J
    | _, _ => False
  symm := ⟨by intro a b h; cases a <;> cases b <;> exact h⟩
  loopless := ⟨by intro a; cases a <;> simp⟩

instance (J : Finset (I × R)) (k : I → ℕ) : DecidableRel (groupedGraph J k).Adj := by
  intro a b
  cases a <;> cases b <;> dsimp [groupedGraph] <;> infer_instance

theorem groupedGraph_left_degree (J : Finset (I × R)) (k : I → ℕ)
    (i : I) (a : Fin (k i)) :
    (groupedGraph J k).degree (.inl ⟨i, a⟩) =
      (univ.filter (fun r => (i, r) ∈ J)).card := by
  have he : (groupedGraph J k).neighborFinset (.inl ⟨i, a⟩) =
      (univ.filter (fun r => (i, r) ∈ J)).map Function.Embedding.inr := by
    ext v
    simp only [mem_neighborFinset]
    cases v <;> simp [groupedGraph]
  rw [← card_neighborFinset_eq_degree, he, card_map]

omit [DecidableEq I] [DecidableEq R] in
theorem groupedGraph_bipartite (J : Finset (I × R)) (k : I → ℕ) :
    (groupedGraph J k).IsBipartiteWith
      (↑((univ : Finset (Σ i, Fin (k i))).map
        (Function.Embedding.inl : (Σ i, Fin (k i)) ↪ ((Σ i, Fin (k i)) ⊕ R))))
      (↑((univ : Finset R).map
        (Function.Embedding.inr : R ↪ ((Σ i, Fin (k i)) ⊕ R)))) := by
  constructor
  · apply Set.disjoint_left.mpr
    intro x hx hy
    cases x <;> simp_all
  · intro a b ha
    cases a <;> cases b <;> simp_all [groupedGraph]

theorem groupedGraph_edge_card (J : Finset (I × R)) (k : I → ℕ) :
    (groupedGraph J k).edgeFinset.card =
      ∑ i, k i * (univ.filter (fun r => (i, r) ∈ J)).card := by
  have hh := isBipartiteWith_sum_degrees_eq_card_edges (groupedGraph_bipartite J k)
  simp only [sum_map] at hh
  change (∑ x : (Σ i, Fin (k i)), (groupedGraph J k).degree (.inl x)) = _ at hh
  simp_rw [Fintype.sum_sigma, groupedGraph_left_degree] at hh
  simpa using hh.symm

theorem groupedGraph_right_degree (J : Finset (I × R)) (k : I → ℕ) (r : R) :
    (groupedGraph J k).degree (.inr r) =
      ∑ i ∈ univ.filter (fun i => (i, r) ∈ J), k i := by
  have he : (groupedGraph J k).neighborFinset (.inr r) =
      (univ.filter (fun x : (Σ i, Fin (k i)) => (x.1, r) ∈ J)).map
        Function.Embedding.inl := by
    ext v
    simp only [mem_neighborFinset]
    cases v <;> simp [groupedGraph]
  rw [← card_neighborFinset_eq_degree, he, card_map, card_eq_sum_ones]
  simp only [sum_filter, Fintype.sum_sigma]
  apply sum_congr rfl
  intro i _
  by_cases h : (i, r) ∈ J <;> simp [h]

theorem groupedGraph_right_quotient_bound (J : Finset (I × R)) (k : I → ℕ)
    (hk : ∀ i, 2 ≤ k i) (r : R) :
    2 * (univ.filter (fun i => (i, r) ∈ J)).card ≤
      (groupedGraph J k).degree (.inr r) := by
  rw [groupedGraph_right_degree]
  calc
    2 * (univ.filter (fun i => (i, r) ∈ J)).card =
        ∑ _i ∈ univ.filter (fun i => (i, r) ∈ J), 2 := by simp [Nat.mul_comm]
    _ ≤ _ := sum_le_sum (fun i _ => hk i)

/-- The exact critical edge count and the degree cap balance the two shores.
No sparsity or minimality assumption is needed for this counting fact. -/
theorem groupedGraph_balance (J : Finset (I × R)) (k : I → ℕ)
    (hmax : ∀ v, (groupedGraph J k).degree v ≤ 6)
    (hedges : (groupedGraph J k).edgeFinset.card + 2 =
      3 * Fintype.card ((Σ i, Fin (k i)) ⊕ R)) :
    (∑ i, k i) = Fintype.card R := by
  have hL := isBipartiteWith_sum_degrees_eq_card_edges (groupedGraph_bipartite J k)
  have hR := isBipartiteWith_sum_degrees_eq_card_edges' (groupedGraph_bipartite J k)
  simp only [sum_map] at hL hR
  change (∑ x : (Σ i, Fin (k i)), (groupedGraph J k).degree (.inl x)) = _ at hL
  change (∑ r : R, (groupedGraph J k).degree (.inr r)) = _ at hR
  have hL' := sum_le_sum (s := (univ : Finset (Σ i, Fin (k i))))
    (fun x _ => hmax (.inl x))
  have hR' := sum_le_sum (s := (univ : Finset R)) (fun r _ => hmax (.inr r))
  rw [hL] at hL'
  rw [hR] at hR'
  simp only [sum_const, card_univ, smul_eq_mul, Fintype.card_sigma, Fintype.card_fin]
    at hL' hR'
  simp only [Fintype.card_sum, Fintype.card_sigma, Fintype.card_fin] at hedges
  omega

theorem groupedGraph_right_nonempty (J : Finset (I × R)) (k : I → ℕ)
    (hmax : ∀ v, (groupedGraph J k).degree v ≤ 6)
    (hedges : (groupedGraph J k).edgeFinset.card + 2 =
      3 * Fintype.card ((Σ i, Fin (k i)) ⊕ R)) : Nonempty R := by
  have hb := groupedGraph_balance J k hmax hedges
  simp only [Fintype.card_sum, Fintype.card_sigma, Fintype.card_fin] at hedges
  rw [hb] at hedges
  apply Fintype.card_pos_iff.mp
  omega

/-- The host degree cap implies the quotient caps used by the selection theorem. -/
theorem groupedGraph_quotient_caps (J : Finset (I × R)) (k : I → ℕ)
    (hk : ∀ i, 2 ≤ k i) (hmax : ∀ v, (groupedGraph J k).degree v ≤ 6) :
    (∀ i, (J.filter (fun e => e.1 = i)).card ≤ 6) ∧
      (∀ r, (J.filter (fun e => e.2 = r)).card ≤ 3) := by
  constructor
  · intro i
    rw [card_filter_fst]
    simpa only [groupedGraph_left_degree] using
      hmax (.inl ⟨i, ⟨0, by have := hk i; omega⟩⟩)
  · intro r
    rw [card_filter_snd]
    have hr := groupedGraph_right_quotient_bound J k hk r
    have hcap := hmax (.inr r)
    omega

/-- Deficit two in groups of size two or three supplies the full incidence budget. -/
theorem incidence_budget_of_deficit_two (J : Finset (I × R)) (k : I → ℕ)
    (hk : ∀ i, k i = 2 ∨ k i = 3)
    (hl : ∀ i, (univ.filter (fun r => (i, r) ∈ J)).card ≤ 6)
    (hbal : (∑ i, k i) = Fintype.card R)
    (hdef : ∑ i, k i * (6 - (univ.filter (fun r => (i, r) ∈ J)).card) = 2) :
    3 * Fintype.card I + Fintype.card R ≤ J.card := by
  let d : I → ℕ := fun i => 6 - (univ.filter (fun r => (i, r) ∈ J)).card
  have hklo : ∀ i, 2 ≤ k i := by intro i; rcases hk i with h | h <;> omega
  have hkhi : ∀ i, k i ≤ 3 := by intro i; rcases hk i with h | h <;> omega
  have hdu : 2 * (∑ i, d i) ≤ 2 := by
    calc
      2 * (∑ i, d i) = ∑ i, 2 * d i := mul_sum ..
      _ ≤ ∑ i, k i * d i := sum_le_sum (fun i _ => Nat.mul_le_mul_right _ (hklo i))
      _ = 2 := hdef
  have hp : ∃ i, k i = 2 := by
    by_contra hh
    push Not at hh
    have hall : ∀ i, k i = 3 := fun i => (hk i).resolve_left (hh i)
    have hd3 : 3 * (∑ i, d i) = 2 := by
      rw [mul_sum]
      simpa only [hall] using hdef
    omega
  have hsize : Fintype.card R < 3 * Fintype.card I := by
    rw [← hbal]
    calc
      ∑ i, k i < ∑ _i : I, 3 := by
        apply sum_lt_sum (fun i _ => hkhi i)
        obtain ⟨i, hi⟩ := hp
        exact ⟨i, mem_univ _, by omega⟩
      _ = 3 * Fintype.card I := by simp [Nat.mul_comm]
  have hsum : J.card + (∑ i, d i) = 6 * Fintype.card I := by
    rw [← sum_left_card, ← sum_add_distrib]
    calc
      ∑ i, ((univ.filter (fun r => (i, r) ∈ J)).card + d i) = ∑ _i : I, 6 := by
        apply sum_congr rfl
        intro i _
        exact Nat.add_sub_of_le (hl i)
      _ = _ := by simp [Nat.mul_comm]
  omega

/-- The left shore of an exact represented core has total degree deficit two. -/
theorem groupedGraph_deficit_two (J : Finset (I × R)) (k : I → ℕ)
    (hklo : ∀ i, 1 ≤ k i)
    (hmax : ∀ v, (groupedGraph J k).degree v ≤ 6)
    (hedges : (groupedGraph J k).edgeFinset.card + 2 =
      3 * Fintype.card ((Σ i, Fin (k i)) ⊕ R)) :
    ∑ i, k i * (6 - (univ.filter (fun r => (i, r) ∈ J)).card) = 2 := by
  have hl : ∀ i, (univ.filter (fun r => (i, r) ∈ J)).card ≤ 6 := by
    intro i
    simpa only [groupedGraph_left_degree] using
      hmax (.inl ⟨i, ⟨0, by have := hklo i; omega⟩⟩)
  have hbal := groupedGraph_balance J k hmax hedges
  have hs : (∑ i, k i * (6 - (univ.filter (fun r => (i, r) ∈ J)).card)) +
      (groupedGraph J k).edgeFinset.card = 6 * ∑ i, k i := by
    rw [groupedGraph_edge_card, ← sum_add_distrib, mul_sum]
    apply sum_congr rfl
    intro i _
    rw [← Nat.mul_add, Nat.sub_add_cancel (hl i), Nat.mul_comm]
  simp only [Fintype.card_sum, Fintype.card_sigma, Fintype.card_fin] at hedges
  rw [hbal] at hs hedges
  omega

/-- The exact degree-capped edge count forces the quotient size inequality in
the explicitly represented pair/triple class. -/
theorem groupedGraph_incidence_budget (J : Finset (I × R)) (k : I → ℕ)
    (hk : ∀ i, k i = 2 ∨ k i = 3)
    (hmax : ∀ v, (groupedGraph J k).degree v ≤ 6)
    (hedges : (groupedGraph J k).edgeFinset.card + 2 =
      3 * Fintype.card ((Σ i, Fin (k i)) ⊕ R)) :
    3 * Fintype.card I + Fintype.card R ≤ J.card := by
  have hklo : ∀ i, 1 ≤ k i := by intro i; rcases hk i with h | h <;> omega
  have hl : ∀ i, (univ.filter (fun r => (i, r) ∈ J)).card ≤ 6 := by
    intro i
    simpa only [groupedGraph_left_degree] using
      hmax (.inl ⟨i, ⟨0, by have := hklo i; omega⟩⟩)
  exact incidence_budget_of_deficit_two J k hk hl
    (groupedGraph_balance J k hmax hedges)
    (groupedGraph_deficit_two J k hklo hmax hedges)

/-- Exact pair/triple cores supply a nonempty simultaneous selected incidence set. -/
theorem exists_selected_incidence_of_grouped_core (J : Finset (I × R)) (k : I → ℕ)
    (hk : ∀ i, k i = 2 ∨ k i = 3)
    (hmax : ∀ v, (groupedGraph J k).degree v ≤ 6)
    (hedges : (groupedGraph J k).edgeFinset.card + 2 =
      3 * Fintype.card ((Σ i, Fin (k i)) ⊕ R)) :
    ∃ K : Finset (I × R), K ⊆ J ∧ K.Nonempty ∧
      (∀ i, (K.filter (fun e => e.1 = i)).card = 0 ∨
        (K.filter (fun e => e.1 = i)).card = 4) ∧
      (∀ r, (K.filter (fun e => e.2 = r)).card = 0 ∨
        (K.filter (fun e => e.2 = r)).card = 2) := by
  have : Nonempty R := groupedGraph_right_nonempty J k hmax hedges
  have hklo : ∀ i, 2 ≤ k i := by intro i; rcases hk i with h | h <;> omega
  obtain ⟨hl, hr⟩ := groupedGraph_quotient_caps J k hklo hmax
  exact TwinZeroSum.exists_nonempty_selected_incidence J hl hr
    (groupedGraph_incidence_budget J k hk hmax hedges)

/-- Select the first two actual clones from every represented group. -/
def twoCloneEmbedding (k : I → ℕ) (hk : ∀ i, 2 ≤ k i) :
    (I × Bool) ↪ (Σ i, Fin (k i)) where
  toFun x := ⟨x.1, Fin.castLE (hk x.1) (finTwoEquiv.symm x.2)⟩
  inj' := by
    rintro ⟨i, b⟩ ⟨j, c⟩ h
    have hij : i = j := congrArg Sigma.fst h
    subst j
    have hv := congrArg (fun x : (Σ i, Fin (k i)) => x.2.val) h
    have hb : b = c := finTwoEquiv.symm.injective (Fin.ext hv)
    exact Prod.ext rfl hb

/-- The clone choice and all actual right vertices stay injective together. -/
def twoCloneHostEmbedding (k : I → ℕ) (hk : ∀ i, 2 ≤ k i) :
    ((I × Bool) ⊕ R) ↪ ((Σ i, Fin (k i)) ⊕ R) :=
  (twoCloneEmbedding k hk).sumMap (Function.Embedding.refl R)

omit [Fintype I] [Fintype R] [DecidableEq I] [DecidableEq R] in
theorem groupedGraph_twoClone_adj (J : Finset (I × R)) (k : I → ℕ)
    (hk : ∀ i, 2 ≤ k i) (i : I) (b : Bool) (r : R) (h : (i, r) ∈ J) :
    (groupedGraph J k).Adj
      (twoCloneHostEmbedding k hk (.inl (i, b)))
      (twoCloneHostEmbedding k hk (.inr r)) := h

omit [Fintype I] in
/-- Four actual twins with four common neighbors contain the original pair. -/
theorem groupedGraph_hasPair_of_large_group (J : Finset (I × R)) (k : I → ℕ)
    (i : I) (hki : 4 ≤ k i)
    (hli : 4 ≤ (univ.filter (fun r => (i, r) ∈ J)).card) :
    HasTwoEdgeDisjointCyclesSameVertexSet (groupedGraph J k) := by
  classical
  let S := univ.filter (fun r => (i, r) ∈ J)
  obtain ⟨b⟩ := Function.Embedding.nonempty_of_card_le
    (show Fintype.card (Fin 4) ≤ Fintype.card S by
      rw [Fintype.card_fin, Fintype.card_coe]
      exact hli)
  let L : Fin 4 → ((Σ i, Fin (k i)) ⊕ R) := fun a => .inl ⟨i, Fin.castLE hki a⟩
  let B : Fin 4 → ((Σ i, Fin (k i)) ⊕ R) := fun a => .inr (b a).val
  apply (hasPairF_iff _).mp
  apply BipartiteObstruction.hasPair_of_biclique_four (groupedGraph J k) L B
  · intro a c hac
    have hσ : (⟨i, Fin.castLE hki a⟩ : (Σ i, Fin (k i))) = ⟨i, Fin.castLE hki c⟩ :=
      Sum.inl_injective hac
    exact Fin.ext (congrArg (fun x : (Σ i, Fin (k i)) => x.2.val) hσ)
  · intro a c hac
    exact b.injective (Subtype.ext (Sum.inr_injective hac))
  · intro a c
    exact Sum.inl_ne_inr
  · intro a c
    exact (mem_filter.mp (b c).property).2

/-- In the exact core, any group of at least four twins directly forces a pair. -/
theorem groupedGraph_hasPair_of_large_group_core (J : Finset (I × R)) (k : I → ℕ)
    (hklo : ∀ i, 1 ≤ k i)
    (hmax : ∀ v, (groupedGraph J k).degree v ≤ 6)
    (hedges : (groupedGraph J k).edgeFinset.card + 2 =
      3 * Fintype.card ((Σ i, Fin (k i)) ⊕ R))
    (i : I) (hki : 4 ≤ k i) :
    HasTwoEdgeDisjointCyclesSameVertexSet (groupedGraph J k) := by
  have hdef := groupedGraph_deficit_two J k hklo hmax hedges
  have hi : k i * (6 - (univ.filter (fun r => (i, r) ∈ J)).card) ≤ 2 := by
    calc
      _ ≤ ∑ j, k j * (6 - (univ.filter (fun r => (j, r) ∈ J)).card) :=
        single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ i)
      _ = 2 := hdef
  apply groupedGraph_hasPair_of_large_group J k i hki
  have hi' : 4 * (6 - (univ.filter (fun r => (i, r) ∈ J)).card) ≤ 2 :=
    (Nat.mul_le_mul_right _ hki).trans hi
  omega

/-- A finite twin incidence quotient with the stated degree and size bounds
forces the original faithful pair in any actual host containing its clones.
The injection and adjacency hypotheses concern only actual vertices and edges. -/
theorem hasPair_of_twin_incidence {V : Type*} [Nonempty R]
    (G : SimpleGraph V) (J : Finset (I × R))
    (hleft : ∀ i, (J.filter (fun e => e.1 = i)).card ≤ 6)
    (hright : ∀ r, (J.filter (fun e => e.2 = r)).card ≤ 3)
    (hsize : 3 * Fintype.card I + Fintype.card R ≤ J.card)
    (f : ((I × Bool) ⊕ R) ↪ V)
    (hadj : ∀ i b r, (i, r) ∈ J → G.Adj (f (.inl (i, b))) (f (.inr r))) :
    HasTwoEdgeDisjointCyclesSameVertexSet G := by
  obtain ⟨K, hKJ, hK, hKl, hKr⟩ :=
    TwinZeroSum.exists_nonempty_selected_incidence J hleft hright hsize
  have hl : ∀ i, (univ.filter (fun r => (i, r) ∈ K)).card = 0 ∨
      (univ.filter (fun r => (i, r) ∈ K)).card = 4 := by
    intro i
    simpa only [card_filter_fst] using hKl i
  have hr : ∀ r, (univ.filter (fun i => (i, r) ∈ K)).card = 0 ∨
      (univ.filter (fun i => (i, r) ∈ K)).card = 2 := by
    intro r
    simpa only [card_filter_snd] using hKr r
  have hp := TwinDoubleCycle.hasPair_of_selected_incidence K hK hl hr
  let g : TwinDoubleCycle.twinGraph K →g G := {
    toFun := f
    map_rel' := by
      rintro (⟨i, b⟩ | r) (⟨j, c⟩ | s) h
      · exact False.elim h
      · exact hadj i b s (hKJ h)
      · exact (hadj j c r (hKJ h)).symm
      · exact False.elim h }
  exact faithfulPair_map hp g f.injective

/-- Every actual represented pair/triple core forces the original pair. -/
theorem groupedGraph_hasPair_of_pairTriple (J : Finset (I × R)) (k : I → ℕ)
    (hk : ∀ i, k i = 2 ∨ k i = 3)
    (hmax : ∀ v, (groupedGraph J k).degree v ≤ 6)
    (hedges : (groupedGraph J k).edgeFinset.card + 2 =
      3 * Fintype.card ((Σ i, Fin (k i)) ⊕ R)) :
    HasTwoEdgeDisjointCyclesSameVertexSet (groupedGraph J k) := by
  have : Nonempty R := groupedGraph_right_nonempty J k hmax hedges
  have hklo : ∀ i, 2 ≤ k i := by intro i; rcases hk i with h | h <;> omega
  obtain ⟨hl, hr⟩ := groupedGraph_quotient_caps J k hklo hmax
  exact hasPair_of_twin_incidence (groupedGraph J k) J hl hr
    (groupedGraph_incidence_budget J k hk hmax hedges)
    (twoCloneHostEmbedding k hklo) (groupedGraph_twoClone_adj J k hklo)

/-- Every explicit represented core with no singleton group forces the original
pair. The statement assumes no walks, cycle factors, or selected edge set. -/
theorem groupedGraph_hasPair_of_no_singletons (J : Finset (I × R)) (k : I → ℕ)
    (hk : ∀ i, 2 ≤ k i)
    (hmax : ∀ v, (groupedGraph J k).degree v ≤ 6)
    (hedges : (groupedGraph J k).edgeFinset.card + 2 =
      3 * Fintype.card ((Σ i, Fin (k i)) ⊕ R)) :
    HasTwoEdgeDisjointCyclesSameVertexSet (groupedGraph J k) := by
  by_cases hlarge : ∃ i, 4 ≤ k i
  · obtain ⟨i, hi⟩ := hlarge
    exact groupedGraph_hasPair_of_large_group_core J k (fun i => (hk i).trans' (by omega))
      hmax hedges i hi
  · have hsmall : ∀ i, k i = 2 ∨ k i = 3 := by
      intro i
      have hi := hk i
      have hn : ¬ 4 ≤ k i := fun hh => hlarge ⟨i, hh⟩
      omega
    exact groupedGraph_hasPair_of_pairTriple J k hsmall hmax hedges

end Erdos585.TwinCoreForcing
