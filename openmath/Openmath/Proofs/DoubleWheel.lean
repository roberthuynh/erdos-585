/-
Copyright 2026 The Formal Conjectures Authors.

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
import Openmath.Proofs.Counting

/-!
# Erdős 585: the double wheel and the lower bound `3 n - 5`

The double wheel `K₂ ∨ Cₘ` has two adjacent hubs joined to every vertex of an `m`-cycle, so it
has `3 m + 1` edges. For `m ≥ 5` it contains no two edge-disjoint cycles with the same vertex set:

* in such a pair `(p, q)` with common vertex set `S`, every `v ∈ S` has exactly two neighbours
  along `p` and two along `q`, and these are disjoint, so `v` has exactly four neighbours along
  the union of the two edge sets;
* a rim vertex has degree four, so if it lies in `S` then all its edges are used and all its
  neighbours lie in `S`; propagating along the rim, every spoke to a hub is used, and the hub has
  at least `m ≥ 5` neighbours along the union, a contradiction;
* if `S` has no rim vertex then `S` has at most two elements, but it has at least five
  (`five_le_card_support`).

Transporting along `Fin m ⊕ Fin 2 ≃ Fin (m + 2)` gives `3 n - 5 ∈ edgeCounts n` for `n ≥ 7`.
-/

open SimpleGraph Finset

namespace Erdos585

section Pair

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {u v : V} {p : G.Walk u u}
  {q : G.Walk v v}

/-- The neighbours of `x` along the edges of a walk are the neighbours of `x` in its subgraph. -/
lemma coe_filter_mem_edges (x : V) :
    ((p.support.toFinset.filter (fun w => s(x, w) ∈ p.edges)) : Set V) =
      p.toSubgraph.neighborSet x := by
  ext w
  simp only [Finset.coe_filter, List.mem_toFinset, Set.mem_ofPred_eq, Subgraph.mem_neighborSet,
    Walk.adj_toSubgraph_iff_mem_edges]
  exact ⟨fun h => h.2, fun h => ⟨p.snd_mem_support_of_mem_edges h, h⟩⟩

/-- A vertex of a cycle has exactly two neighbours along the cycle. -/
lemma card_filter_mem_edges (hp : p.IsCycle) {x : V} (hx : x ∈ p.support) :
    (p.support.toFinset.filter (fun w => s(x, w) ∈ p.edges)).card = 2 := by
  rw [← Set.ncard_coe_finset, coe_filter_mem_edges]
  exact hp.ncard_neighborSet_toSubgraph_eq_two hx

/-- In two edge-disjoint cycles with the same vertex set, every vertex has exactly four
neighbours along the union of the two edge sets. -/
theorem card_neighbors_of_pair (hp : p.IsCycle) (hq : q.IsCycle)
    (hS : p.support.toFinset = q.support.toFinset)
    (hE : Disjoint p.edges.toFinset q.edges.toFinset) {x : V} (hx : x ∈ p.support) :
    (p.support.toFinset.filter
      (fun w => s(x, w) ∈ p.edges.toFinset ∪ q.edges.toFinset)).card = 4 := by
  have hxq : x ∈ q.support := by
    rw [← List.mem_toFinset, ← hS, List.mem_toFinset]
    exact hx
  have h1 := card_filter_mem_edges hp hx
  have h2 := card_filter_mem_edges hq hxq
  rw [← hS] at h2
  have hsplit : p.support.toFinset.filter
      (fun w => s(x, w) ∈ p.edges.toFinset ∪ q.edges.toFinset) =
      p.support.toFinset.filter (fun w => s(x, w) ∈ p.edges) ∪
        p.support.toFinset.filter (fun w => s(x, w) ∈ q.edges) := by
    rw [← Finset.filter_or]
    simp only [Finset.mem_union, List.mem_toFinset]
  rw [hsplit, Finset.card_union_of_disjoint, h1, h2]
  rw [Finset.disjoint_left]
  intro w hw1 hw2
  rw [Finset.mem_filter] at hw1 hw2
  exact Finset.disjoint_left.1 hE (List.mem_toFinset.2 hw1.2) (List.mem_toFinset.2 hw2.2)

/-- In two edge-disjoint cycles with the same vertex set, every vertex has at least four
neighbours along the union of the two edge sets. -/
theorem four_le_card_neighbors_of_pair (hp : p.IsCycle) (hq : q.IsCycle)
    (hS : p.support.toFinset = q.support.toFinset)
    (hE : Disjoint p.edges.toFinset q.edges.toFinset) {x : V} (hx : x ∈ p.support) :
    4 ≤ (p.support.toFinset.filter
      (fun w => s(x, w) ∈ p.edges.toFinset ∪ q.edges.toFinset)).card :=
  (card_neighbors_of_pair hp hq hS hE hx).ge

/-- A neighbour of `x` along the union of the edge sets of two cycles with the same vertex set
lies in that vertex set and is a neighbour of `x` in `G`. -/
theorem mem_support_and_adj_of_mem_union_edges
    (hS : p.support.toFinset = q.support.toFinset) {x w : V}
    (h : s(x, w) ∈ p.edges.toFinset ∪ q.edges.toFinset) :
    w ∈ p.support.toFinset ∧ G.Adj x w := by
  rw [Finset.mem_union, List.mem_toFinset, List.mem_toFinset] at h
  rcases h with h | h
  · exact ⟨List.mem_toFinset.2 (p.snd_mem_support_of_mem_edges h), p.adj_of_mem_edges h⟩
  · rw [hS]
    exact ⟨List.mem_toFinset.2 (q.snd_mem_support_of_mem_edges h), q.adj_of_mem_edges h⟩

end Pair

/-- The double wheel `K₂ ∨ Cₘ`: the rim `Fin m` carries the cycle graph, the two hubs `Fin 2` are
adjacent to each other and to every rim vertex. -/
def doubleWheel (m : ℕ) : SimpleGraph (Fin m ⊕ Fin 2) where
  Adj
    | .inl i, .inl j => (cycleGraph m).Adj i j
    | .inl _, .inr _ => True
    | .inr _, .inl _ => True
    | .inr a, .inr b => a ≠ b
  symm := ⟨by
    rintro (i | a) (j | b) h
    · exact (cycleGraph m).adj_symm h
    · trivial
    · trivial
    · exact Ne.symm h⟩
  loopless := ⟨by
    rintro (i | a) h
    · exact (cycleGraph m).loopless.irrefl i h
    · exact h rfl⟩

section DoubleWheel

@[simp] lemma doubleWheel_adj_inl_inl {m : ℕ} {i j : Fin m} :
    (doubleWheel m).Adj (.inl i) (.inl j) ↔ (cycleGraph m).Adj i j := Iff.rfl

@[simp] lemma doubleWheel_adj_inl_inr {m : ℕ} {i : Fin m} {a : Fin 2} :
    (doubleWheel m).Adj (.inl i) (.inr a) := trivial

@[simp] lemma doubleWheel_adj_inr_inl {m : ℕ} {a : Fin 2} {i : Fin m} :
    (doubleWheel m).Adj (.inr a) (.inl i) := trivial

@[simp] lemma doubleWheel_adj_inr_inr {m : ℕ} {a b : Fin 2} :
    (doubleWheel m).Adj (.inr a) (.inr b) ↔ a ≠ b := Iff.rfl

instance (m : ℕ) : DecidableRel (doubleWheel m).Adj
  | .inl i, .inl j => inferInstanceAs (Decidable ((cycleGraph m).Adj i j))
  | .inl _, .inr _ => inferInstanceAs (Decidable True)
  | .inr _, .inl _ => inferInstanceAs (Decidable True)
  | .inr a, .inr b => inferInstanceAs (Decidable (a ≠ b))

/-- The neighbours of a rim vertex: its neighbours on the cycle and both hubs. -/
lemma neighborFinset_doubleWheel_inl (m : ℕ) (i : Fin m) :
    (doubleWheel m).neighborFinset (.inl i) = ((cycleGraph m).neighborFinset i).disjSum univ := by
  ext (j | a) <;> simp

/-- The neighbours of a hub: every rim vertex and the other hub. -/
lemma neighborFinset_doubleWheel_inr (m : ℕ) (a : Fin 2) :
    (doubleWheel m).neighborFinset (.inr a) = univ.disjSum {a}ᶜ := by
  ext (j | b) <;> simp [eq_comm]

/-- A rim vertex of the double wheel on a rim of length at least three has degree four. -/
lemma degree_doubleWheel_inl (k : ℕ) (i : Fin (k + 3)) :
    (doubleWheel (k + 3)).degree (.inl i) = 4 := by
  rw [← card_neighborFinset_eq_degree, neighborFinset_doubleWheel_inl, card_disjSum,
    card_neighborFinset_eq_degree, cycleGraph_degree_three_le, card_univ, Fintype.card_fin]

/-- A hub of the double wheel on a rim of length `m` has degree `m + 1`. -/
lemma degree_doubleWheel_inr (m : ℕ) (a : Fin 2) :
    (doubleWheel m).degree (.inr a) = m + 1 := by
  rw [← card_neighborFinset_eq_degree, neighborFinset_doubleWheel_inr, card_disjSum,
    card_univ, Fintype.card_fin, card_compl, card_singleton, Fintype.card_fin]

/-- The neighbours of a rim vertex: its two rim neighbours and the two hubs. -/
lemma neighborFinset_doubleWheel_inl_eq (k : ℕ) (i : Fin (k + 3)) :
    (doubleWheel (k + 3)).neighborFinset (.inl i) =
      {.inl (i - 1), .inl (i + 1), .inr 0, .inr 1} := by
  rw [neighborFinset_doubleWheel_inl, cycleGraph_neighborFinset]
  ext (j | a)
  · simp
  · fin_cases a <;> simp

/-- The double wheel on a rim of length `k + 3` has `3 (k + 3) + 1` edges. -/
theorem ncard_edgeSet_doubleWheel (k : ℕ) :
    (doubleWheel (k + 3)).edgeSet.ncard = 3 * (k + 3) + 1 := by
  rw [← coe_edgeFinset, Set.ncard_coe_finset]
  have h := sum_degrees_eq_twice_card_edges (doubleWheel (k + 3))
  rw [Fintype.sum_sum_type] at h
  simp only [degree_doubleWheel_inl, degree_doubleWheel_inr, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul] at h
  omega

end DoubleWheel

section NoPair

open Fin.NatCast in
/-- A predicate on `Fin n` that holds at one point and is preserved by `+ 1` holds everywhere. -/
lemma fin_forall_of_add_one {n : ℕ} [NeZero n] {P : Fin n → Prop} (h : ∀ i, P i → P (i + 1))
    {i₀ : Fin n} (h₀ : P i₀) (j : Fin n) : P j := by
  have hn : ∀ m : ℕ, P (i₀ + (m : Fin n)) := by
    intro m
    induction m with
    | zero => simpa using h₀
    | succ m ih =>
      have := h _ ih
      rwa [Nat.cast_succ, ← add_assoc]
  have := hn (j - i₀).val
  rwa [Fin.cast_val_eq_self, add_sub_cancel] at this

/-- For a rim of length at least five, the double wheel has no two edge-disjoint cycles with the
same vertex set. -/
theorem doubleWheel_not_hasPair (k : ℕ) (hk : 2 ≤ k) :
    ¬ HasPairF (doubleWheel (k + 3)) := by
  rintro ⟨u, v, p, q, hp, hq, hS, hE⟩
  -- a rim vertex of `S` uses all four of its edges
  have key : ∀ i : Fin (k + 3), Sum.inl i ∈ p.support.toFinset →
      ∀ w, (doubleWheel (k + 3)).Adj (Sum.inl i) w →
        s(Sum.inl i, w) ∈ p.edges.toFinset ∪ q.edges.toFinset := by
    intro i hi w hw
    have h4 := card_neighbors_of_pair hp hq hS hE (List.mem_toFinset.1 hi)
    have hsub : p.support.toFinset.filter
        (fun w => s(Sum.inl i, w) ∈ p.edges.toFinset ∪ q.edges.toFinset) ⊆
        (doubleWheel (k + 3)).neighborFinset (Sum.inl i) := by
      intro w hw
      rw [Finset.mem_filter] at hw
      rw [mem_neighborFinset]
      exact (mem_support_and_adj_of_mem_union_edges hS hw.2).2
    have heq := Finset.eq_of_subset_of_card_le hsub
      (by rw [card_neighborFinset_eq_degree, degree_doubleWheel_inl, h4])
    have hw' : w ∈ (doubleWheel (k + 3)).neighborFinset (Sum.inl i) :=
      (mem_neighborFinset _ _ _).2 hw
    rw [← heq, Finset.mem_filter] at hw'
    exact hw'.2
  have memS : ∀ x w, s(x, w) ∈ p.edges.toFinset ∪ q.edges.toFinset →
      w ∈ p.support.toFinset :=
    fun x w h => (mem_support_and_adj_of_mem_union_edges hS h).1
  -- the rim part of `S` is closed under `+ 1`
  have step : ∀ i : Fin (k + 3), Sum.inl i ∈ p.support.toFinset →
      Sum.inl (i + 1) ∈ p.support.toFinset := by
    intro i hi
    apply memS _ _ (key i hi _ _)
    rw [doubleWheel_adj_inl_inl, cycleGraph_adj]
    right
    exact add_sub_cancel_left i 1
  -- `S` contains a rim vertex, as it has at least five elements
  have hrim : ∃ i : Fin (k + 3), Sum.inl i ∈ p.support.toFinset := by
    by_contra h
    push Not at h
    have hsub : p.support.toFinset ⊆ Finset.univ.map Function.Embedding.inr := by
      intro x hx
      rcases x with i | a
      · exact absurd hx (h i)
      · simp
    have h1 := Finset.card_le_card hsub
    have h5 := five_le_card_support hp hq hS hE
    rw [Finset.card_map, Finset.card_univ, Fintype.card_fin] at h1
    omega
  obtain ⟨i₀, hi₀⟩ := hrim
  -- so `S` contains every rim vertex
  have hall : ∀ j : Fin (k + 3), Sum.inl j ∈ p.support.toFinset :=
    fin_forall_of_add_one (P := fun j => Sum.inl j ∈ p.support.toFinset) step hi₀
  -- every spoke to the hub `0` is used, and the hub lies in `S`
  have hspoke : ∀ j : Fin (k + 3),
      s(Sum.inr 0, Sum.inl j) ∈ p.edges.toFinset ∪ q.edges.toFinset := by
    intro j
    rw [Sym2.eq_swap]
    exact key j (hall j) _ doubleWheel_adj_inl_inr
  have hhub : (Sum.inr 0 : Fin (k + 3) ⊕ Fin 2) ∈ p.support :=
    List.mem_toFinset.1 (memS _ _ (key i₀ hi₀ (Sum.inr 0) doubleWheel_adj_inl_inr))
  -- so the hub has `k + 3 ≥ 5` neighbours along the union, not four
  have h4 := card_neighbors_of_pair hp hq hS hE hhub
  have hsub : Finset.univ.map Function.Embedding.inl ⊆ p.support.toFinset.filter
      (fun w => s(Sum.inr 0, w) ∈ p.edges.toFinset ∪ q.edges.toFinset) := by
    intro w hw
    rw [Finset.mem_map] at hw
    obtain ⟨j, -, rfl⟩ := hw
    rw [Finset.mem_filter]
    exact ⟨hall j, hspoke j⟩
  have := Finset.card_le_card hsub
  rw [h4, Finset.card_map, Finset.card_univ, Fintype.card_fin] at this
  omega

end NoPair

section Transport

/-- An injective homomorphism carries two edge-disjoint cycles with the same vertex set to two
edge-disjoint cycles with the same vertex set. -/
theorem hasPair_of_injective {V W : Type*} [DecidableEq V] [DecidableEq W] {G : SimpleGraph V}
    {G' : SimpleGraph W} (f : G →g G') (hf : Function.Injective f)
    (h : HasPairF G) : HasPairF G' := by
  obtain ⟨u, v, p, q, hp, hq, hS, hE⟩ := h
  have hsupp : ∀ {a : V} (r : G.Walk a a),
      (r.map f).support.toFinset = r.support.toFinset.image f := by
    intro a r
    ext x
    simp [Walk.support_map]
  have hedges : ∀ {a : V} (r : G.Walk a a),
      (r.map f).edges.toFinset = r.edges.toFinset.image (Sym2.map f) := by
    intro a r
    ext e
    simp [Walk.edges_map]
  refine ⟨f u, f v, p.map f, q.map f, (Walk.isCycle_map_iff_of_injective hf).2 hp,
    (Walk.isCycle_map_iff_of_injective hf).2 hq, ?_, ?_⟩
  · rw [hsupp, hsupp, hS]
  · rw [hedges, hedges]
    exact (Finset.disjoint_image (Sym2.map.injective hf)).2 hE

/-- For `n ≥ 7`, some graph on `n` vertices with `3 n - 5` edges has no two edge-disjoint cycles
with the same vertex set: the double wheel on a rim of length `n - 2`. -/
theorem three_mul_sub_five_mem_edgeCounts (n : ℕ) (hn : 7 ≤ n) : 3 * n - 5 ∈ edgeCounts n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
  let e : Fin (k + 3) ⊕ Fin 2 ≃ Fin (k + 5) := finSumFinEquiv.trans (finCongr (by omega))
  refine ⟨(doubleWheel (k + 3)).map e, ?_, ?_⟩
  · intro h
    have iso := Iso.map e (doubleWheel (k + 3))
    exact doubleWheel_not_hasPair k (by omega)
      (hasPair_of_injective iso.symm.toHom iso.symm.injective h)
  · have hmap := edgeSet_map e.toEmbedding (doubleWheel (k + 3))
    rw [Equiv.coe_toEmbedding] at hmap
    rw [hmap, Set.ncard_image_of_injective _ e.toEmbedding.sym2Map.injective,
      ncard_edgeSet_doubleWheel]
    omega

/-- Any maximum of `edgeCounts n` for `n ≥ 7` is at least `3 n - 5`. -/
theorem three_mul_sub_five_le_of_isGreatest (n : ℕ) (hn : 7 ≤ n) {M : ℕ}
    (h : IsGreatest (edgeCounts n) M) : 3 * n - 5 ≤ M :=
  h.2 (three_mul_sub_five_mem_edgeCounts n hn)

end Transport

end Erdos585
