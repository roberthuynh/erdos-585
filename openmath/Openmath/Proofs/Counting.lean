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
import Openmath.Proofs.Compat

/-!
# Erdős 585: counting lemmas for small vertex sets

Two edge-disjoint cycles with the same vertex set `S` use `2 |S|` distinct edges inside `S`,
so `2 |S| ≤ |S|.choose 2` and `|S| ≥ 5`. Consequences: no graph on at most four vertices has
such a pair, the answer for `n ≤ 4` is `n.choose 2`, and `K₅` minus an edge has no such pair.
-/

open SimpleGraph Finset

namespace Erdos585

section CycleFacts

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

/-- A cycle traverses `p.length` distinct edges. -/
lemma card_edges_toFinset_of_isCycle {u : V} {p : G.Walk u u} (hp : p.IsCycle) :
    p.edges.toFinset.card = p.length := by
  rw [List.toFinset_card_of_nodup hp.edges_nodup, Walk.length_edges]

/-- A cycle visits `p.length` distinct vertices. -/
lemma card_support_toFinset_of_isCycle {u : V} {p : G.Walk u u} (hp : p.IsCycle) :
    p.support.toFinset.card = p.length := by
  have hmem : u ∈ p.support.tail := p.end_mem_tail_support hp.not_nil
  have hsupp : p.support.toFinset = p.support.tail.toFinset := by
    ext x
    simp only [List.mem_toFinset]
    constructor
    · intro hx
      rw [← p.cons_tail_support, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hmem
      · exact hx
    · exact List.mem_of_mem_tail
  rw [hsupp, List.toFinset_card_of_nodup hp.support_nodup, List.length_tail,
    Walk.length_support, Nat.add_sub_cancel]

/-- Every edge of a walk joins two distinct vertices of its support. -/
lemma mem_image_offDiag_of_mem_edges {u v : V} (p : G.Walk u v) {e : Sym2 V}
    (he : e ∈ p.edges) : e ∈ p.support.toFinset.offDiag.image Sym2.mk.uncurry := by
  induction e using Sym2.ind with
  | h a b =>
    exact Finset.mem_image.2 ⟨(a, b), Finset.mem_offDiag.2
      ⟨List.mem_toFinset.2 (p.fst_mem_support_of_mem_edges he),
        List.mem_toFinset.2 (p.snd_mem_support_of_mem_edges he),
        G.ne_of_adj (p.adj_of_mem_edges he)⟩, rfl⟩

/-- Every edge of a graph on a finite type joins two distinct vertices. -/
lemma mem_image_offDiag_univ_of_mem_edgeSet [Fintype V] {e : Sym2 V} (he : e ∈ G.edgeSet) :
    e ∈ (Finset.univ : Finset V).offDiag.image Sym2.mk.uncurry := by
  induction e using Sym2.ind with
  | h a b =>
    exact Finset.mem_image.2 ⟨(a, b), Finset.mem_offDiag.2
      ⟨Finset.mem_univ _, Finset.mem_univ _, G.ne_of_adj (G.mem_edgeSet.1 he)⟩, rfl⟩

end CycleFacts

section Pair

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {u v : V} {p : G.Walk u u}
  {q : G.Walk v v}

/-- Two edge-disjoint cycles with the same vertex set `S` together use `2 |S|` edges. -/
lemma card_union_edges (hp : p.IsCycle) (hq : q.IsCycle)
    (hS : p.support.toFinset = q.support.toFinset)
    (hE : Disjoint p.edges.toFinset q.edges.toFinset) :
    (p.edges.toFinset ∪ q.edges.toFinset).card = 2 * p.support.toFinset.card := by
  rw [Finset.card_union_of_disjoint hE, card_edges_toFinset_of_isCycle hp,
    card_edges_toFinset_of_isCycle hq, ← card_support_toFinset_of_isCycle hp,
    ← card_support_toFinset_of_isCycle hq, hS]
  omega

/-- The edges of two cycles with the same vertex set `S` are pairs of distinct points of `S`. -/
lemma union_edges_subset (hS : p.support.toFinset = q.support.toFinset) :
    p.edges.toFinset ∪ q.edges.toFinset ⊆ p.support.toFinset.offDiag.image Sym2.mk.uncurry := by
  intro e he
  rw [Finset.mem_union, List.mem_toFinset, List.mem_toFinset] at he
  rcases he with he | he
  · exact mem_image_offDiag_of_mem_edges p he
  · rw [hS]
    exact mem_image_offDiag_of_mem_edges q he

/-- Two edge-disjoint cycles with the same vertex set `S` force `2 |S| ≤ |S|.choose 2`. -/
lemma two_mul_card_le_choose_two (hp : p.IsCycle) (hq : q.IsCycle)
    (hS : p.support.toFinset = q.support.toFinset)
    (hE : Disjoint p.edges.toFinset q.edges.toFinset) :
    2 * p.support.toFinset.card ≤ p.support.toFinset.card.choose 2 := by
  rw [← card_union_edges hp hq hS hE, ← Sym2.card_image_offDiag p.support.toFinset]
  exact Finset.card_le_card (union_edges_subset hS)

/-- Two edge-disjoint cycles with the same vertex set `S` force `|S| ≥ 5`. -/
lemma five_le_card_support (hp : p.IsCycle) (hq : q.IsCycle)
    (hS : p.support.toFinset = q.support.toFinset)
    (hE : Disjoint p.edges.toFinset q.edges.toFinset) :
    5 ≤ p.support.toFinset.card := by
  have h := two_mul_card_le_choose_two hp hq hS hE
  have h3 : 3 ≤ p.support.toFinset.card := by
    rw [card_support_toFinset_of_isCycle hp]
    exact hp.three_le_length
  by_contra hlt
  have h4 : p.support.toFinset.card ≤ 4 := by omega
  generalize p.support.toFinset.card = k at h h3 h4
  interval_cases k <;> revert h <;> decide

end Pair

/-- If `G` has two edge-disjoint cycles with the same vertex set, that vertex set has at least
five elements. -/
theorem five_le_card_of_hasTwoEdgeDisjointCyclesSameVertexSet {V : Type*} [Fintype V]
    [DecidableEq V] {G : SimpleGraph V} (h : HasPairF G) :
    ∃ (u : V) (p : G.Walk u u), p.IsCycle ∧ 5 ≤ p.support.toFinset.card := by
  obtain ⟨u, v, p, q, hp, hq, hS, hE⟩ := h
  exact ⟨u, p, hp, five_le_card_support hp hq hS hE⟩

/-- No graph on at most four vertices has two edge-disjoint cycles with the same vertex set. -/
theorem not_hasPair_of_card_le_four' {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hV : Fintype.card V ≤ 4) :
    ¬ HasPairF G := by
  intro h
  obtain ⟨u, p, -, h5⟩ := five_le_card_of_hasTwoEdgeDisjointCyclesSameVertexSet h
  have := Finset.card_le_univ p.support.toFinset
  omega

/-- For `n ≤ 4` the maximum is `n.choose 2`, attained by the complete graph. -/
theorem le_four' (n : ℕ) (hn : n ≤ 4) : IsGreatest (edgeCounts n) (n.choose 2) := by
  classical
  refine ⟨⟨⊤, not_hasPair_of_card_le_four' _ (by simpa using hn), ?_⟩, ?_⟩
  · rw [← coe_edgeFinset, Set.ncard_coe_finset, card_edgeFinset_top_eq_card_choose_two,
      Fintype.card_fin]
  · rintro m ⟨G, -, rfl⟩
    rw [← coe_edgeFinset, Set.ncard_coe_finset]
    simpa using G.card_edgeFinset_le_card_choose_two

/-- `K₅` minus an edge has no two edge-disjoint cycles with the same vertex set: they would need
ten distinct edges among its nine. -/
theorem not_hasPair_top_deleteEdge_five :
    ¬ HasPairF ((⊤ : SimpleGraph (Fin 5)).deleteEdges {s(0, 1)}) := by
  rintro ⟨u, v, p, q, hp, hq, hS, hE⟩
  have hsub : p.edges.toFinset ∪ q.edges.toFinset ⊆
      ((Finset.univ : Finset (Fin 5)).offDiag.image Sym2.mk.uncurry).erase s(0, 1) := by
    intro e he
    rw [Finset.mem_union, List.mem_toFinset, List.mem_toFinset] at he
    have heG : e ∈ ((⊤ : SimpleGraph (Fin 5)).deleteEdges {s(0, 1)}).edgeSet := by
      rcases he with he | he
      · exact p.edges_subset_edgeSet he
      · exact q.edges_subset_edgeSet he
    rw [edgeSet_deleteEdges] at heG
    exact Finset.mem_erase.2 ⟨heG.2, mem_image_offDiag_univ_of_mem_edgeSet heG.1⟩
  have h01 : s(0, 1) ∈ (Finset.univ : Finset (Fin 5)).offDiag.image Sym2.mk.uncurry :=
    mem_image_offDiag_univ_of_mem_edgeSet (G := ⊤) ((top_adj 0 1).2 (by decide))
  have hcard := Finset.card_le_card hsub
  rw [card_union_edges hp hq hS hE, Finset.card_erase_of_mem h01, Sym2.card_image_offDiag,
    Finset.card_univ, Fintype.card_fin] at hcard
  have h5 := five_le_card_support hp hq hS hE
  have hc : Nat.choose 5 2 = 10 := by decide
  omega

end Erdos585
