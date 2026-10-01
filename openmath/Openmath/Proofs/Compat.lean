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
import Openmath.Target

/-!
# Erdős 585: the `Finset` form of the predicate and the bridge to `maxEdges`

The proofs in `Openmath/Proofs` were written against a `Finset` form of the predicate:
`HasPairF G` compares the vertex sets with `List.toFinset` and the edge sets with `Disjoint` on
`Finset`s, and `edgeCounts n` collects the edge counts of pair-free graphs on `Fin n`.

`hasPairF_iff` shows that `HasPairF` agrees with the upstream predicate
`HasTwoEdgeDisjointCyclesSameVertexSet`, so `edgeCounts n` is the set whose supremum is
`maxEdges n`. That set contains `0` (the edgeless graph) and is bounded by `n.choose 2`, so
`maxEdges n` is its greatest element.
-/

open SimpleGraph Finset

namespace Erdos585

/-- `G` contains two edge-disjoint cycles with the same vertex set, stated with `Finset`s: closed
walks `p` and `q` that are cycles, whose sets of visited vertices coincide and whose sets of
traversed edges are disjoint. -/
def HasPairF {V : Type*} [DecidableEq V] (G : SimpleGraph V) : Prop :=
  ∃ (u v : V) (p : G.Walk u u) (q : G.Walk v v), p.IsCycle ∧ q.IsCycle ∧
    p.support.toFinset = q.support.toFinset ∧ Disjoint p.edges.toFinset q.edges.toFinset

/-- The edge counts of graphs on `n` vertices that do not contain two edge-disjoint cycles with
the same vertex set. -/
def edgeCounts (n : ℕ) : Set ℕ :=
  {m | ∃ G : SimpleGraph (Fin n), ¬ HasPairF G ∧ G.edgeSet.ncard = m}

/-- The `Finset` form of the predicate agrees with the upstream one. -/
theorem hasPairF_iff {V : Type*} [DecidableEq V] (G : SimpleGraph V) :
    HasPairF G ↔ HasTwoEdgeDisjointCyclesSameVertexSet G := by
  constructor
  · rintro ⟨u, v, p, q, hp, hq, hS, hE⟩
    refine ⟨u, v, p, q, hp, hq, ?_, List.disjoint_toFinset_iff_disjoint.1 hE⟩
    rw [← List.coe_toFinset, ← List.coe_toFinset, hS]
  · rintro ⟨u, v, p, q, hp, hq, hS, hE⟩
    refine ⟨u, v, p, q, hp, hq, ?_, List.disjoint_toFinset_iff_disjoint.2 hE⟩
    rw [← Finset.coe_inj, List.coe_toFinset, List.coe_toFinset, hS]

/-- `edgeCounts n` is the set whose supremum defines `maxEdges n`. -/
theorem edgeCounts_eq (n : ℕ) : edgeCounts n =
    {m | ∃ G : SimpleGraph (Fin n), ¬ HasTwoEdgeDisjointCyclesSameVertexSet G ∧
      G.edgeSet.ncard = m} := by
  ext m
  simp only [edgeCounts, Set.mem_ofPred_eq, hasPairF_iff]

/-- The edgeless graph has no cycle, so no pair. -/
theorem not_hasPairF_bot {V : Type*} [DecidableEq V] : ¬ HasPairF (⊥ : SimpleGraph V) := by
  rintro ⟨u, v, p, q, hp, -, -, -⟩
  cases p with
  | nil => exact hp.not_nil Walk.Nil.nil
  | cons h _ => exact h

/-- `0 ∈ edgeCounts n`, witnessed by the edgeless graph. -/
theorem zero_mem_edgeCounts (n : ℕ) : 0 ∈ edgeCounts n :=
  ⟨⊥, not_hasPairF_bot, by rw [edgeSet_bot, Set.ncard_empty]⟩

/-- Every graph on `Fin n` has at most `n.choose 2` edges. -/
theorem bddAbove_edgeCounts (n : ℕ) : BddAbove (edgeCounts n) := by
  classical
  refine ⟨n.choose 2, ?_⟩
  rintro m ⟨G, -, rfl⟩
  rw [← coe_edgeFinset, Set.ncard_coe_finset]
  simpa using G.card_edgeFinset_le_card_choose_two

/-- A greatest element of `edgeCounts n` is `maxEdges n`. -/
theorem maxEdges_eq_of_isGreatest {n M : ℕ} (h : IsGreatest (edgeCounts n) M) :
    maxEdges n = M := by
  rw [edgeCounts_eq] at h
  exact h.csSup_eq

/-- Every element of `edgeCounts n` is at most `maxEdges n`. -/
theorem le_maxEdges_of_mem {n m : ℕ} (h : m ∈ edgeCounts n) : m ≤ maxEdges n := by
  have hb := bddAbove_edgeCounts n
  rw [edgeCounts_eq] at h hb
  exact le_csSup hb h

/-- The supremum is attained: `maxEdges n ∈ edgeCounts n`. -/
theorem maxEdges_mem_edgeCounts (n : ℕ) : maxEdges n ∈ edgeCounts n := by
  have hne : (edgeCounts n).Nonempty := ⟨0, zero_mem_edgeCounts n⟩
  have hb := bddAbove_edgeCounts n
  rw [edgeCounts_eq] at hne hb ⊢
  exact Nat.sSup_mem hne hb

end Erdos585
