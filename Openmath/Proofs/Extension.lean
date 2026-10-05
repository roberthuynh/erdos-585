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
import Openmath.Proofs.Counting
import Openmath.Proofs.Five

/-!
# Erdős 585: rigidity of a pair, an extension lemma, and a witness on nine vertices

In two edge-disjoint cycles `p`, `q` with the same vertex set `S`, every `v ∈ S` has two
neighbours along `p` and two along `q`, and these four are distinct because the edge sets are
disjoint. So `v` has degree at least four, and a vertex of degree at most three lies on no pair.

Consequently, adding a new vertex joined to three old vertices keeps a graph pair-free, and adds
three edges: `m ∈ edgeCounts n` gives `m + 3 ∈ edgeCounts (n + 1)` for `n ≥ 3`. Starting from
`K₅` minus an edge this gives `3 n - 6 ∈ edgeCounts n` for `n ≥ 5`.

On nine vertices, `K₂ ∨ θ(2,3,3)` (two adjacent hubs joined to a theta graph with paths of
lengths `2, 3, 3`) has `23` edges and no pair: the union of a pair is `4`-regular on its vertex
set, and a case analysis on which degree-four vertices it uses rules this out. Extending it gives
`3 n - 4 ∈ edgeCounts n` for `n ≥ 9`.
-/

open SimpleGraph Finset

namespace Erdos585

section Rigidity

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- The neighbours of `v` along the edges of a walk. -/
def walkNbrs {u w : V} (p : G.Walk u w) (v : V) : Finset V :=
  univ.filter fun x => s(v, x) ∈ p.edges

lemma mem_walkNbrs {u w v x : V} {p : G.Walk u w} : x ∈ walkNbrs p v ↔ s(v, x) ∈ p.edges := by
  simp [walkNbrs]

lemma coe_walkNbrs {u w : V} (p : G.Walk u w) (v : V) :
    (walkNbrs p v : Set V) = p.toSubgraph.neighborSet v := by
  ext x
  rw [Finset.mem_coe, mem_walkNbrs, Subgraph.mem_neighborSet, ← Subgraph.mem_edgeSet,
    Walk.mem_edges_toSubgraph]

/-- On a cycle, every vertex of the support has exactly two neighbours along the cycle. -/
lemma card_walkNbrs {u v : V} {p : G.Walk u u} (hp : p.IsCycle) (hv : v ∈ p.support) :
    (walkNbrs p v).card = 2 := by
  rw [← Set.ncard_coe_finset, coe_walkNbrs, hp.ncard_neighborSet_toSubgraph_eq_two hv]

/-- The neighbours of `v` along the edges of `p` or of `q`. -/
def pairNbrs {u w : V} (p : G.Walk u u) (q : G.Walk w w) (v : V) : Finset V :=
  walkNbrs p v ∪ walkNbrs q v

variable {u w : V} {p : G.Walk u u} {q : G.Walk w w}

lemma mem_pairNbrs {v x : V} : x ∈ pairNbrs p q v ↔ s(v, x) ∈ p.edges ∨ s(v, x) ∈ q.edges := by
  rw [pairNbrs, Finset.mem_union, mem_walkNbrs, mem_walkNbrs]

lemma adj_of_mem_pairNbrs {v x : V} (h : x ∈ pairNbrs p q v) : G.Adj v x := by
  rcases mem_pairNbrs.1 h with h | h
  · exact p.adj_of_mem_edges h
  · exact q.adj_of_mem_edges h

lemma mem_pairNbrs_symm {v x : V} (h : x ∈ pairNbrs p q v) : v ∈ pairNbrs p q x := by
  rw [mem_pairNbrs] at h ⊢
  rw [Sym2.eq_swap (a := x) (b := v)]
  exact h

lemma mem_support_of_mem_pairNbrs (hS : p.support.toFinset = q.support.toFinset) {v x : V}
    (h : x ∈ pairNbrs p q v) : v ∈ p.support := by
  rcases mem_pairNbrs.1 h with h | h
  · exact p.fst_mem_support_of_mem_edges h
  · rw [← List.mem_toFinset, hS, List.mem_toFinset]
    exact q.fst_mem_support_of_mem_edges h

/-- In a pair, every vertex of the common support has exactly four neighbours along the union. -/
lemma card_pairNbrs (hp : p.IsCycle) (hq : q.IsCycle) (hS : p.support.toFinset = q.support.toFinset)
    (hE : Disjoint p.edges.toFinset q.edges.toFinset) {v : V} (hv : v ∈ p.support) :
    (pairNbrs p q v).card = 4 := by
  have hv' : v ∈ q.support := by rw [← List.mem_toFinset, ← hS, List.mem_toFinset]; exact hv
  have hdisj : Disjoint (walkNbrs p v) (walkNbrs q v) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    rw [mem_walkNbrs] at hx hx'
    exact Finset.disjoint_left.1 hE (List.mem_toFinset.2 hx) (List.mem_toFinset.2 hx')
  rw [pairNbrs, card_union_of_disjoint hdisj, card_walkNbrs hp hv, card_walkNbrs hq hv']

/-- A vertex on a pair has at least four neighbours (stated with `Set.ncard`). -/
theorem four_le_ncard_neighborSet_of_mem_pair (hp : p.IsCycle) (hq : q.IsCycle)
    (hS : p.support.toFinset = q.support.toFinset) (hE : Disjoint p.edges.toFinset q.edges.toFinset)
    {v : V} (hv : v ∈ p.support) : 4 ≤ (G.neighborSet v).ncard := by
  rw [← card_pairNbrs hp hq hS hE hv, ← Set.ncard_coe_finset]
  exact Set.ncard_le_ncard (fun x hx => adj_of_mem_pairNbrs (Finset.mem_coe.1 hx))

/-- **Rigidity.** A vertex on a pair of edge-disjoint cycles with the same vertex set has degree
at least four. -/
theorem four_le_degree_of_mem_pair [DecidableRel G.Adj] (hp : p.IsCycle) (hq : q.IsCycle)
    (hS : p.support.toFinset = q.support.toFinset) (hE : Disjoint p.edges.toFinset q.edges.toFinset)
    {v : V} (hv : v ∈ p.support) : 4 ≤ G.degree v := by
  rw [← card_neighborFinset_eq_degree, ← card_pairNbrs hp hq hS hE hv]
  exact card_le_card fun x hx => (mem_neighborFinset _ _ _).2 (adj_of_mem_pairNbrs hx)

/-- A vertex with at most three neighbours is on no cycle of a pair (stated with `Set.ncard`). -/
theorem not_mem_support_of_ncard_le_three (hp : p.IsCycle) (hq : q.IsCycle)
    (hS : p.support.toFinset = q.support.toFinset) (hE : Disjoint p.edges.toFinset q.edges.toFinset)
    {v : V} (hv : (G.neighborSet v).ncard ≤ 3) : v ∉ p.support := fun h => by
  have := four_le_ncard_neighborSet_of_mem_pair hp hq hS hE h
  omega

/-- A vertex of degree at most three is on no cycle of a pair. -/
theorem not_mem_support_of_degree_le_three [DecidableRel G.Adj] (hp : p.IsCycle) (hq : q.IsCycle)
    (hS : p.support.toFinset = q.support.toFinset) (hE : Disjoint p.edges.toFinset q.edges.toFinset)
    {v : V} (hv : G.degree v ≤ 3) : v ∉ p.support := fun h => by
  have := four_le_degree_of_mem_pair hp hq hS hE h
  omega

end Rigidity

section Transport

variable {V W : Type*} [DecidableEq V] [DecidableEq W] {G : SimpleGraph V} {H : SimpleGraph W}

lemma toFinset_map_eq_image {α β : Type*} [DecidableEq α] [DecidableEq β] (f : α → β)
    (l : List α) : (l.map f).toFinset = l.toFinset.image f := by
  ext x
  simp

/-- The four pair conditions are invariant under mapping along an injective graph hom. -/
lemma pair_map_iff (f : G →g H) (hf : Function.Injective f) {u w : V} (p : G.Walk u u)
    (q : G.Walk w w) :
    ((p.map f).IsCycle ∧ (q.map f).IsCycle ∧
        (p.map f).support.toFinset = (q.map f).support.toFinset ∧
        Disjoint (p.map f).edges.toFinset (q.map f).edges.toFinset) ↔
      (p.IsCycle ∧ q.IsCycle ∧ p.support.toFinset = q.support.toFinset ∧
        Disjoint p.edges.toFinset q.edges.toFinset) := by
  rw [Walk.isCycle_map_iff_of_injective hf, Walk.isCycle_map_iff_of_injective hf,
    Walk.support_map, Walk.support_map, Walk.edges_map, Walk.edges_map, toFinset_map_eq_image,
    toFinset_map_eq_image, toFinset_map_eq_image, toFinset_map_eq_image,
    (Finset.image_injective hf).eq_iff, Finset.disjoint_image (Sym2.map.injective hf)]

end Transport

section Extension

variable {n : ℕ}

/-- Add a new vertex `Fin.last n` to a graph on `Fin n`, joined to `a`, `b` and `c`. -/
def extend (G : SimpleGraph (Fin n)) (a b c : Fin n) : SimpleGraph (Fin (n + 1)) :=
  G.map Fin.castSuccEmb ⊔
    fromEdgeSet {s(Fin.last n, a.castSucc), s(Fin.last n, b.castSucc), s(Fin.last n, c.castSucc)}

variable {G : SimpleGraph (Fin n)} {a b c : Fin n}

lemma extend_adj_castSucc {i j : Fin n} :
    (extend G a b c).Adj i.castSucc j.castSucc ↔ G.Adj i j := by
  rw [extend, sup_adj, map_adj, fromEdgeSet_adj]
  constructor
  · rintro (⟨i', j', h, hi, hj⟩ | ⟨h, -⟩)
    · rw [Fin.castSuccEmb_apply, Fin.castSucc_inj] at hi hj
      subst hi hj
      exact h
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Sym2.eq_iff] at h
      rcases h with (⟨h, -⟩ | ⟨-, h⟩) | (⟨h, -⟩ | ⟨-, h⟩) | (⟨h, -⟩ | ⟨-, h⟩) <;>
        exact absurd h (Fin.castSucc_ne_last _)
  · intro h
    exact Or.inl ⟨i, j, h, rfl, rfl⟩

lemma extend_adj_last {x : Fin (n + 1)} (h : (extend G a b c).Adj (Fin.last n) x) :
    x ∈ ({a.castSucc, b.castSucc, c.castSucc} : Set (Fin (n + 1))) := by
  rw [extend, sup_adj, map_adj, fromEdgeSet_adj] at h
  rcases h with ⟨i', j', -, hi, -⟩ | ⟨h, -⟩
  · exact absurd hi (Fin.castSucc_ne_last _)
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Sym2.congr_right] at h
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h

lemma ncard_neighborSet_last_le : ((extend G a b c).neighborSet (Fin.last n)).ncard ≤ 3 := by
  calc ((extend G a b c).neighborSet (Fin.last n)).ncard
      ≤ ({a.castSucc, b.castSucc, c.castSucc} : Set (Fin (n + 1))).ncard :=
        Set.ncard_le_ncard (fun x hx => extend_adj_last hx)
    _ ≤ 3 := by
        rw [← Finset.coe_singleton, ← Finset.coe_insert, ← Finset.coe_insert,
          Set.ncard_coe_finset]
        exact Finset.card_le_three

/-- The hom from the extended graph, restricted to the old vertices, back to `G`. -/
def extendPull (G : SimpleGraph (Fin n)) (a b c : Fin n) :
    (extend G a b c).induce {x | x ≠ Fin.last n} →g G where
  toFun x := x.1.castPred x.2
  map_rel' {x y} h := by
    have h' := induce_adj.1 h
    rw [← Fin.castSucc_castPred x.1 x.2, ← Fin.castSucc_castPred y.1 y.2] at h'
    exact extend_adj_castSucc.1 h'

lemma extendPull_injective : Function.Injective (extendPull G a b c) := by
  intro x y h
  change x.1.castPred x.2 = y.1.castPred y.2 at h
  exact Subtype.ext (Fin.castPred_inj.1 h)

/-- **Extension lemma.** Adding a vertex of degree three to a pair-free graph keeps it
pair-free. -/
theorem extend_not_hasPair (hG : ¬ HasPairF G) (a b c : Fin n) :
    ¬ HasPairF (extend G a b c) := by
  rintro ⟨u, w, p, q, hp, hq, hS, hE⟩
  have hlast : Fin.last n ∉ p.support :=
    not_mem_support_of_ncard_le_three hp hq hS hE ncard_neighborSet_last_le
  have hlast' : Fin.last n ∉ q.support := by
    rwa [← List.mem_toFinset, ← hS, List.mem_toFinset]
  have hps : ∀ x ∈ p.support, x ∈ {x : Fin (n + 1) | x ≠ Fin.last n} := by
    rintro x hx rfl
    exact hlast hx
  have hqs : ∀ x ∈ q.support, x ∈ {x : Fin (n + 1) | x ≠ Fin.last n} := by
    rintro x hx rfl
    exact hlast' hx
  have h1 := (pair_map_iff (Embedding.induce {x : Fin (n + 1) | x ≠ Fin.last n}).toHom
    (Embedding.induce (G := extend G a b c) _).injective (p.induce _ hps) (q.induce _ hqs)).1
    (by rw [Walk.map_induce, Walk.map_induce]; exact ⟨hp, hq, hS, hE⟩)
  have h2 := (pair_map_iff (extendPull G a b c) extendPull_injective _ _).2 h1
  exact hG ⟨_, _, _, _, h2⟩

/-- Adding three distinct edges at a new vertex adds three to the edge count. -/
theorem ncard_edgeSet_extend (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (extend G a b c).edgeSet.ncard = G.edgeSet.ncard + 3 := by
  have hT : ({s(Fin.last n, a.castSucc), s(Fin.last n, b.castSucc),
      s(Fin.last n, c.castSucc)} : Set (Sym2 (Fin (n + 1)))) \ Sym2.diagSet =
      {s(Fin.last n, a.castSucc), s(Fin.last n, b.castSucc), s(Fin.last n, c.castSucc)} := by
    rw [sdiff_eq_left, Set.disjoint_left]
    intro e he hd
    rw [Sym2.mem_diagSet] at hd
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
    rcases he with rfl | rfl | rfl <;>
      exact Fin.castSucc_ne_last _ (Sym2.mk_isDiag_iff.1 hd).symm
  have hdisj : Disjoint (Fin.castSuccEmb.sym2Map '' G.edgeSet)
      ({s(Fin.last n, a.castSucc), s(Fin.last n, b.castSucc), s(Fin.last n, c.castSucc)} :
        Set (Sym2 (Fin (n + 1)))) := by
    rw [Set.disjoint_left]
    rintro e ⟨e', -, rfl⟩ he
    induction e' using Sym2.ind with
    | h i j =>
      simp only [Function.Embedding.sym2Map_apply, Sym2.map_mk, Fin.castSuccEmb_apply,
        Set.mem_insert_iff, Set.mem_singleton_iff, Sym2.eq_iff] at he
      rcases he with (⟨h, -⟩ | ⟨-, h⟩) | (⟨h, -⟩ | ⟨-, h⟩) | (⟨h, -⟩ | ⟨-, h⟩) <;>
        exact Fin.castSucc_ne_last _ h
  have h3 : ({s(Fin.last n, a.castSucc), s(Fin.last n, b.castSucc),
      s(Fin.last n, c.castSucc)} : Set (Sym2 (Fin (n + 1)))).ncard = 3 := by
    rw [Set.ncard_eq_three]
    refine ⟨_, _, _, ?_, ?_, ?_, rfl⟩ <;>
      simpa [Sym2.congr_right, Fin.castSucc_inj]
  rw [extend, edgeSet_sup, edgeSet_map, edgeSet_fromEdgeSet, hT, Set.ncard_union_eq hdisj,
    Set.ncard_image_of_injective _ (Function.Embedding.injective _), h3]

/-- For `n ≥ 3`, `m ∈ edgeCounts n` gives `m + 3 ∈ edgeCounts (n + 1)`. -/
theorem mem_edgeCounts_succ {m : ℕ} (hn : 3 ≤ n) (hm : m ∈ edgeCounts n) :
    m + 3 ∈ edgeCounts (n + 1) := by
  obtain ⟨G, hG, rfl⟩ := hm
  refine ⟨extend G ⟨0, by omega⟩ ⟨1, by omega⟩ ⟨2, by omega⟩, extend_not_hasPair hG _ _ _,
    ncard_edgeSet_extend ?_ ?_ ?_⟩ <;> simp [Fin.ext_iff]

end Extension

/-- `3 n - 6 ∈ edgeCounts n` for `n ≥ 5`, from `K₅` minus an edge by repeated extension. -/
theorem three_mul_sub_six_mem (n : ℕ) (hn : 5 ≤ n) : 3 * n - 6 ∈ edgeCounts n := by
  induction n, hn using Nat.le_induction with
  | base => exact nine_mem_edgeCounts_five
  | succ n hn ih =>
    have h : 3 * (n + 1) - 6 = 3 * n - 6 + 3 := by omega
    rw [h]
    exact mem_edgeCounts_succ (by omega) ih

section Theta

/-- The edges of `K₂ ∨ θ(2,3,3)` on `Fin 9`. -/
def thetaWheelEdges : List (Fin 9 × Fin 9) :=
  [(0, 1), (0, 5), (0, 7), (0, 8), (1, 6), (1, 7), (1, 8), (2, 3), (2, 5), (2, 7), (2, 8),
    (3, 6), (3, 7), (3, 8), (4, 5), (4, 6), (4, 7), (4, 8), (5, 7), (5, 8), (6, 7), (6, 8), (7, 8)]

/-- `K₂ ∨ θ(2,3,3)` on `Fin 9`: the hubs `7` and `8` are adjacent to every other vertex, and
`0, …, 6` carry the theta graph with branch vertices `5`, `6` joined by the paths `5 - 4 - 6`,
`5 - 0 - 1 - 6` and `5 - 2 - 3 - 6`. -/
def thetaWheel : SimpleGraph (Fin 9) :=
  SimpleGraph.fromRel fun a b => (a, b) ∈ thetaWheelEdges

instance : DecidableRel thetaWheel.Adj := fun a b =>
  inferInstanceAs (Decidable (a ≠ b ∧ ((a, b) ∈ thetaWheelEdges ∨ (b, a) ∈ thetaWheelEdges)))

/-- `thetaWheel` has `23` edges. -/
lemma ncard_edgeSet_thetaWheel : thetaWheel.edgeSet.ncard = 23 := by
  rw [← coe_edgeFinset, Set.ncard_coe_finset]
  decide

/-- The neighbourhoods of the non-hub vertices of `thetaWheel`. -/
lemma thetaWheel_nbrs :
    (∀ x, thetaWheel.Adj 0 x → x ∈ ({1, 5, 7, 8} : Finset (Fin 9))) ∧
    (∀ x, thetaWheel.Adj 1 x → x ∈ ({0, 6, 7, 8} : Finset (Fin 9))) ∧
    (∀ x, thetaWheel.Adj 2 x → x ∈ ({3, 5, 7, 8} : Finset (Fin 9))) ∧
    (∀ x, thetaWheel.Adj 3 x → x ∈ ({2, 6, 7, 8} : Finset (Fin 9))) ∧
    (∀ x, thetaWheel.Adj 4 x → x ∈ ({5, 6, 7, 8} : Finset (Fin 9))) ∧
    (∀ x, thetaWheel.Adj 5 x → x = 0 ∨ x = 2 ∨ x = 4 ∨ x = 7 ∨ x = 8) ∧
    (∀ x, thetaWheel.Adj 6 x → x = 1 ∨ x = 3 ∨ x = 4 ∨ x = 7 ∨ x = 8) := by
  decide

/-- A symmetric neighbourhood function on `thetaWheel` in which every nonempty neighbourhood has
exactly four elements is empty everywhere. This is the case analysis on which of the five
degree-four vertices carry the union. -/
theorem thetaWheel_aux (N : Fin 9 → Finset (Fin 9))
    (hA : ∀ v w, w ∈ N v → thetaWheel.Adj v w) (hS : ∀ v w, w ∈ N v → v ∈ N w)
    (hC : ∀ v w, w ∈ N v → (N v).card = 4) (v w : Fin 9) : w ∉ N v := by
  obtain ⟨n0, n1, n2, n3, n4, n5, n6⟩ := thetaWheel_nbrs
  have full : ∀ v w (T : Finset (Fin 9)), N v ⊆ T → T.card ≤ 4 → w ∈ N v → N v = T :=
    fun v w T hT hc hw => eq_of_subset_of_card_le hT (hc.trans (hC v w hw).ge)
  have small : ∀ v w (T : Finset (Fin 9)), N v ⊆ T → T.card < 4 → w ∉ N v := by
    intro v w T hT hc hw
    have := card_le_card hT
    rw [hC v w hw] at this
    omega
  have big : ∀ v (T : Finset (Fin 9)), T ⊆ N v → 4 < T.card → False := by
    intro v T hT hc
    obtain ⟨w, hw⟩ : T.Nonempty := card_pos.1 (by omega)
    have := card_le_card hT
    rw [hC v w (hT hw)] at this
    omega
  -- vertex `0` (and with it its path partner `1`) carries no union edge
  have h0 : ∀ w, w ∉ N 0 := by
    intro w hw
    have e0 := full 0 w _ (fun x hx => n0 x (hA 0 x hx)) (by decide) hw
    have e1 := full 1 0 _ (fun x hx => n1 x (hA 1 x hx)) (by decide)
      (hS 0 1 (by rw [e0]; decide))
    have h50 : 0 ∈ N 5 := hS 0 5 (by rw [e0]; decide)
    have h61 : 1 ∈ N 6 := hS 1 6 (by rw [e1]; decide)
    have h70 : 0 ∈ N 7 := hS 0 7 (by rw [e0]; decide)
    have h71 : 1 ∈ N 7 := hS 1 7 (by rw [e1]; decide)
    have h80 : 0 ∈ N 8 := hS 0 8 (by rw [e0]; decide)
    have h81 : 1 ∈ N 8 := hS 1 8 (by rw [e1]; decide)
    by_cases hP2 : ∃ w, w ∈ N 2
    · obtain ⟨w2, hw2⟩ := hP2
      have e2 := full 2 w2 _ (fun x hx => n2 x (hA 2 x hx)) (by decide) hw2
      have e3 := full 3 2 _ (fun x hx => n3 x (hA 3 x hx)) (by decide)
        (hS 2 3 (by rw [e2]; decide))
      have h72 : 2 ∈ N 7 := hS 2 7 (by rw [e2]; decide)
      have h73 : 3 ∈ N 7 := hS 3 7 (by rw [e3]; decide)
      have h82 : 2 ∈ N 8 := hS 2 8 (by rw [e2]; decide)
      have h83 : 3 ∈ N 8 := hS 3 8 (by rw [e3]; decide)
      -- the hubs are saturated by `0, 1, 2, 3`, so `5` has at most two union neighbours
      refine small 5 0 {0, 2} ?_ (by decide) h50
      intro x hx
      rcases n5 x (hA 5 x hx) with rfl | rfl | rfl | rfl | rfl
      · decide
      · decide
      · have e4 := full 4 5 _ (fun x hx => n4 x (hA 4 x hx)) (by decide) (hS 5 4 hx)
        have h74 : 4 ∈ N 7 := hS 4 7 (by rw [e4]; decide)
        refine (big 7 {0, 1, 2, 3, 4} ?_ (by decide)).elim
        intro y hy
        simp only [mem_insert, mem_singleton] at hy
        rcases hy with rfl | rfl | rfl | rfl | rfl <;> assumption
      · have h75 : 5 ∈ N 7 := hS 5 7 hx
        refine (big 7 {0, 1, 2, 3, 5} ?_ (by decide)).elim
        intro y hy
        simp only [mem_insert, mem_singleton] at hy
        rcases hy with rfl | rfl | rfl | rfl | rfl <;> assumption
      · have h85 : 5 ∈ N 8 := hS 5 8 hx
        refine (big 8 {0, 1, 2, 3, 5} ?_ (by decide)).elim
        intro y hy
        simp only [mem_insert, mem_singleton] at hy
        rcases hy with rfl | rfl | rfl | rfl | rfl <;> assumption
    · push Not at hP2
      have hP3 : ∀ w, w ∉ N 3 := fun w hw =>
        hP2 3 (hS 3 2 (by rw [full 3 w _ (fun x hx => n3 x (hA 3 x hx)) (by decide) hw]; decide))
      by_cases hP4 : ∃ w, w ∈ N 4
      · obtain ⟨w4, hw4⟩ := hP4
        have e4 := full 4 w4 _ (fun x hx => n4 x (hA 4 x hx)) (by decide) hw4
        have h74 : 4 ∈ N 7 := hS 4 7 (by rw [e4]; decide)
        have e5 : N 5 = {0, 4, 7, 8} := by
          refine full 5 0 _ ?_ (by decide) h50
          intro x hx
          rcases n5 x (hA 5 x hx) with rfl | rfl | rfl | rfl | rfl
          · decide
          · exact absurd (hS 5 2 hx) (hP2 5)
          · decide
          · decide
          · decide
        have e6 : N 6 = {1, 4, 7, 8} := by
          refine full 6 1 _ ?_ (by decide) h61
          intro x hx
          rcases n6 x (hA 6 x hx) with rfl | rfl | rfl | rfl | rfl
          · decide
          · exact absurd (hS 6 3 hx) (hP3 6)
          · decide
          · decide
          · decide
        have h75 : 5 ∈ N 7 := hS 5 7 (by rw [e5]; decide)
        have h76 : 6 ∈ N 7 := hS 6 7 (by rw [e6]; decide)
        refine big 7 {0, 1, 4, 5, 6} ?_ (by decide)
        intro y hy
        simp only [mem_insert, mem_singleton] at hy
        rcases hy with rfl | rfl | rfl | rfl | rfl <;> assumption
      · push Not at hP4
        refine small 5 0 {0, 7, 8} ?_ (by decide) h50
        intro x hx
        rcases n5 x (hA 5 x hx) with rfl | rfl | rfl | rfl | rfl
        · decide
        · exact absurd (hS 5 2 hx) (hP2 5)
        · exact absurd (hS 5 4 hx) (hP4 5)
        · decide
        · decide
  have h1 : ∀ w, w ∉ N 1 := fun w hw =>
    h0 1 (hS 1 0 (by rw [full 1 w _ (fun x hx => n1 x (hA 1 x hx)) (by decide) hw]; decide))
  -- vertex `2` (and its partner `3`) carries no union edge
  have h2 : ∀ w, w ∉ N 2 := by
    intro w hw
    have e2 := full 2 w _ (fun x hx => n2 x (hA 2 x hx)) (by decide) hw
    have e3 := full 3 2 _ (fun x hx => n3 x (hA 3 x hx)) (by decide)
      (hS 2 3 (by rw [e2]; decide))
    have h52 : 2 ∈ N 5 := hS 2 5 (by rw [e2]; decide)
    have h63 : 3 ∈ N 6 := hS 3 6 (by rw [e3]; decide)
    have h72 : 2 ∈ N 7 := hS 2 7 (by rw [e2]; decide)
    have h73 : 3 ∈ N 7 := hS 3 7 (by rw [e3]; decide)
    by_cases hP4 : ∃ w, w ∈ N 4
    · obtain ⟨w4, hw4⟩ := hP4
      have e4 := full 4 w4 _ (fun x hx => n4 x (hA 4 x hx)) (by decide) hw4
      have h74 : 4 ∈ N 7 := hS 4 7 (by rw [e4]; decide)
      have e5 : N 5 = {2, 4, 7, 8} := by
        refine full 5 2 _ ?_ (by decide) h52
        intro x hx
        rcases n5 x (hA 5 x hx) with rfl | rfl | rfl | rfl | rfl
        · exact absurd (hS 5 0 hx) (h0 5)
        · decide
        · decide
        · decide
        · decide
      have e6 : N 6 = {3, 4, 7, 8} := by
        refine full 6 3 _ ?_ (by decide) h63
        intro x hx
        rcases n6 x (hA 6 x hx) with rfl | rfl | rfl | rfl | rfl
        · exact absurd (hS 6 1 hx) (h1 6)
        · decide
        · decide
        · decide
        · decide
      have h75 : 5 ∈ N 7 := hS 5 7 (by rw [e5]; decide)
      have h76 : 6 ∈ N 7 := hS 6 7 (by rw [e6]; decide)
      refine big 7 {2, 3, 4, 5, 6} ?_ (by decide)
      intro y hy
      simp only [mem_insert, mem_singleton] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl <;> assumption
    · push Not at hP4
      refine small 5 2 {2, 7, 8} ?_ (by decide) h52
      intro x hx
      rcases n5 x (hA 5 x hx) with rfl | rfl | rfl | rfl | rfl
      · exact absurd (hS 5 0 hx) (h0 5)
      · decide
      · exact absurd (hS 5 4 hx) (hP4 5)
      · decide
      · decide
  have h3 : ∀ w, w ∉ N 3 := fun w hw =>
    h2 3 (hS 3 2 (by rw [full 3 w _ (fun x hx => n3 x (hA 3 x hx)) (by decide) hw]; decide))
  -- vertex `4` carries no union edge: then `5` would have at most three union neighbours
  have h4 : ∀ w, w ∉ N 4 := by
    intro w hw
    have e4 := full 4 w _ (fun x hx => n4 x (hA 4 x hx)) (by decide) hw
    refine small 5 4 {4, 7, 8} ?_ (by decide) (hS 4 5 (by rw [e4]; decide))
    intro x hx
    rcases n5 x (hA 5 x hx) with rfl | rfl | rfl | rfl | rfl
    · exact absurd (hS 5 0 hx) (h0 5)
    · exact absurd (hS 5 2 hx) (h2 5)
    · decide
    · decide
    · decide
  -- the remaining vertices see at most two candidates
  have h5 : ∀ w, w ∉ N 5 := by
    intro w hw
    refine small 5 w {7, 8} ?_ (by decide) hw
    intro x hx
    rcases n5 x (hA 5 x hx) with rfl | rfl | rfl | rfl | rfl
    · exact absurd (hS 5 0 hx) (h0 5)
    · exact absurd (hS 5 2 hx) (h2 5)
    · exact absurd (hS 5 4 hx) (h4 5)
    · decide
    · decide
  have h6 : ∀ w, w ∉ N 6 := by
    intro w hw
    refine small 6 w {7, 8} ?_ (by decide) hw
    intro x hx
    rcases n6 x (hA 6 x hx) with rfl | rfl | rfl | rfl | rfl
    · exact absurd (hS 6 1 hx) (h1 6)
    · exact absurd (hS 6 3 hx) (h3 6)
    · exact absurd (hS 6 4 hx) (h4 6)
    · decide
    · decide
  have h7 : ∀ w, w ∉ N 7 := by
    intro w hw
    refine small 7 w {8} ?_ (by decide) hw
    intro x hx
    have hx7 := hA 7 x hx
    fin_cases x
    · exact absurd (hS 7 0 hx) (h0 7)
    · exact absurd (hS 7 1 hx) (h1 7)
    · exact absurd (hS 7 2 hx) (h2 7)
    · exact absurd (hS 7 3 hx) (h3 7)
    · exact absurd (hS 7 4 hx) (h4 7)
    · exact absurd (hS 7 5 hx) (h5 7)
    · exact absurd (hS 7 6 hx) (h6 7)
    · exact absurd hx7 (thetaWheel.loopless.irrefl 7)
    · decide
  have h8 : ∀ w, w ∉ N 8 := by
    intro w hw
    refine small 8 w ∅ ?_ (by decide) hw
    intro x hx
    have hx8 := hA 8 x hx
    fin_cases x
    · exact absurd (hS 8 0 hx) (h0 8)
    · exact absurd (hS 8 1 hx) (h1 8)
    · exact absurd (hS 8 2 hx) (h2 8)
    · exact absurd (hS 8 3 hx) (h3 8)
    · exact absurd (hS 8 4 hx) (h4 8)
    · exact absurd (hS 8 5 hx) (h5 8)
    · exact absurd (hS 8 6 hx) (h6 8)
    · exact absurd (hS 8 7 hx) (h7 8)
    · exact absurd hx8 (thetaWheel.loopless.irrefl 8)
  fin_cases v
  exacts [h0 w, h1 w, h2 w, h3 w, h4 w, h5 w, h6 w, h7 w, h8 w]

/-- `K₂ ∨ θ(2,3,3)` has no two edge-disjoint cycles with the same vertex set. -/
theorem theta_not_hasPair : ¬ HasPairF thetaWheel := by
  rintro ⟨u, w, p, q, hp, hq, hS, hE⟩
  have h4 := card_pairNbrs hp hq hS hE p.start_mem_support
  obtain ⟨x, hx⟩ : (pairNbrs p q u).Nonempty := card_pos.1 (by omega)
  exact thetaWheel_aux (pairNbrs p q) (fun _ _ h => adj_of_mem_pairNbrs h)
    (fun _ _ h => mem_pairNbrs_symm h)
    (fun _ _ h => card_pairNbrs hp hq hS hE (mem_support_of_mem_pairNbrs hS h)) u x hx

/-- `23 ∈ edgeCounts 9`, witnessed by `K₂ ∨ θ(2,3,3)`. -/
theorem twentythree_mem_edgeCounts_nine : 23 ∈ edgeCounts 9 :=
  ⟨thetaWheel, theta_not_hasPair, ncard_edgeSet_thetaWheel⟩

/-- `3 n - 4 ∈ edgeCounts n` for `n ≥ 9`, from `K₂ ∨ θ(2,3,3)` by repeated extension. -/
theorem three_mul_sub_four_mem (n : ℕ) (hn : 9 ≤ n) : 3 * n - 4 ∈ edgeCounts n := by
  induction n, hn using Nat.le_induction with
  | base => exact twentythree_mem_edgeCounts_nine
  | succ n hn ih =>
    have h : 3 * (n + 1) - 4 = 3 * n - 4 + 3 := by omega
    rw [h]
    exact mem_edgeCounts_succ (by omega) ih

end Theta

end Erdos585
