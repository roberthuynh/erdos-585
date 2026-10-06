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
import Openmath.Proofs.QB4.Main

/-!
# QB(4) and a vertex-deleted form, for Mathlib's `SimpleGraph`

The two headline statements, transferred from pairs of vertex sets to Mathlib's `SimpleGraph`. QB(4)
is this project's working label for the statement of `Erdos585.qb4`; it is not a name from the
literature. Whether the same bound holds for graphs that are not bipartite is not proved here. For a
6-regular bipartite graph the conclusion is classical: by König's theorem the graph is a union of
six perfect matchings, and any four of them form a 4-regular subgraph. From `3n - 2` edges on, it
also follows from Alon, Friedland and Kalai (J. Combin. Theory Ser. B 37 (1984), Remark 3.6): a
bipartite graph with more than `3(n - 1)` edges has a subgraph with at least one edge in which every
degree is divisible by four, and when the maximum degree is at most seven its edges and their ends
form a 4-regular subgraph. The content is the case of `3n - 4` and `3n - 3` edges. C1 and E4 are the
instance classes of `Reductions.lean`.

* `Erdos585.qb4`: a bipartite graph with maximum degree at most six, `n ≥ 2`
  vertices and at least `3n - 4` edges has a nonempty 4-regular subgraph.
* `Erdos585.exists_four_regular_avoiding_of_bipartite_six_regular`: for a bipartite 6-regular
  graph `B` and a vertex `o`, `B - o` has a nonempty 4-regular subgraph, that is, `B` has one
  avoiding `o`.

The bridge from pairs of vertex sets to `SimpleGraph`:

* `exists_sides`: the two color classes of a 2-coloring, as disjoint finsets covering `V`.
* `dg_eq_degree`, `dg_le_maxDegree`, `ec_eq_ncard`: on the sides of a bipartition, the degree
  into the other side is the degree, and `e(U, W)` is the number of edges.
* `pairSubgraph`, `exists_subgraph_of_quartic`: a quartic subgraph of a pair of disjoint sets is a
  nonempty subgraph of `G` in which every vertex has degree four.
-/

open Finset SimpleGraph

namespace Erdos585.QB4

variable {V : Type*} {G : SimpleGraph V}

/-! ### From a set of adjacent pairs to a subgraph -/

/-- The subgraph of `G` formed by a set `F` of adjacent pairs: its vertices are the entries of the
pairs, and its edges are the pairs. -/
def pairSubgraph (F : Finset (V × V)) (hF : ∀ x ∈ F, G.Adj x.1 x.2) : G.Subgraph where
  verts := {v | ∃ x ∈ F, x.1 = v ∨ x.2 = v}
  Adj a b := ∃ x ∈ F, (x.1 = a ∧ x.2 = b) ∨ (x.1 = b ∧ x.2 = a)
  adj_sub := by
    rintro a b ⟨x, hx, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact hF x hx
    · exact (hF x hx).symm
  edge_vert := by
    rintro a b ⟨x, hx, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact ⟨x, hx, Or.inl rfl⟩
    · exact ⟨x, hx, Or.inr rfl⟩
  symm := ⟨by
    rintro a b ⟨x, hx, hab | hab⟩
    · exact ⟨x, hx, Or.inr hab⟩
    · exact ⟨x, hx, Or.inl hab⟩⟩

lemma pairSubgraph_adj {F : Finset (V × V)} {hF : ∀ x ∈ F, G.Adj x.1 x.2} {a b : V} :
    (pairSubgraph F hF).Adj a b ↔ ∃ x ∈ F, (x.1 = a ∧ x.2 = b) ∨ (x.1 = b ∧ x.2 = a) :=
  Iff.rfl

lemma mem_pairSubgraph_verts {F : Finset (V × V)} {hF : ∀ x ∈ F, G.Adj x.1 x.2} {v : V} :
    v ∈ (pairSubgraph F hF).verts ↔ ∃ x ∈ F, x.1 = v ∨ x.2 = v :=
  Iff.rfl

variable [DecidableEq V]

/-- If no pair of `F` has second entry `v`, the neighbors of `v` in `pairSubgraph F` are the
second entries of the pairs with first entry `v`. -/
lemma neighborSet_pairSubgraph_left {W : Finset V} {F : Finset (V × V)}
    (hF : ∀ x ∈ F, G.Adj x.1 x.2) (hFW : ∀ x ∈ F, x.2 ∈ W) {v : V} (hv : v ∉ W) :
    (pairSubgraph F hF).neighborSet v = ↑((F.filter fun x => x.1 = v).image Prod.snd) := by
  ext b
  rw [Subgraph.mem_neighborSet, pairSubgraph_adj, coe_image, coe_filter]
  constructor
  · rintro ⟨x, hx, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
    · exact ⟨x, ⟨hx, h1⟩, h2⟩
    · exact (hv (h2 ▸ hFW x hx)).elim
  · rintro ⟨x, ⟨hx, h1⟩, h2⟩
    exact ⟨x, hx, Or.inl ⟨h1, h2⟩⟩

/-- If no pair of `F` has first entry `v`, the neighbors of `v` in `pairSubgraph F` are the
first entries of the pairs with second entry `v`. -/
lemma neighborSet_pairSubgraph_right {U : Finset V} {F : Finset (V × V)}
    (hF : ∀ x ∈ F, G.Adj x.1 x.2) (hFU : ∀ x ∈ F, x.1 ∈ U) {v : V} (hv : v ∉ U) :
    (pairSubgraph F hF).neighborSet v = ↑((F.filter fun x => x.2 = v).image Prod.fst) := by
  ext b
  rw [Subgraph.mem_neighborSet, pairSubgraph_adj, coe_image, coe_filter]
  constructor
  · rintro ⟨x, hx, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
    · exact (hv (h1 ▸ hFU x hx)).elim
    · exact ⟨x, ⟨hx, h2⟩, h1⟩
  · rintro ⟨x, ⟨hx, h1⟩, h2⟩
    exact ⟨x, hx, Or.inr ⟨h2, h1⟩⟩

/-- The degree of a vertex `v` that is never a second entry: the number of pairs with first
entry `v`. -/
lemma degree_pairSubgraph_left {W : Finset V} {F : Finset (V × V)}
    (hF : ∀ x ∈ F, G.Adj x.1 x.2) (hFW : ∀ x ∈ F, x.2 ∈ W) {v : V} (hv : v ∉ W)
    [Fintype ((pairSubgraph F hF).neighborSet v)] :
    (pairSubgraph F hF).degree v = #{x ∈ F | x.1 = v} := by
  rw [Subgraph.degree, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq,
    neighborSet_pairSubgraph_left hF hFW hv, Set.ncard_coe_finset]
  refine card_image_of_injOn fun x hx y hy hxy => ?_
  rw [mem_coe, mem_filter] at hx hy
  exact Prod.ext (hx.2.trans hy.2.symm) hxy

/-- The degree of a vertex `v` that is never a first entry: the number of pairs with second
entry `v`. -/
lemma degree_pairSubgraph_right {U : Finset V} {F : Finset (V × V)}
    (hF : ∀ x ∈ F, G.Adj x.1 x.2) (hFU : ∀ x ∈ F, x.1 ∈ U) {v : V} (hv : v ∉ U)
    [Fintype ((pairSubgraph F hF).neighborSet v)] :
    (pairSubgraph F hF).degree v = #{x ∈ F | x.2 = v} := by
  rw [Subgraph.degree, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq,
    neighborSet_pairSubgraph_right hF hFU hv, Set.ncard_coe_finset]
  refine card_image_of_injOn fun x hx y hy hxy => ?_
  rw [mem_coe, mem_filter] at hx hy
  exact Prod.ext hxy (hx.2.trans hy.2.symm)

/-- **From pairs to subgraphs.** A quartic subgraph of a pair `(U, W)` of disjoint sets is a
nonempty subgraph `H` of `G`, with all its vertices in `U ∪ W`, in which every vertex has degree
four. -/
theorem exists_subgraph_of_quartic {U W : Finset V} (hUW : Disjoint U W) (h : Quartic G U W) :
    ∃ H : G.Subgraph, H.verts.Nonempty ∧ H.verts ⊆ ↑(U ∪ W) ∧
      ∀ v ∈ H.verts, ∀ [Fintype (H.neighborSet v)], H.degree v = 4 := by
  obtain ⟨F, hne, hFUW, hadj, h1, h2⟩ := h
  have hFU : ∀ x ∈ F, x.1 ∈ U := fun x hx => (mem_product.1 (hFUW hx)).1
  have hFW : ∀ x ∈ F, x.2 ∈ W := fun x hx => (mem_product.1 (hFUW hx)).2
  refine ⟨pairSubgraph F hadj, ?_, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := hne
    exact ⟨x.1, x, hx, Or.inl rfl⟩
  · rintro v ⟨x, hx, rfl | rfl⟩
    · exact mem_coe.2 (mem_union_left _ (hFU x hx))
    · exact mem_coe.2 (mem_union_right _ (hFW x hx))
  · rintro v ⟨x, hx, rfl | rfl⟩ _
    · rw [degree_pairSubgraph_left hadj hFW (disjoint_left.1 hUW (hFU x hx))]
      exact (h1 x.1).resolve_left (card_ne_zero.2 ⟨x, mem_filter.2 ⟨hx, rfl⟩⟩)
    · rw [degree_pairSubgraph_right hadj hFU (disjoint_right.1 hUW (hFW x hx))]
      exact (h2 x.2).resolve_left (card_ne_zero.2 ⟨x, mem_filter.2 ⟨hx, rfl⟩⟩)

/-! ### Bipartitions -/

/-- The two color classes of a 2-coloring of `G`, with `o` in the first: disjoint finsets that
cover `V`, with every edge between them. -/
lemma exists_sides [Fintype V] (hbip : G.IsBipartite) (o : V) :
    ∃ U W : Finset V, o ∈ U ∧ Disjoint U W ∧ U ∪ W = univ ∧ G.IsBipartiteWith ↑U ↑W := by
  obtain ⟨c⟩ := hbip
  have key : ∀ x y z : Fin 2, x ≠ y → (x = z ∧ y ≠ z) ∨ (x ≠ z ∧ y = z) := by decide
  refine ⟨univ.filter fun v => c v = c o, univ.filter fun v => c v ≠ c o, by simp,
    disjoint_filter_filter_not _ _ _, ?_, ⟨?_, fun a b hab => ?_⟩⟩
  · ext v
    simp only [mem_union, mem_filter, mem_univ, true_and, iff_true]
    exact em _
  · rw [disjoint_coe]
    exact disjoint_filter_filter_not _ _ _
  · simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq]
    exact key _ _ _ (c.valid hab)

variable [DecidableRel G.Adj]

omit [DecidableEq V] in
/-- On a side of a bipartition, the degree into the other side is the degree. -/
lemma dg_eq_degree {U W : Finset V} (h : G.IsBipartiteWith ↑U ↑W) {u : V} (hu : u ∈ U)
    [Fintype (G.neighborSet u)] : dg G W u = G.degree u := by
  rw [← card_neighborFinset_eq_degree, isBipartiteWith_neighborFinset h hu]
  rfl

omit [DecidableEq V] in
/-- A degree into a set is at most the maximum degree. -/
lemma dg_le_maxDegree [Fintype V] (S : Finset V) (v : V) : dg G S v ≤ G.maxDegree := by
  refine le_trans ?_ (G.degree_le_maxDegree v)
  rw [← card_neighborFinset_eq_degree]
  exact card_le_card fun w hw => by simpa using (mem_filter.1 hw).2

omit [DecidableEq V] in
/-- On the sides of a bipartition, `e(U, W)` is the number of edges. -/
lemma ec_eq_ncard [Fintype V] {U W : Finset V} (h : G.IsBipartiteWith ↑U ↑W) :
    ec G U W = G.edgeSet.ncard := by
  have h1 := isBipartiteWith_sum_degrees_eq_card_edges h
  have h2 := Set.ncard_eq_toFinset_card' G.edgeSet
  have h3 : ec G U W = ∑ u ∈ U, G.degree u := sum_congr rfl fun u hu => dg_eq_degree h hu
  rw [h3, h1, h2]
  rfl

end Erdos585.QB4

namespace Erdos585

open Finset SimpleGraph QB4

open scoped Classical in
/-- **QB(4)**: a bipartite graph with maximum degree at most six,
`n ≥ 2` vertices and at least `3n - 4` edges has a nonempty 4-regular subgraph. -/
theorem qb4 {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hbip : G.IsBipartite) (hdeg : G.maxDegree ≤ 6) (hn : 2 ≤ Fintype.card V)
    (he : 3 * Fintype.card V ≤ G.edgeSet.ncard + 4) :
    ∃ H : G.Subgraph, H.verts.Nonempty ∧ H.coe.IsRegularOfDegree 4 := by
  obtain ⟨o⟩ : Nonempty V := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨U, W, -, hUW, hcov, hbw⟩ := exists_sides hbip o
  have hcard : #U + #W = Fintype.card V := by
    rw [← card_union_of_disjoint hUW, hcov, card_univ]
  have hec := ec_eq_ncard hbw
  have hq : Quartic G U W :=
    quartic_of_dense (fun u _ => (dg_le_maxDegree W u).trans hdeg)
      (fun w _ => (dg_le_maxDegree U w).trans hdeg) (by omega) (by omega)
  obtain ⟨H, hne, -, h4⟩ := exists_subgraph_of_quartic hUW hq
  refine ⟨H, hne, fun v => ?_⟩
  rw [Subgraph.coe_degree]
  exact h4 v v.2

open scoped Classical in
/-- **A vertex-deleted form**: for a bipartite 6-regular graph `B` and any vertex
`o`, the graph `B - o` has a nonempty 4-regular subgraph, stated as a nonempty 4-regular subgraph
of `B` avoiding `o`. -/
theorem exists_four_regular_avoiding_of_bipartite_six_regular {V : Type*} [Fintype V]
    (B : SimpleGraph V) [DecidableRel B.Adj] (hbip : B.IsBipartite) (hreg : B.IsRegularOfDegree 6)
    (o : V) :
    ∃ H : B.Subgraph, H.verts.Nonempty ∧ o ∉ H.verts ∧ H.coe.IsRegularOfDegree 4 := by
  obtain ⟨U, W, hoU, hUW, -, hbw⟩ := exists_sides hbip o
  have hdU : ∀ u ∈ U, dg B W u = 6 := fun u hu => (dg_eq_degree hbw hu).trans (hreg u)
  have hdW : ∀ w ∈ W, dg B U w = 6 := fun w hw => (dg_eq_degree hbw.symm hw).trans (hreg w)
  -- the sides have equal size, `6 |U| = e(U, W) = e(W, U) = 6 |W|`
  have hcU : ec B U W = 6 * #U := by
    unfold ec
    rw [sum_congr rfl hdU, sum_const, smul_eq_mul, mul_comm]
  have hcW : ec B W U = 6 * #W := by
    unfold ec
    rw [sum_congr rfl hdW, sum_const, smul_eq_mul, mul_comm]
  have hcomm := ec_comm (G := B) U W
  -- `W` contains the six neighbors of `o`
  have hW6 : 6 ≤ #W := by
    rw [← hdU o hoU]
    exact dg_le_card W o
  have hcUo := card_erase_of_mem hoU
  -- `(U - o, W)` is a C1 instance of size `|U| - 1 ≥ 5`, with deficiency `D_U = 0`
  have hC1 : IsC1 B (U.erase o) W (#U - 1) :=
    { pos := by omega
      cardU := hcUo
      cardW := by omega
      degU := fun u hu => (hdU u (mem_of_mem_erase hu)).le
      degW := fun w hw => (dg_mono (erase_subset o U) w).trans (hdW w hw).le
      defU := by
        have h0 : df B W (U.erase o) = 0 := sum_eq_zero fun u hu => by
          rw [hdU u (mem_of_mem_erase hu)]
          norm_num
        rw [h0]
        norm_num }
  obtain ⟨H, hne, hsub, h4⟩ :=
    exists_subgraph_of_quartic (disjoint_of_subset_left (erase_subset o U) hUW)
      (quartic_of_isC1 hC1)
  refine ⟨H, hne, fun ho => ?_, fun v => ?_⟩
  · rcases mem_union.1 (mem_coe.1 (hsub ho)) with h | h
    · exact notMem_erase o U h
    · exact disjoint_left.1 hUW hoU h
  · rw [Subgraph.coe_degree]
    exact h4 v v.2

end Erdos585
