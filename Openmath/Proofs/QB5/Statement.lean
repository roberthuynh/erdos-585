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
import Openmath.Proofs.QB5.Main

/-!
# QB(5) for Mathlib's `SimpleGraph`

QB(5) is this project's working label for the statement of `Erdos585.qb5`; it is not a name from
the literature. It says that every finite simple bipartite graph with maximum degree at most 6,
`n ≥ 3` vertices and at least `3n - 5` edges contains a nonempty 4-regular subgraph.

* `Erdos585.qb5` has the hypotheses and the conclusion of `Erdos585.qb4`, with `2 ≤ n` replaced
  by `3 ≤ n` and the slack `+ 4` replaced by `+ 5`. In `ℕ`, `3 * n ≤ e + 5` is exactly
  `e ≥ 3n - 5`. The proof is the proof of `qb4` with `quartic_of_dense5` (`Main.lean`) in place
  of `quartic_of_dense`, through the bridge from pairs of vertex sets to `SimpleGraph` in the QB4
  file `Statement.lean` (`exists_sides`, `dg_le_maxDegree`, `ec_eq_ncard`,
  `exists_subgraph_of_quartic`).
* The example after it shows that `3 ≤ n` cannot be dropped: `K_2` satisfies every other
  hypothesis and has no nonempty 4-regular subgraph.
-/

namespace Erdos585

open Finset SimpleGraph QB4 QB5

open scoped Classical in
/-- **QB(5)**: a bipartite graph with maximum degree at most six, `n ≥ 3` vertices and at least
`3n - 5` edges has a nonempty 4-regular subgraph. -/
theorem qb5 {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hbip : G.IsBipartite) (hdeg : G.maxDegree ≤ 6) (hn : 3 ≤ Fintype.card V)
    (he : 3 * Fintype.card V ≤ G.edgeSet.ncard + 5) :
    ∃ H : G.Subgraph, H.verts.Nonempty ∧ H.coe.IsRegularOfDegree 4 := by
  obtain ⟨o⟩ : Nonempty V := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨U, W, -, hUW, hcov, hbw⟩ := exists_sides hbip o
  have hcard : #U + #W = Fintype.card V := by
    rw [← card_union_of_disjoint hUW, hcov, card_univ]
  have hec := ec_eq_ncard hbw
  have hq : Quartic G U W :=
    quartic_of_dense5 (fun u _ => (dg_le_maxDegree W u).trans hdeg)
      (fun w _ => (dg_le_maxDegree U w).trans hdeg) (by omega) (by omega)
  obtain ⟨H, hne, -, h4⟩ := exists_subgraph_of_quartic hUW hq
  refine ⟨H, hne, fun v => ?_⟩
  rw [Subgraph.coe_degree]
  exact h4 v v.2

open scoped Classical in
/-- **`3 ≤ n` cannot be dropped.** The complete graph `K_2` on `Fin 2` satisfies every hypothesis
of `qb5` except `hn`: it is bipartite, its maximum degree is `1 ≤ 6`, and its `n = 2` vertices and
one edge meet `3n ≤ e + 5`. It has no nonempty 4-regular subgraph, since a vertex of a subgraph of
`K_2` has at most one neighbor. -/
example : (⊤ : SimpleGraph (Fin 2)).IsBipartite ∧ (⊤ : SimpleGraph (Fin 2)).maxDegree ≤ 6 ∧
    3 * Fintype.card (Fin 2) ≤ (⊤ : SimpleGraph (Fin 2)).edgeSet.ncard + 5 ∧
    ¬ ∃ H : (⊤ : SimpleGraph (Fin 2)).Subgraph, H.verts.Nonempty ∧
      H.coe.IsRegularOfDegree 4 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := (⊤ : SimpleGraph (Fin 2)).colorable_of_fintype
    rwa [Fintype.card_fin] at h
  · have h := (⊤ : SimpleGraph (Fin 2)).maxDegree_lt_card_verts
    rw [Fintype.card_fin] at h
    omega
  · have h : 0 < (⊤ : SimpleGraph (Fin 2)).edgeSet.ncard :=
      (Set.ncard_pos (Set.toFinite _)).2 ⟨s(0, 1), by simp⟩
    simp only [Fintype.card_fin]
    omega
  · rintro ⟨H, ⟨v, hv⟩, hreg⟩
    have hlt : H.coe.degree ⟨v, hv⟩ < Fintype.card H.verts := by
      convert H.coe.degree_lt_card_verts ⟨v, hv⟩
    have h4 : H.coe.degree ⟨v, hv⟩ = 4 := by convert hreg ⟨v, hv⟩
    have hcard : Fintype.card H.verts ≤ 2 := by
      simpa using Fintype.card_le_of_injective (Subtype.val : H.verts → Fin 2)
        Subtype.val_injective
    omega

end Erdos585
