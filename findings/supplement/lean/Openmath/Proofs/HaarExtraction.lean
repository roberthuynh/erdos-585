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
import Openmath.Proofs.HaarSixCycle
import Openmath.Proofs.Wenger

/-! # A boundary for unconditional exact abelian-Haar extraction

The known Wenger family has degree q, order 2q³, and q⁴ edges, but
contains no injective copy of any abelian Haar graph with three colors.
The complete written proof and primary-source comparison preceded this
file in Paper85/HAAR-EXTRACTION-BOUNDARY.md. This does not assert that
these graphs avoid the Erdős 585 pattern. In fact, for sufficiently
large q the published polylogarithmic theorem implies they contain it.
-/

namespace Erdos585.HaarExtraction
open SimpleGraph Finset

variable {V K : Type*} [AddCommGroup V] [Field K]

/-- No shore-preserving condition is imposed on the hypothetical embedding. -/
theorem no_embedding (S : Finset V) (hcard : 3 ≤ S.card)
    (f : Haar.graph S →g Wenger.graph (K := K)) : ¬ Function.Injective f := by
  classical
  intro hf
  obtain ⟨g, hg⟩ := Function.Embedding.exists_of_card_le_finset
    (α := Fin 3) (by simpa using hcard)
  have hm : ∀ i, g i ∈ S := fun i => hg ⟨i, rfl⟩
  let s := g 0
  let t := g 1
  let u := g 2
  have hp := HaarSixCycle.cycle_isCycle S s t u (hm 0) (hm 1) (hm 2)
    (g.injective.ne (by decide)) (g.injective.ne (by decide))
    (g.injective.ne (by decide))
  apply Wenger.no_six_cycle (f (0, false)) (f (s, true))
    (f (s-t, false)) (f (s-t+u, true)) (f (u-t, false)) (f (u, true))
  · simpa [HaarSixCycle.cycle] using hp.nodup_dropLast_support.map hf
  · apply f.map_rel'
    simpa using hm 0
  · apply f.map_rel'
    apply Adj.symm
    rw [Haar.graph_cross]
    simpa using hm 1
  · apply f.map_rel'
    rw [Haar.graph_cross]
    simpa using hm 2
  · apply f.map_rel'
    apply Adj.symm
    rw [Haar.graph_cross]
    have he : s-t+u-(u-t) = s := by abel
    simpa only [he] using hm 0
  · apply f.map_rel'
    rw [Haar.graph_cross]
    simpa using hm 1
  · apply f.map_rel'
    apply Adj.symm
    rw [Haar.graph_cross]
    simpa using hm 2

/-- An actual finite regular bipartite family, with exact counts and the
extraction obstruction, rather than a host postulated to have large girth. -/
theorem family_boundary [Fintype K] [DecidableEq K] :
    (Wenger.graph (K := K)).IsBipartite ∧
    Fintype.card (Wenger.Vertex K) = 2 * Fintype.card K ^ 3 ∧
    (∀ x : Wenger.Vertex K, Wenger.graph.degree x = Fintype.card K) ∧
    (Wenger.graph (K := K)).edgeFinset.card = Fintype.card K ^ 4 ∧
    (∀ (S : Finset V), 3 ≤ S.card →
      ∀ f : Haar.graph S →g Wenger.graph (K := K), ¬ Function.Injective f) := by
  exact ⟨Wenger.graph_bipartite, Wenger.card_vertex, Wenger.degree_eq,
    Wenger.card_edges, no_embedding⟩

end Erdos585.HaarExtraction
