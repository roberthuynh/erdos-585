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
import Openmath.Proofs.MatchingJoinDefs

/-!
# Exact order and degree of every matching join of the quintic seed

The neighbor-finset proof follows the explicit insertion-and-image method in
`SignedPrismCore.prism_degree`, here with an arbitrary matching bijection.
-/

open SimpleGraph Finset

namespace Erdos585.MatchingJoin

private def mate (f : Equiv.Perm (Fin 32)) (x : Fin 32) (s : Bool) : Fin 32 :=
  if s then f.symm x else f x

private lemma neighborFinset_join (f : Equiv.Perm (Fin 32)) (x : Fin 32) (s : Bool) :
    (graph f).neighborFinset (x,s) =
      insert (mate f x s, !s) ((RegularFive.graph.neighborFinset x).image fun y => (y,s)) := by
  ext ⟨y,t⟩
  rw [mem_neighborFinset, mem_insert, mem_image]
  cases s <;> cases t <;>
    simp [graph, mate, mem_neighborFinset, Equiv.eq_symm_apply]
  exact eq_comm

/-- The actual neighbor set consists of five old neighbors and one opposite-copy mate. -/
theorem graph_degree (f : Equiv.Perm (Fin 32)) (x : Fin 32) (s : Bool) :
    (graph f).degree (x,s) = 6 := by
  have hi : Function.Injective (fun y : Fin 32 => (y,s)) := by
    intro y z h
    exact congrArg Prod.fst h
  have hn : (mate f x s, !s) ∉
      (RegularFive.graph.neighborFinset x).image (fun y => (y,s)) := by
    rintro h
    obtain ⟨y, hy, he⟩ := mem_image.mp h
    have hs := congrArg Prod.snd he
    cases s <;> simp at hs
  rw [← card_neighborFinset_eq_degree, neighborFinset_join,
    card_insert_of_notMem hn, card_image_of_injective _ hi,
    card_neighborFinset_eq_degree, RegularFive.graph_degree]

/-- Every unrestricted perfect-matching join of the two actual seeds is six-regular. -/
theorem graph_regular (f : Equiv.Perm (Fin 32)) : (graph f).IsRegularOfDegree 6 := by
  rintro ⟨x,s⟩
  exact graph_degree f x s

theorem vertex_count : Fintype.card (Fin 32 × Bool) = 64 := by decide

theorem graph_edge_count (f : Equiv.Perm (Fin 32)) : (graph f).edgeFinset.card = 192 := by
  have h := sum_degrees_eq_twice_card_edges (graph f)
  have hd : ∀ v : Fin 32 × Bool, (graph f).degree v = 6 := graph_regular f
  simp only [hd, sum_const, card_univ, vertex_count, smul_eq_mul] at h
  omega

end Erdos585.MatchingJoin
