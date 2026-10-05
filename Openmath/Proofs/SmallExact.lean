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
import Openmath.Proofs.Extension
import Openmath.Proofs.DoubleWheel
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Logic.Equiv.Fintype

/-!
# Exact values at six and seven vertices

The six-vertex obstruction is either a copy of K₅ or the octahedral graph.
Vertex deletion then gives the seven-vertex upper bound.
-/

open SimpleGraph Finset

namespace Erdos585

/-- An injective graph homomorphism preserves a forbidden pair. -/
theorem HasPairF.map {V W : Type*} [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} (h : HasPairF G)
    (f : G →g H) (hf : Function.Injective f) : HasPairF H := by
  obtain ⟨u, v, p, q, hp, hq, hS, hE⟩ := h
  exact ⟨f u, f v, p.map f, q.map f,
    (pair_map_iff f hf p q).2 ⟨hp, hq, hS, hE⟩⟩

/-- Every induced subgraph of a pair-free graph is pair-free. -/
theorem not_hasPairF_induce {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} (h : ¬ HasPairF G) (S : Set V) : ¬ HasPairF (G.induce S) :=
  fun hp => h (hp.map (Embedding.induce S).toHom (Embedding.induce (G := G) S).injective)

/-- Deleting a vertex removes exactly its degree many edges. -/
theorem card_edges_delete_vertex {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    (G.induce {v}ᶜ).edgeFinset.card = G.edgeFinset.card - G.degree v := by
  rw [card_edgeFinset_induce_compl_singleton, card_edgeFinset_deleteIncidenceSet]

/-- K₆ with the perfect matching 01, 23, 45 removed. -/
def octahedron : SimpleGraph (Fin 6) where
  Adj a b := a.val / 2 ≠ b.val / 2
  symm := ⟨fun _ _ => Ne.symm⟩
  loopless := ⟨fun _ => not_not_intro rfl⟩

instance : DecidableRel octahedron.Adj := fun _ _ => inferInstanceAs (Decidable (_ ≠ _))

/-- The first Hamiltonian cycle in the octahedron. -/
def octA : octahedron.Walk 0 0 :=
  .cons (v := 2) (by decide) (.cons (v := 1) (by decide) (.cons (v := 4) (by decide)
    (.cons (v := 3) (by decide) (.cons (v := 5) (by decide) (.cons (by decide) .nil)))))

/-- The second Hamiltonian cycle in the octahedron. -/
def octB : octahedron.Walk 0 0 :=
  .cons (v := 3) (by decide) (.cons (v := 1) (by decide) (.cons (v := 5) (by decide)
    (.cons (v := 2) (by decide) (.cons (v := 4) (by decide) (.cons (by decide) .nil)))))

lemma octA_isCycle : octA.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  exact ⟨by decide, by simp [octA], by decide⟩

lemma octB_isCycle : octB.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  exact ⟨by decide, by simp [octB], by decide⟩

lemma hasPair_octahedron : HasPairF octahedron :=
  ⟨0, 0, octA, octB, octA_isCycle, octB_isCycle, by decide, by decide⟩

/-- A graph complete away from one vertex on six vertices contains K₅. -/
lemma hasPair_of_complete_off_vertex (G : SimpleGraph (Fin 6)) (a : Fin 6)
    (h : ∀ u v, u ≠ v → u ≠ a → v ≠ a → G.Adj u v) : HasPairF G := by
  classical
  have hc : Fintype.card ({a}ᶜ : Set (Fin 6)) = 5 := by
    rw [Fintype.card_compl_set, Fintype.card_fin, Fintype.card_unique]
  let e : Fin 5 ≃ ({a}ᶜ : Set (Fin 6)) := (Fintype.equivFinOfCardEq hc).symm
  let f : K5 →g G := {
    toFun := fun x => (e x).val
    map_rel' := by
      intro x y hxy
      exact h _ _ (fun he => (show x ≠ y from hxy)
        (e.injective (Subtype.ext he))) (e x).property (e y).property }
  exact hasPair_top_five.map f (Subtype.val_injective.comp e.injective)

lemma hasPair_of_two_missing_disjoint (G : SimpleGraph (Fin 6))
    (a b c d : Fin 6) (hab : a ≠ b) (hcd : c ≠ d)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (h : ∀ u v, u ≠ v → s(u,v) ≠ s(a,b) → s(u,v) ≠ s(c,d) → G.Adj u v) :
    HasPairF G := by
  let g : Fin 4 → Fin 6 := ![a, b, c, d]
  have hg : Function.Injective g := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [g]
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair
    (fun i : Fin 4 => i.castLE (by decide) : Fin 4 → Fin 6) g
    (Fin.castLE_injective (by decide)) hg
  have hs0 : σ 0 = a := hσ 0
  have hs1 : σ 1 = b := hσ 1
  have hs2 : σ 2 = c := hσ 2
  have hs3 : σ 3 = d := hσ 3
  have ho : ∀ x y : Fin 6, octahedron.Adj x y →
      x ≠ y ∧ s(x,y) ≠ s(0,1) ∧ s(x,y) ≠ s(2,3) := by decide
  let f : octahedron →g G := {
    toFun := σ
    map_rel' := by
      intro x y hxy
      obtain ⟨hne, h01, h23⟩ := ho x y hxy
      apply h _ _ (σ.injective.ne hne)
      · rw [← hs0, ← hs1]
        exact (Sym2.map.injective σ.injective).ne h01
      · rw [← hs2, ← hs3]
        exact (Sym2.map.injective σ.injective).ne h23 }
  exact hasPair_octahedron.map f σ.injective

/-- Thirteen edges on six vertices force a forbidden pair. -/
theorem hasPair_six_of_thirteen (G : SimpleGraph (Fin 6))
    (hG : 13 ≤ G.edgeSet.ncard) : HasPairF G := by
  classical
  let T := (⊤ : SimpleGraph (Fin 6)).edgeFinset
  have hsub : G.edgeFinset ⊆ T := edgeFinset_mono le_top
  have ht : T.card = 15 := by
    change (⊤ : SimpleGraph (Fin 6)).edgeFinset.card = 15
    rw [card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin]
    decide
  have hm : (T \ G.edgeFinset).card ≤ 2 := by
    rw [card_sdiff_of_subset hsub, ht]
    rw [← coe_edgeFinset, Set.ncard_coe_finset] at hG
    omega
  obtain ⟨S, hMS, hST, hS⟩ := exists_subsuperset_card_eq
    (sdiff_subset : T \ G.edgeFinset ⊆ T) hm (by omega : 2 ≤ T.card)
  obtain ⟨e, f, hef, rfl⟩ := card_eq_two.mp hS
  induction e using Sym2.inductionOn with | _ a b => ?_
  induction f using Sym2.inductionOn with | _ c d => ?_
  have hab : a ≠ b := by
    simpa [T] using hST (show s(a,b) ∈ {s(a,b), s(c,d)} by simp)
  have hcd : c ≠ d := by
    simpa [T] using hST (show s(c,d) ∈ {s(a,b), s(c,d)} by simp)
  have h : ∀ u v, u ≠ v → s(u,v) ≠ s(a,b) → s(u,v) ≠ s(c,d) → G.Adj u v := by
    intro u v huv he hf
    by_contra hn
    have hx : s(u,v) ∈ T \ G.edgeFinset := by simp [T, huv, hn]
    simpa [he, hf] using hMS hx
  by_cases hac : a = c
  · subst c
    apply hasPair_of_complete_off_vertex G a
    intro u v huv hua hva
    apply h u v huv <;> simp_all
  by_cases had : a = d
  · subst d
    apply hasPair_of_complete_off_vertex G a
    intro u v huv hua hva
    apply h u v huv <;> simp_all
  by_cases hbc : b = c
  · subst c
    apply hasPair_of_complete_off_vertex G b
    intro u v huv hua hva
    apply h u v huv <;> simp_all
  by_cases hbd : b = d
  · subst d
    apply hasPair_of_complete_off_vertex G b
    intro u v huv hua hva
    apply h u v huv <;> simp_all
  exact hasPair_of_two_missing_disjoint G a b c d hab hcd hac had hbc hbd h

/-- The lower construction and the two obstruction cases give the exact six-vertex value. -/
theorem six : IsGreatest (edgeCounts 6) 12 := by
  refine ⟨three_mul_sub_six_mem 6 (by decide), ?_⟩
  rintro m ⟨G, hG, rfl⟩
  by_contra hn
  exact hG (hasPair_six_of_thirteen G (by omega))

/-- A pair-free graph on any finite vertex type is bounded by the extremal function. -/
theorem card_edges_le_maxEdges {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : ¬ HasPairF G)
    {n : ℕ} (hc : Fintype.card V = n) : G.edgeFinset.card ≤ maxEdges n := by
  classical
  let e : Fin n ≃ V := (Fintype.equivFinOfCardEq hc).symm
  let H := G.comap e
  have hi : H ≃g G := Iso.comap e G
  have hh : ¬ HasPairF H := fun hp => hG (hp.map hi.toHom hi.injective)
  have he : H.edgeSet.ncard = G.edgeFinset.card := by
    rw [← coe_edgeFinset, Set.ncard_coe_finset, hi.card_edgeFinset_eq]
  exact le_maxEdges_of_mem ⟨H, hh, he⟩

/-- Every vertex deletion of a pair-free graph is bounded by the preceding extremal value. -/
theorem delete_vertex_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : ¬ HasPairF G)
    {n : ℕ} (hc : Fintype.card V = n + 1) (v : V) :
    G.edgeFinset.card ≤ maxEdges n + G.degree v := by
  classical
  have hcard : Fintype.card ({v}ᶜ : Set V) = n := by
    rw [Fintype.card_compl_set, hc, Fintype.card_unique]
    omega
  have h := card_edges_le_maxEdges (G.induce {v}ᶜ) (not_hasPairF_induce hG _) hcard
  rw [card_edges_delete_vertex] at h
  omega

/-- Summing the seven deletion bounds gives 5|E| ≤ 84, hence at most sixteen edges. -/
theorem edgeCounts_seven_upper : ∀ m ∈ edgeCounts 7, m ≤ 16 := by
  rintro m ⟨G, hG, rfl⟩
  classical
  have hd : ∀ v : Fin 7, G.edgeFinset.card ≤ 12 + G.degree v := by
    intro v
    simpa only [maxEdges_eq_of_isGreatest six] using
      delete_vertex_bound G hG (show Fintype.card (Fin 7) = 6 + 1 from rfl) v
  have hs := Finset.sum_le_sum (s := (univ : Finset (Fin 7))) (fun v _ => hd v)
  simp only [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, smul_eq_mul,
    G.sum_degrees_eq_twice_card_edges] at hs
  rw [← coe_edgeFinset, Set.ncard_coe_finset]
  omega

/-- The double wheel attains the seven-vertex upper bound. -/
theorem seven : IsGreatest (edgeCounts 7) 16 :=
  ⟨three_mul_sub_five_mem_edgeCounts 7 (by decide), edgeCounts_seven_upper⟩

end Erdos585
