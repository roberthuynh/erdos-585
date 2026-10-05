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
import Openmath.Proofs.SmallExact

/-!
# Small edge cuts confine forbidden pairs

A cycle crossing a cut uses at least two distinct cut edges. Consequently,
two edge-disjoint cycles with equal support cannot cross a cut of size at most three.
-/

open SimpleGraph Finset

namespace Erdos585

section Cut

variable {V C : Type*} [DecidableEq V] {G : SimpleGraph V}
    (color : V → C) (cut : Finset (Sym2 V))
    (hcut : ∀ a b, G.Adj a b → color a ≠ color b → s(a, b) ∈ cut)

include hcut

omit [DecidableEq V] in
lemma exists_cut_edge_of_walk {a b : V} (p : G.Walk a b) (h : color a ≠ color b) :
    ∃ e, e ∈ p.edges ∧ e ∈ cut := by
  induction p with
  | nil => exact False.elim (h rfl)
  | @cons a b z hab p ih =>
    by_cases hc : color a = color b
    · obtain ⟨e, he, hf⟩ := ih (fun h' => h (hc.trans h'))
      exact ⟨e, by simp only [Walk.edges_cons, List.mem_cons]; exact Or.inr he, hf⟩
    · exact ⟨s(a, b), by simp, hcut a b hab hc⟩

lemma two_le_card_cut_edges {a x : V} (p : G.Walk a a) (hp : p.IsTrail)
    (hx : x ∈ p.support) (hc : color a ≠ color x) :
    2 ≤ (cut ∩ p.edges.toFinset).card := by
  obtain ⟨e, he, hef⟩ := exists_cut_edge_of_walk color cut hcut (p.takeUntil x hx) hc
  obtain ⟨f, hf, hff⟩ := exists_cut_edge_of_walk color cut hcut (p.dropUntil x hx) hc.symm
  have hd := hp.disjoint_edges_takeUntil_dropUntil hx
  have hne : e ≠ f := by
    intro h
    subst f
    exact List.disjoint_left.1 hd he hf
  have hep : e ∈ p.edges := p.edges_takeUntil_subset_edges hx he
  have hfp : f ∈ p.edges := p.edges_dropUntil_subset_edges hx hf
  have hsub : ({e, f} : Finset (Sym2 V)) ⊆ cut ∩ p.edges.toFinset := by
    intro z hz
    simp only [mem_insert, mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact mem_inter.2 ⟨hef, List.mem_toFinset.2 hep⟩
    · exact mem_inter.2 ⟨hff, List.mem_toFinset.2 hfp⟩
  have hn : ({e, f} : Finset (Sym2 V)).card = 2 := by simp [hne]
  rw [← hn]
  exact card_le_card hsub

/-- A forbidden pair has constant color when all edges between colors lie in a cut of size
at most three. No finite ambient vertex type is needed. -/
theorem pair_constant_of_small_cut {u v : V} {p : G.Walk u u} {q : G.Walk v v}
    (hp : p.IsCycle) (hq : q.IsCycle)
    (hS : p.support.toFinset = q.support.toFinset)
    (hE : Disjoint p.edges.toFinset q.edges.toFinset) (hsize : cut.card ≤ 3) :
    ∀ x ∈ p.support, color x = color u := by
  intro x hx
  by_contra hne
  have hp2 := two_le_card_cut_edges color cut hcut p hp.isTrail hx (Ne.symm hne)
  have huq : u ∈ q.support := by
    rw [← List.mem_toFinset, ← hS, List.mem_toFinset]
    exact p.start_mem_support
  have hxq : x ∈ q.support := by
    rw [← List.mem_toFinset, ← hS, List.mem_toFinset]
    exact hx
  have hq2 : 2 ≤ (cut ∩ q.edges.toFinset).card := by
    by_cases hc : color v = color u
    · exact two_le_card_cut_edges color cut hcut q hq.isTrail hxq
        (fun h => hne (h.symm.trans hc))
    · exact two_le_card_cut_edges color cut hcut q hq.isTrail huq hc
  have hd : Disjoint (cut ∩ p.edges.toFinset) (cut ∩ q.edges.toFinset) := by
    apply Finset.disjoint_left.2
    intro e he hf
    exact Finset.disjoint_left.1 hE (mem_inter.1 he).2 (mem_inter.1 hf).2
  have hle : ((cut ∩ p.edges.toFinset) ∪ (cut ∩ q.edges.toFinset)).card ≤ cut.card :=
    card_le_card (union_subset inter_subset_left inter_subset_left)
  rw [card_union_of_disjoint hd] at hle
  omega

/-- Pair-free induced color classes remain pair-free when their entire separating cut has
at most three edges. -/
theorem not_hasPairF_of_small_cut (hsize : cut.card ≤ 3)
    (hfree : ∀ c, ¬ HasPairF (G.induce {x | color x = c})) : ¬ HasPairF G := by
  rintro ⟨u, v, p, q, hp, hq, hS, hE⟩
  have hps : ∀ x ∈ p.support, x ∈ {x | color x = color u} :=
    pair_constant_of_small_cut color cut hcut hp hq hS hE hsize
  have hqs : ∀ x ∈ q.support, x ∈ {x | color x = color u} := by
    intro x hx
    apply hps
    rwa [← List.mem_toFinset, hS, List.mem_toFinset]
  have hpair := (pair_map_iff (Embedding.induce {x | color x = color u}).toHom
    (Embedding.induce (G := G) _).injective (p.induce _ hps) (q.induce _ hqs)).1
    (by rw [Walk.map_induce, Walk.map_induce]; exact ⟨hp, hq, hS, hE⟩)
  exact hfree (color u) ⟨_, _, _, _, hpair⟩

/-- A convenient form of small-cut gluing: each color class injects into the same pair-free
target graph, although the projection need not be injective on the whole vertex type. -/
theorem not_hasPairF_of_small_cut_map {W : Type*} [DecidableEq W]
    (H : SimpleGraph W) (f : V → W) (hsize : cut.card ≤ 3) (hH : ¬ HasPairF H)
    (hinj : ∀ x y, color x = color y → f x = f y → x = y)
    (hadj : ∀ x y, color x = color y → G.Adj x y → H.Adj (f x) (f y)) :
    ¬ HasPairF G := by
  apply not_hasPairF_of_small_cut color cut hcut hsize
  intro c h
  let hom : G.induce {x | color x = c} →g H :=
    { toFun := fun x => f x.1
      map_rel' := fun {x y} hxy => hadj x.1 y.1 (x.2.trans y.2.symm) hxy }
  apply hH (h.map hom ?_)
  intro x y hxy
  exact Subtype.ext (hinj x.1 y.1 (x.2.trans y.2.symm) hxy)

end Cut

end Erdos585
