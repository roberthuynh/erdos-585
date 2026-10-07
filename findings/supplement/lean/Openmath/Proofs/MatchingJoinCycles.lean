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
import Openmath.Proofs.MatchingJoinCertificates
import Openmath.Proofs.MatchingJoinWalks

/-!
# Closing actual same-support path pairs across four matching edges

The two old copies have disjoint vertex sets. Each color uses one actual
path in each copy and two distinct matching edges. Support equality is needed
within each copy only; no image relation between the two supports is assumed.
-/

open SimpleGraph Finset

namespace Erdos585.MatchingJoin

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

private abbrev copyHom (f : Equiv.Perm (Fin 32)) (s : Bool) :
    RegularFive.graph →g graph f where
  toFun x := (x,s)
  map_rel' h := Or.inl ⟨rfl, h⟩

private lemma copy_injective (f : Equiv.Perm (Fin 32)) (s : Bool) :
    Function.Injective (copyHom f s) := by
  intro x y h
  exact congrArg Prod.fst h

private lemma copy_mono (f : Equiv.Perm (Fin 32)) (s : Bool)
    {a b : Fin 32} (p : RegularFive.graph.Walk a b) :
    Mono Prod.snd s (p.map (copyHom f s)) := by
  intro v hv
  rw [Walk.support_map] at hv
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hv
  rfl

private lemma matching_edge (f : Equiv.Perm (Fin 32)) (x : Fin 32) :
    (graph f).Adj (x,false) (f x,true) := Or.inr (Or.inl ⟨rfl,rfl,rfl⟩)

private lemma closed_support {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {a b c d : V} (p : G.Walk a b) (q : G.Walk c d)
    (hbc : G.Adj b c) (hda : G.Adj d a) :
    ((bridge p q hbc).cons hda).support.toFinset =
      p.support.toFinset ∪ q.support.toFinset := by
  rw [Walk.support_cons, support_bridge, List.toFinset_cons, List.toFinset_append]
  exact insert_eq_of_mem (mem_union_right _ (List.mem_toFinset.mpr q.end_mem_support))

private lemma mapped_finset {V W : Type*} [DecidableEq V] [DecidableEq W]
    (p : List V) (f : V → W) : (p.map f).toFinset = p.toFinset.image f := by
  ext x
  simp

/-- Actual simple paths in the two old copies close to faithful cycles.
All four matching edges and both cycles are explicitly constructed. -/
theorem hasPair_of_twoPaths (f : Equiv.Perm (Fin 32)) {a b c d : Fin 32}
    (hab : a ≠ b) (hcd : c ≠ d) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d)
    (hp : TwoPaths RegularFive.graph a b c d)
    (hq : TwoPaths RegularFive.graph (f a) (f b) (f c) (f d)) :
    HasPairF (graph f) := by
  obtain ⟨r₀,t₀,hr₀,ht₀,hs₀,he₀⟩ := hp
  obtain ⟨r₁,t₁,hr₁,ht₁,hs₁,he₁⟩ := hq
  let R₀ := r₀.map (copyHom f false)
  let T₀ := t₀.map (copyHom f false)
  let R₁ := r₁.reverse.map (copyHom f true)
  let T₁ := t₁.reverse.map (copyHom f true)
  have hmR₀ : Mono Prod.snd false R₀ := copy_mono f false r₀
  have hmT₀ : Mono Prod.snd false T₀ := copy_mono f false t₀
  have hmR₁ : Mono Prod.snd true R₁ := copy_mono f true r₁.reverse
  have hmT₁ : Mono Prod.snd true T₁ := copy_mono f true t₁.reverse
  have hr₀' : R₀.IsPath := hr₀.map (copy_injective f false)
  have ht₀' : T₀.IsPath := ht₀.map (copy_injective f false)
  have hr₁' : R₁.IsPath := hr₁.reverse.map (copy_injective f true)
  have ht₁' : T₁.IsPath := ht₁.reverse.map (copy_injective f true)
  have hE₀ : Disjoint R₀.edges.toFinset T₀.edges.toFinset := by
    simp only [R₀,T₀,Walk.edges_map,mapped_finset]
    exact (Finset.disjoint_image (Sym2.map.injective (copy_injective f false))).mpr he₀
  have hE₁ : Disjoint R₁.edges.toFinset T₁.edges.toFinset := by
    simp only [R₁,T₁,Walk.edges_map,Walk.edges_reverse,mapped_finset,List.toFinset_reverse]
    exact (Finset.disjoint_image (Sym2.map.injective (copy_injective f true))).mpr he₁
  have hS₀ : R₀.support.toFinset = T₀.support.toFinset := by
    simp only [R₀,T₀,Walk.support_map,mapped_finset]
    rw [hs₀]
  have hS₁ : R₁.support.toFinset = T₁.support.toFinset := by
    simp only [R₁,T₁,Walk.support_map,Walk.support_reverse,mapped_finset,List.toFinset_reverse]
    rw [hs₁]
  have hab' : (a,false) ≠ (b,false) := fun h => hab (congrArg Prod.fst h)
  have hcd' : (c,false) ≠ (d,false) := fun h => hcd (congrArg Prod.fst h)
  have hac' : (a,false) ≠ (c,false) := fun h => hac (congrArg Prod.fst h)
  have had' : (a,false) ≠ (d,false) := fun h => had (congrArg Prod.fst h)
  have hcb' : (c,false) ≠ (b,false) := fun h => hbc (congrArg Prod.fst h.symm)
  have hbd' : (b,false) ≠ (d,false) := fun h => hbd (congrArg Prod.fst h)
  let P := bridge R₀ R₁ (matching_edge f b)
  let Q := bridge T₀ T₁ (matching_edge f d)
  have hPQ : Disjoint P.edges.toFinset Q.edges.toFinset :=
    bridges_disjoint R₀ T₀ R₁ T₁ (matching_edge f b) (matching_edge f d)
      hmR₀ hmT₀ hmR₁ hmT₁ hE₀ hE₁ hbd'
  have hA : s((f a,true),(a,false)) ∉ Q.edges := by
    rw [Sym2.eq_swap]
    change s((a,false),(f a,true)) ∉ (bridge T₀ T₁ (matching_edge f d)).edges
    rw [edges_bridge]
    simp only [List.mem_append, List.mem_cons, not_or]
    exact ⟨hmT₀.not_cross rfl rfl,
      cross_ne (color := Prod.snd) rfl rfl rfl rfl had', hmT₁.not_cross rfl rfl⟩
  have hC : s((f c,true),(c,false)) ∉ P.edges := by
    rw [Sym2.eq_swap]
    change s((c,false),(f c,true)) ∉ (bridge R₀ R₁ (matching_edge f b)).edges
    rw [edges_bridge]
    simp only [List.mem_append, List.mem_cons, not_or]
    exact ⟨hmR₀.not_cross rfl rfl,
      cross_ne (color := Prod.snd) rfl rfl rfl rfl hcb', hmR₁.not_cross rfl rfl⟩
  have hAC : s((f a,true),(a,false)) ≠ s((f c,true),(c,false)) := by
    intro h
    have h' : s((a,false),(f a,true)) = s((c,false),(f c,true)) :=
      Sym2.eq_swap.trans (h.trans Sym2.eq_swap)
    exact cross_ne (color := Prod.snd) rfl rfl rfl rfl hac' h'
  let C₀ := P.cons (matching_edge f a).symm
  let C₁ := Q.cons (matching_edge f c).symm
  refine ⟨(f a,true),(f c,true),C₀,C₁,?_,?_,?_,?_⟩
  · exact bridge_close_cycle R₀ R₁ (matching_edge f b)
      (matching_edge f a).symm hr₀' hr₁' (hmR₀.support_disjoint hmR₁) hab'
  · exact bridge_close_cycle T₀ T₁ (matching_edge f d)
      (matching_edge f c).symm ht₀' ht₁' (hmT₀.support_disjoint hmT₁) hcd'
  · rw [show C₀.support.toFinset = R₀.support.toFinset ∪ R₁.support.toFinset from
        closed_support R₀ R₁ (matching_edge f b) (matching_edge f a).symm,
      show C₁.support.toFinset = T₀.support.toFinset ∪ T₁.support.toFinset from
        closed_support T₀ T₁ (matching_edge f d) (matching_edge f c).symm,
      hS₀,hS₁]
  · simp only [C₀,C₁,Walk.edges_cons,List.toFinset_cons]
    rw [Finset.disjoint_insert_left, Finset.disjoint_insert_right]
    exact ⟨by simpa only [mem_insert, List.mem_toFinset, not_or] using And.intro hAC hA,
      List.mem_toFinset.not.mpr hC, hPQ⟩

end Erdos585.MatchingJoin
