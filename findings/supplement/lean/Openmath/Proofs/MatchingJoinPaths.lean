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

/-! # Actual whole-seed path pairs obtained by joining the two certified halves -/

open SimpleGraph Finset
namespace Erdos585.MatchingJoin

set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

theorem list_toFinset_map {V W : Type*} [DecidableEq V] [DecidableEq W]
    (f : V → W) (l : List V) : (l.map f).toFinset = l.toFinset.image f := by
  ext w
  simp

theorem TwoPaths.map {V W : Type*} [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} {a b c d : V}
    (hp : TwoPaths G a b c d) (f : G →g H) (hf : Function.Injective f) :
    TwoPaths H (f a) (f b) (f c) (f d) := by
  obtain ⟨r,t,hr,ht,hs,he⟩ := hp
  refine ⟨r.map f,t.map f,hr.map hf,ht.map hf,?_,?_⟩
  · simp only [Walk.support_map, list_toFinset_map]
    rw [hs]
  · simp only [Walk.edges_map, list_toFinset_map]
    exact (Finset.disjoint_image (Sym2.map.injective hf)).mpr he

theorem mono_map {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G →g H) (color : W → Bool) (s : Bool) (hc : ∀ v, color (f v) = s)
    {a b : V} (p : G.Walk a b) : Mono color s (p.map f) := by
  intro w hw
  rw [Walk.support_map] at hw
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hw
  exact hc v

theorem Mono.reverse {V : Type*} {G : SimpleGraph V} {color : V → Bool} {s : Bool}
    {a b : V} {p : G.Walk a b} (hp : Mono color s p) : Mono color s p.reverse := by
  intro v hv
  apply hp v
  simpa using hv

abbrev halfHom (s : Bool) : RegularFive.half →g RegularFive.graph where
  toFun := embed s
  map_rel' := by
    have hh : ∀ (s : Bool) (x y : Fin 16), RegularFive.half.Adj x y →
        RegularFive.graph.Adj (embed s x) (embed s y) := by decide
    intro x y hxy
    exact hh s x y hxy

def halfColor (s : Bool) (v : Fin 32) : Bool := (decide (16 ≤ v.val)) ^^ s

theorem halfColor_left (s : Bool) (x : Fin 16) : halfColor s (embed s x) = false := by
  have h : ∀ (s : Bool) (x : Fin 16), halfColor s (embed s x) = false := by decide
  exact h s x

theorem halfColor_right (s : Bool) (x : Fin 16) : halfColor s (embed (!s) x) = true := by
  have h : ∀ (s : Bool) (x : Fin 16), halfColor s (embed (!s) x) = true := by decide
  exact h s x

theorem red_cut (s : Bool) : RegularFive.graph.Adj (embed s 2) (embed (!s) 2) := by
  cases s <;> decide

theorem blue_cut (s : Bool) : RegularFive.graph.Adj (embed s 8) (embed (!s) 8) := by
  cases s <;> decide

/-- Both old halves are used through their two actual old joining edges. -/
theorem whole_twoPaths (s : Bool) (x₀ y₀ x₁ y₁ : Fin 16)
    (h₀ : Admitted x₀ y₀) (h₁ : Admitted x₁ y₁) :
    TwoPaths RegularFive.graph (embed s x₀) (embed (!s) x₁)
      (embed s y₀) (embed (!s) y₁) := by
  obtain ⟨r₀,t₀,hr₀,ht₀,hs₀,he₀⟩ := half_twoPaths x₀ y₀ h₀
  obtain ⟨r₁,t₁,hr₁,ht₁,hs₁,he₁⟩ := half_twoPaths x₁ y₁ h₁
  let R₀ := r₀.map (halfHom s)
  let T₀ := t₀.map (halfHom s)
  let R₁ := r₁.map (halfHom (!s))
  let T₁ := t₁.map (halfHom (!s))
  have hmR₀ : Mono (halfColor s) false R₀ := mono_map _ _ _ (halfColor_left s) r₀
  have hmT₀ : Mono (halfColor s) false T₀ := mono_map _ _ _ (halfColor_left s) t₀
  have hmR₁ : Mono (halfColor s) true R₁ := mono_map _ _ _ (halfColor_right s) r₁
  have hmT₁ : Mono (halfColor s) true T₁ := mono_map _ _ _ (halfColor_right s) t₁
  have hr₀' : R₀.IsPath := hr₀.map (embed_injective s)
  have ht₀' : T₀.IsPath := ht₀.map (embed_injective s)
  have hr₁' : R₁.IsPath := hr₁.map (embed_injective (!s))
  have ht₁' : T₁.IsPath := ht₁.map (embed_injective (!s))
  refine ⟨bridge R₀.reverse R₁ (red_cut s), bridge T₀.reverse T₁ (blue_cut s),
    bridge_isPath _ _ _ hr₀'.reverse hr₁' (hmR₀.reverse.support_disjoint hmR₁),
    bridge_isPath _ _ _ ht₀'.reverse ht₁' (hmT₀.reverse.support_disjoint hmT₁), ?_, ?_⟩
  · simp only [support_bridge, Walk.support_reverse, List.toFinset_append,
      List.toFinset_reverse, R₀,T₀,R₁,T₁,Walk.support_map,list_toFinset_map]
    rw [hs₀,hs₁]
  · apply bridges_disjoint _ _ _ _ _ _ hmR₀.reverse hmT₀.reverse hmR₁ hmT₁
    · simp only [Walk.edges_reverse, List.toFinset_reverse, R₀,T₀,
        Walk.edges_map,list_toFinset_map]
      exact (Finset.disjoint_image (Sym2.map.injective (embed_injective s))).mpr he₀
    · simp only [R₁,T₁,Walk.edges_map,list_toFinset_map]
      exact (Finset.disjoint_image (Sym2.map.injective (embed_injective (!s)))).mpr he₁
    · exact fun hh => (by decide : (2 : Fin 16) ≠ 8) (embed_injective s hh)

end Erdos585.MatchingJoin
