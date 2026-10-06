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
import Openmath.Proofs.SignedPrismCoreDefs

/-! # Unrestricted signed-prism obstruction for the quintic avoiding seed -/

open SimpleGraph Finset

namespace Erdos585.SignedPrismCore

set_option maxRecDepth 65536
set_option maxHeartbeats 64000000


/-- Rim rotations/reflections and the optional exchange of the two hubs. -/
def corePermutation (g : Fin 20) : Fin 7 → Fin 7 :=
  ![![0,1,2,3,4,5,6],
    ![0,1,2,3,4,6,5],
    ![1,2,3,4,0,5,6],
    ![1,2,3,4,0,6,5],
    ![2,3,4,0,1,5,6],
    ![2,3,4,0,1,6,5],
    ![3,4,0,1,2,5,6],
    ![3,4,0,1,2,6,5],
    ![4,0,1,2,3,5,6],
    ![4,0,1,2,3,6,5],
    ![0,4,3,2,1,5,6],
    ![0,4,3,2,1,6,5],
    ![1,0,4,3,2,5,6],
    ![1,0,4,3,2,6,5],
    ![2,1,0,4,3,5,6],
    ![2,1,0,4,3,6,5],
    ![3,2,1,0,4,5,6],
    ![3,2,1,0,4,6,5],
    ![4,3,2,1,0,5,6],
    ![4,3,2,1,0,6,5]] g

theorem corePermutation_injective (g : Fin 20) : Function.Injective (corePermutation g) := by
  have h : ∀ g : Fin 20, Function.Injective (corePermutation g) := by decide
  exact h g

def coreHom (g : Fin 20) : core →g core where
  toFun := corePermutation g
  map_rel' := by
    have h : ∀ (g : Fin 20) (u v : Fin 7), core.Adj u v →
        core.Adj (corePermutation g u) (corePermutation g v) := by decide
    intro u v huv
    exact h g u v huv

/-- This finite kernel check concerns only the nine normalized bits, after the
structural normalization of arbitrary signs in `hasPair_of_normalized`. -/
theorem normalized_cover :
    ∀ b : Fin 9 → Bool, ∃ g : Fin 20, ∃ i : Fin 5,
      templateCondition
        (normalizedBits (pullSign (corePermutation g) (normalizedSign b))) i := by
  decide

/-- Every signing of the actual pentagon-plus-two-hubs core has an actual pair. -/
theorem core_hasPair (σ : Sym2 (Fin 7) → Bool) : HasPairF (prism core σ) := by
  apply hasPair_of_normalized σ
  let b := normalizedBits σ
  obtain ⟨g, i, hi⟩ := normalized_cover b
  have hp := hasPair_of_normalized
    (pullSign (corePermutation g) (normalizedSign b)) (template_hasPair _ i hi)
  exact hp.map (prismHom (coreHom g) (normalizedSign b))
    (prismHom_injective (coreHom g) (corePermutation_injective g) (normalizedSign b))

theorem core_faithful_pair (σ : Sym2 (Fin 7) → Bool) :
    HasTwoEdgeDisjointCyclesSameVertexSet (prism core σ) :=
  (hasPairF_iff _).mp (core_hasPair σ)

/-- The core occurs inside the first eight-vertex block of the checked seed. -/
def coreToFive : Fin 7 → Fin 32 := ![1,3,2,5,4,6,7]

theorem coreToFive_injective : Function.Injective coreToFive := by decide

def coreToFiveHom : core →g RegularFive.graph where
  toFun := coreToFive
  map_rel' := by decide

theorem regularFive_hasPair (σ : Sym2 (Fin 32) → Bool) :
    HasPairF (prism RegularFive.graph σ) :=
  (core_hasPair (pullSign coreToFive σ)).map (prismHom coreToFiveHom σ)
    (prismHom_injective coreToFiveHom coreToFive_injective σ)

section Degree

variable {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (σ : Sym2 V → Bool)

theorem neighborFinset_prism (x : V) (a : Bool) :
    (prism G σ).neighborFinset (x,a) =
      insert (x,!a) ((G.neighborFinset x).image fun y => (y,a ^^ σ s(x,y))) := by
  ext ⟨y,b⟩
  rw [mem_neighborFinset, Finset.mem_insert, Finset.mem_image]
  constructor
  · intro h
    rcases h with ⟨hxy,hab⟩ | ⟨hxy,hab⟩
    · change x = y at hxy
      subst y
      left
      have hb : b = !a := by cases a <;> cases b <;> simp_all
      exact congrArg (fun c => (x,c)) hb
    · right
      refine ⟨y, (mem_neighborFinset _ _ _).mpr hxy, ?_⟩
      change (a ^^ b) = σ s(x,y) at hab
      have hb : (a ^^ σ s(x,y)) = b := by
        cases a <;> cases b <;> cases hs : σ s(x,y) <;> simp_all
      exact congrArg (fun c => (y,c)) hb
  · intro h
    rcases h with h | ⟨w,hw,h⟩
    · have hyx : y = x := congrArg Prod.fst h
      have hba : b = !a := congrArg Prod.snd h
      subst y
      subst b
      exact Or.inl ⟨rfl, by cases a <;> simp⟩
    · have hwy : w = y := congrArg Prod.fst h
      subst w
      have hab : (a ^^ σ s(x,y)) = b := congrArg Prod.snd h
      apply Or.inr
      refine ⟨(mem_neighborFinset _ _ _).mp hw, ?_⟩
      change (a ^^ b) = σ s(x,y)
      cases a <;> cases b <;> cases hs : σ s(x,y) <;> simp_all

/-- A signed prism raises every vertex degree by exactly one. -/
theorem prism_degree (x : V) (a : Bool) :
    (prism G σ).degree (x,a) = G.degree x + 1 := by
  have hi : Function.Injective (fun y : V => (y,a ^^ σ s(x,y))) := by
    intro u v h
    exact congrArg Prod.fst h
  have hn : (x,!a) ∉ (G.neighborFinset x).image (fun y => (y,a ^^ σ s(x,y))) := by
    intro h
    obtain ⟨y,hy,he⟩ := Finset.mem_image.mp h
    have hyx : y = x := congrArg Prod.fst he
    subst y
    exact G.loopless.irrefl x ((mem_neighborFinset _ _ _).mp hy)
  rw [← card_neighborFinset_eq_degree, neighborFinset_prism,
    Finset.card_insert_of_notMem hn, Finset.card_image_of_injective _ hi,
    card_neighborFinset_eq_degree]

end Degree

/-- Every signing gives an actual six-regular 64-vertex positive graph. -/
theorem regularFive_prism (σ : Sym2 (Fin 32) → Bool) :
    Fintype.card (Fin 32 × Bool) = 64 ∧
      (prism RegularFive.graph σ).IsRegularOfDegree 6 ∧
      HasTwoEdgeDisjointCyclesSameVertexSet (prism RegularFive.graph σ) := by
  refine ⟨by decide, ?_, (hasPairF_iff _).mp (regularFive_hasPair σ)⟩
  intro ⟨x,a⟩
  rw [prism_degree, RegularFive.graph_degree]

/-- The avoiding quintic seed has no avoiding degree-six signed prism. -/
theorem signed_prism_raising_counterexample :
    RegularFive.graph.IsRegularOfDegree 5 ∧
      ¬ HasTwoEdgeDisjointCyclesSameVertexSet RegularFive.graph ∧
      ∀ σ : Sym2 (Fin 32) → Bool,
        Fintype.card (Fin 32 × Bool) = 64 ∧
        (prism RegularFive.graph σ).IsRegularOfDegree 6 ∧
        HasTwoEdgeDisjointCyclesSameVertexSet (prism RegularFive.graph σ) := by
  exact ⟨RegularFive.graph_degree, (hasPairF_iff _).not.mp RegularFive.graph_not_hasPair,
    regularFive_prism⟩

end Erdos585.SignedPrismCore
