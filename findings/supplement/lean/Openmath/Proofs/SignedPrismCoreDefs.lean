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
import Openmath.Proofs.RegularFive

/-!
# Every signed prism of the quintic construction contains a faithful pair

The local core is a pentagon joined to two nonadjacent hubs. Structural fiber
switching reduces arbitrary edge signs to nine free bits. Five actual cycle
templates cover all normalized signings after core automorphisms.
-/

open SimpleGraph Finset

namespace Erdos585.SignedPrismCore

set_option maxRecDepth 65536
set_option maxHeartbeats 32000000

variable {V W : Type*}

/-- The signed two-lift together with every vertical fiber edge. -/
def prism (G : SimpleGraph V) (σ : Sym2 V → Bool) : SimpleGraph (V × Bool) where
  Adj x y := (x.1 = y.1 ∧ x.2 ≠ y.2) ∨
    (G.Adj x.1 y.1 ∧ (x.2 ^^ y.2) = σ s(x.1,y.1))
  symm := ⟨by
    intro x y h
    rcases h with h | h
    · exact Or.inl ⟨h.1.symm, h.2.symm⟩
    · exact Or.inr ⟨G.adj_symm h.1, by
        simpa only [Bool.xor_comm, Sym2.eq_swap] using h.2⟩⟩
  loopless := ⟨by
    intro x h
    rcases h with h | h
    · exact h.2 rfl
    · exact G.loopless.irrefl _ h.1⟩

instance [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (σ : Sym2 V → Bool) : DecidableRel (prism G σ).Adj := fun _ _ =>
  inferInstanceAs (Decidable (_ ∨ _))

/-- Pulling signs back along an actual graph map. -/
def pullSign (f : V → W) (σ : Sym2 W → Bool) : Sym2 V → Bool :=
  fun e => σ (e.map f)

def prismHom {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G →g H) (σ : Sym2 W → Bool) :
    prism G (pullSign f σ) →g prism H σ where
  toFun x := (f x.1, x.2)
  map_rel' := by
    intro x y h
    rcases h with h | h
    · exact Or.inl ⟨congrArg f h.1, h.2⟩
    · exact Or.inr ⟨f.map_rel h.1, h.2⟩

theorem prismHom_injective {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G →g H) (hf : Function.Injective f) (σ : Sym2 W → Bool) :
    Function.Injective (prismHom f σ) := by
  intro x y h
  exact Prod.ext (hf (congrArg (fun z : W × Bool => z.1) h))
    (congrArg (fun z : W × Bool => z.2) h)

/-- Swapping the two labels in the fiber at each vertex with potential true. -/
def switched (σ : Sym2 V → Bool) (τ : V → Bool) : Sym2 V → Bool :=
  fun e => σ e ^^ Sym2.lift ⟨fun u v => τ u ^^ τ v, fun _ _ => Bool.xor_comm _ _⟩ e

@[simp] theorem switched_mk (σ : Sym2 V → Bool) (τ : V → Bool) (u v : V) :
    switched σ τ s(u,v) = (σ s(u,v) ^^ (τ u ^^ τ v)) := rfl

def switchVertex (τ : V → Bool) (x : V × Bool) : V × Bool :=
  (x.1, x.2 ^^ τ x.1)

theorem switchVertex_injective (τ : V → Bool) : Function.Injective (switchVertex τ) := by
  rintro ⟨x,a⟩ ⟨y,b⟩ h
  have hxy : x = y := congrArg Prod.fst h
  subst y
  have hab : (a ^^ τ x) = (b ^^ τ x) := congrArg Prod.snd h
  have : a = b := by
    cases a <;> cases b <;> cases ht : τ x <;> simp_all
  exact Prod.ext rfl this

def switchHom (G : SimpleGraph V) (σ : Sym2 V → Bool) (τ : V → Bool) :
    prism G (switched σ τ) →g prism G σ where
  toFun := switchVertex τ
  map_rel' := by
    rintro ⟨x,a⟩ ⟨y,b⟩ h
    rcases h with ⟨hxy, hab⟩ | ⟨hxy, hab⟩
    · change x = y at hxy
      subst y
      apply Or.inl
      refine ⟨rfl, ?_⟩
      cases a <;> cases b <;> cases ht : τ x <;> simp_all [switchVertex]
    · apply Or.inr
      refine ⟨hxy, ?_⟩
      change ((a ^^ τ x) ^^ (b ^^ τ y)) = σ s(x,y)
      change (a ^^ b) = (σ s(x,y) ^^ (τ x ^^ τ y)) at hab
      cases a <;> cases b <;> cases hx : τ x <;> cases hy : τ y <;>
        cases hs : σ s(x,y) <;> simp_all

/-- The five rim vertices are 0,...,4; the two nonadjacent hubs are 5,6. -/
def core : SimpleGraph (Fin 7) := .fromRel fun a b =>
  (a,b) ∈ ([(0,1),(1,2),(2,3),(3,4),(4,0),
    (0,5),(1,5),(2,5),(3,5),(4,5),
    (0,6),(1,6),(2,6),(3,6),(4,6)] : List (Fin 7 × Fin 7))

instance : DecidableRel core.Adj :=
  inferInstanceAs (DecidableRel (SimpleGraph.fromRel _).Adj)

def potential (σ : Sym2 (Fin 7) → Bool) : Fin 7 → Bool :=
  ![σ s(0,5), σ s(1,5), σ s(2,5), σ s(3,5), σ s(4,5), false,
    σ s(0,6) ^^ σ s(0,5)]

/-- The nine off-tree signs; the six spanning-tree signs are false. -/
def normalizedSign (b : Fin 9 → Bool) (e : Sym2 (Fin 7)) : Bool :=
  if e = s(0,1) then b 0 else
  if e = s(0,4) then b 1 else
  if e = s(1,2) then b 2 else
  if e = s(1,6) then b 3 else
  if e = s(2,3) then b 4 else
  if e = s(2,6) then b 5 else
  if e = s(3,4) then b 6 else
  if e = s(3,6) then b 7 else
  if e = s(4,6) then b 8 else false

def normalizedBits (σ : Sym2 (Fin 7) → Bool) : Fin 9 → Bool :=
  let σ' := switched σ (potential σ)
  ![σ' s(0,1), σ' s(0,4), σ' s(1,2), σ' s(1,6), σ' s(2,3),
    σ' s(2,6), σ' s(3,4), σ' s(3,6), σ' s(4,6)]

theorem normalization_on_core (σ : Sym2 (Fin 7) → Bool) :
    ∀ u v, core.Adj u v →
      switched σ (potential σ) s(u,v) = normalizedSign (normalizedBits σ) s(u,v) := by
  intro u v h
  fin_cases u <;> fin_cases v <;>
    simp_all [core, SimpleGraph.fromRel, normalizedSign, normalizedBits,
      switched, potential, Sym2.eq_swap, Bool.xor_comm]
  all_goals try exact congrArg σ (by decide)
  all_goals
    cases h₁ : σ s(1,6) <;> cases h₂ : σ s(0,5) <;>
      cases h₃ : σ s(0,6) <;> cases h₄ : σ s(1,5) <;> simp_all

/-- The normalized theorem implies the unrestricted theorem by an actual injective map. -/
theorem hasPair_of_normalized (σ : Sym2 (Fin 7) → Bool)
    (h : HasPairF (prism core (normalizedSign (normalizedBits σ)))) :
    HasPairF (prism core σ) := by
  let f : prism core (normalizedSign (normalizedBits σ)) →g
      prism core (switched σ (potential σ)) := {
    toFun := id
    map_rel' := by
      intro x y hxy
      rcases hxy with hxy | hxy
      · exact Or.inl hxy
      · exact Or.inr ⟨hxy.1, hxy.2.trans (normalization_on_core σ _ _ hxy.1).symm⟩ }
  exact (h.map f (fun _ _ hxy => hxy)).map (switchHom core σ (potential σ))
    (switchVertex_injective (potential σ))


/-- Each template contains exactly the edges of its two displayed cycles. -/
def templateEdges (i : Fin 5) : List (Fin 14 × Fin 14) :=
  ![[(0,2),(2,3),(3,11),(11,10),(10,8),(8,9),(9,1),(1,13),(13,12),(12,0),(0,8),(8,12),(12,3),(3,1),(1,11),(11,9),(9,13),(13,2),(2,10),(10,0)],
    [(0,2),(2,5),(5,11),(11,3),(3,1),(1,13),(13,9),(9,8),(8,10),(10,4),(4,12),(12,0),(0,1),(1,8),(8,12),(12,13),(13,5),(5,4),(4,3),(3,2),(2,10),(10,11),(11,9),(9,0)],
    [(0,9),(9,6),(6,7),(7,13),(13,1),(1,11),(11,10),(10,8),(8,12),(12,0),(0,1),(1,8),(8,7),(7,11),(11,9),(9,13),(13,12),(12,6),(6,10),(10,0)],
    [(0,1),(1,13),(13,7),(7,8),(8,10),(10,11),(11,9),(9,6),(6,12),(12,0),(0,9),(9,12),(12,13),(13,8),(8,1),(1,11),(11,7),(7,6),(6,10),(10,0)],
    [(0,1),(1,9),(9,11),(11,7),(7,13),(13,5),(5,4),(4,12),(12,6),(6,10),(10,8),(8,0),(0,10),(10,4),(4,6),(6,7),(7,5),(5,11),(11,1),(1,13),(13,9),(9,8),(8,12),(12,0)]] i

def template (i : Fin 5) : SimpleGraph (Fin 14) :=
  .fromRel fun a b => (a,b) ∈ templateEdges i

instance (i : Fin 5) : DecidableRel (template i).Adj :=
  inferInstanceAs (DecidableRel (SimpleGraph.fromRel _).Adj)

def red0 : (template 0).Walk 0 0 :=
  .cons (v := 2) (by decide) (.cons (v := 3) (by decide) (.cons (v := 11) (by decide) (.cons (v := 10) (by decide) (.cons (v := 8) (by decide) (.cons (v := 9) (by decide) (.cons (v := 1) (by decide) (.cons (v := 13) (by decide) (.cons (v := 12) (by decide) (.cons (v := 0) (by decide) (.nil))))))))))

theorem red0_cycle : red0.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  exact ⟨by decide, by simp [red0], by decide⟩

def blue0 : (template 0).Walk 0 0 :=
  .cons (v := 8) (by decide) (.cons (v := 12) (by decide) (.cons (v := 3) (by decide) (.cons (v := 1) (by decide) (.cons (v := 11) (by decide) (.cons (v := 9) (by decide) (.cons (v := 13) (by decide) (.cons (v := 2) (by decide) (.cons (v := 10) (by decide) (.cons (v := 0) (by decide) (.nil))))))))))

theorem blue0_cycle : blue0.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  exact ⟨by decide, by simp [blue0], by decide⟩

def red1 : (template 1).Walk 0 0 :=
  .cons (v := 2) (by decide) (.cons (v := 5) (by decide) (.cons (v := 11) (by decide) (.cons (v := 3) (by decide) (.cons (v := 1) (by decide) (.cons (v := 13) (by decide) (.cons (v := 9) (by decide) (.cons (v := 8) (by decide) (.cons (v := 10) (by decide) (.cons (v := 4) (by decide) (.cons (v := 12) (by decide) (.cons (v := 0) (by decide) (.nil))))))))))))

theorem red1_cycle : red1.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  exact ⟨by decide, by simp [red1], by decide⟩

def blue1 : (template 1).Walk 0 0 :=
  .cons (v := 1) (by decide) (.cons (v := 8) (by decide) (.cons (v := 12) (by decide) (.cons (v := 13) (by decide) (.cons (v := 5) (by decide) (.cons (v := 4) (by decide) (.cons (v := 3) (by decide) (.cons (v := 2) (by decide) (.cons (v := 10) (by decide) (.cons (v := 11) (by decide) (.cons (v := 9) (by decide) (.cons (v := 0) (by decide) (.nil))))))))))))

theorem blue1_cycle : blue1.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  exact ⟨by decide, by simp [blue1], by decide⟩

def red2 : (template 2).Walk 0 0 :=
  .cons (v := 9) (by decide) (.cons (v := 6) (by decide) (.cons (v := 7) (by decide) (.cons (v := 13) (by decide) (.cons (v := 1) (by decide) (.cons (v := 11) (by decide) (.cons (v := 10) (by decide) (.cons (v := 8) (by decide) (.cons (v := 12) (by decide) (.cons (v := 0) (by decide) (.nil))))))))))

theorem red2_cycle : red2.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  exact ⟨by decide, by simp [red2], by decide⟩

def blue2 : (template 2).Walk 0 0 :=
  .cons (v := 1) (by decide) (.cons (v := 8) (by decide) (.cons (v := 7) (by decide) (.cons (v := 11) (by decide) (.cons (v := 9) (by decide) (.cons (v := 13) (by decide) (.cons (v := 12) (by decide) (.cons (v := 6) (by decide) (.cons (v := 10) (by decide) (.cons (v := 0) (by decide) (.nil))))))))))

theorem blue2_cycle : blue2.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  exact ⟨by decide, by simp [blue2], by decide⟩

def red3 : (template 3).Walk 0 0 :=
  .cons (v := 1) (by decide) (.cons (v := 13) (by decide) (.cons (v := 7) (by decide) (.cons (v := 8) (by decide) (.cons (v := 10) (by decide) (.cons (v := 11) (by decide) (.cons (v := 9) (by decide) (.cons (v := 6) (by decide) (.cons (v := 12) (by decide) (.cons (v := 0) (by decide) (.nil))))))))))

theorem red3_cycle : red3.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  exact ⟨by decide, by simp [red3], by decide⟩

def blue3 : (template 3).Walk 0 0 :=
  .cons (v := 9) (by decide) (.cons (v := 12) (by decide) (.cons (v := 13) (by decide) (.cons (v := 8) (by decide) (.cons (v := 1) (by decide) (.cons (v := 11) (by decide) (.cons (v := 7) (by decide) (.cons (v := 6) (by decide) (.cons (v := 10) (by decide) (.cons (v := 0) (by decide) (.nil))))))))))

theorem blue3_cycle : blue3.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  exact ⟨by decide, by simp [blue3], by decide⟩

def red4 : (template 4).Walk 0 0 :=
  .cons (v := 1) (by decide) (.cons (v := 9) (by decide) (.cons (v := 11) (by decide) (.cons (v := 7) (by decide) (.cons (v := 13) (by decide) (.cons (v := 5) (by decide) (.cons (v := 4) (by decide) (.cons (v := 12) (by decide) (.cons (v := 6) (by decide) (.cons (v := 10) (by decide) (.cons (v := 8) (by decide) (.cons (v := 0) (by decide) (.nil))))))))))))

theorem red4_cycle : red4.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  exact ⟨by decide, by simp [red4], by decide⟩

def blue4 : (template 4).Walk 0 0 :=
  .cons (v := 10) (by decide) (.cons (v := 4) (by decide) (.cons (v := 6) (by decide) (.cons (v := 7) (by decide) (.cons (v := 5) (by decide) (.cons (v := 11) (by decide) (.cons (v := 1) (by decide) (.cons (v := 13) (by decide) (.cons (v := 9) (by decide) (.cons (v := 8) (by decide) (.cons (v := 12) (by decide) (.cons (v := 0) (by decide) (.nil))))))))))))

theorem blue4_cycle : blue4.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  exact ⟨by decide, by simp [blue4], by decide⟩

theorem templates_havePair (i : Fin 5) : HasPairF (template i) := by
  fin_cases i
  · exact ⟨0, 0, red0, blue0, red0_cycle, blue0_cycle, by decide, by decide⟩
  · exact ⟨0, 0, red1, blue1, red1_cycle, blue1_cycle, by decide, by decide⟩
  · exact ⟨0, 0, red2, blue2, red2_cycle, blue2_cycle, by decide, by decide⟩
  · exact ⟨0, 0, red3, blue3, red3_cycle, blue3_cycle, by decide, by decide⟩
  · exact ⟨0, 0, red4, blue4, red4_cycle, blue4_cycle, by decide, by decide⟩

/-- The paper labels (v,a) by 2v+a. -/
def label (x : Fin 14) : Fin 7 × Bool :=
  (⟨x.val / 2, by omega⟩, decide (x.val % 2 = 1))

theorem label_injective : Function.Injective label := by decide

def templateCondition (b : Fin 9 → Bool) (i : Fin 5) : Prop :=
  if i = 0 then b 0 = false ∧ b 1 = false ∧ b 3 = true ∧ b 8 = false else
  if i = 1 then b 0 = false ∧ b 1 = true ∧ b 2 = true ∧ b 5 = false ∧ b 8 = false else
  if i = 2 then b 1 = true ∧ b 6 = true ∧ b 7 = false ∧ b 8 = false else
  if i = 3 then b 1 = true ∧ b 6 = true ∧ b 7 = false ∧ b 8 = true else
    b 1 = false ∧ b 4 = false ∧ b 6 = false ∧ b 5 = false ∧ b 7 = false ∧ b 8 = false

instance (b : Fin 9 → Bool) (i : Fin 5) : Decidable (templateCondition b i) := by
  unfold templateCondition
  infer_instance

theorem template_adjacency (b : Fin 9 → Bool) (i : Fin 5) (h : templateCondition b i) :
    ∀ u v, (template i).Adj u v →
      (prism core (normalizedSign b)).Adj (label u) (label v) := by
  intro u v huv
  fin_cases i <;> fin_cases u <;> fin_cases v <;>
    simp_all [templateCondition, template, templateEdges, label, prism, core,
      SimpleGraph.fromRel, normalizedSign]

theorem template_hasPair (b : Fin 9 → Bool) (i : Fin 5) (h : templateCondition b i) :
    HasPairF (prism core (normalizedSign b)) :=
  (templates_havePair i).map
    ⟨label, fun hxy => template_adjacency b i h _ _ hxy⟩ label_injective

end Erdos585.SignedPrismCore
