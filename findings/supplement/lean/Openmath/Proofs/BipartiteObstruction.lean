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
# A local obstruction for an attempted bipartite edge-splitting argument

The complete bipartite graph K(4,4) contains a faithful forbidden pair.
Consequently, after selecting an edge and five further neighbors at each end,
any three unused neighbors on each side include a missing cross edge.
This supports a matching-selection step, not a cycle-lifting theorem.
-/

open SimpleGraph Finset
namespace Erdos585.BipartiteObstruction

def K44 : SimpleGraph (Fin 4 ⊕ Fin 4) :=
  .fromRel fun x y => x.isLeft ≠ y.isLeft

instance : DecidableRel K44.Adj := inferInstanceAs (DecidableRel (SimpleGraph.fromRel _).Adj)

def red : K44.Walk (.inl 0) (.inl 0) :=
  .cons (v := .inr 0) (by decide) (.cons (v := .inl 1) (by decide)
    (.cons (v := .inr 1) (by decide) (.cons (v := .inl 2) (by decide)
    (.cons (v := .inr 2) (by decide) (.cons (v := .inl 3) (by decide)
    (.cons (v := .inr 3) (by decide) (.cons (by decide) .nil)))))))

def blue : K44.Walk (.inl 0) (.inl 0) :=
  .cons (v := .inr 1) (by decide) (.cons (v := .inl 3) (by decide)
    (.cons (v := .inr 0) (by decide) (.cons (v := .inl 2) (by decide)
    (.cons (v := .inr 3) (by decide) (.cons (v := .inl 1) (by decide)
    (.cons (v := .inr 2) (by decide) (.cons (by decide) .nil)))))))

lemma red_isCycle : red.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  exact ⟨by decide, by simp [red], by decide⟩

lemma blue_isCycle : blue.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  exact ⟨by decide, by simp [blue], by decide⟩

theorem hasPair_K44 : HasPairF K44 :=
  ⟨_, _, red, blue, red_isCycle, blue_isCycle, by decide, by decide⟩

theorem hasPair_of_biclique_four {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (L R : Fin 4 → V)
    (hL : Function.Injective L) (hR : Function.Injective R)
    (hLR : ∀ i j, L i ≠ R j) (hE : ∀ i j, G.Adj (L i) (R j)) : HasPairF G := by
  let f : K44 →g G := {
    toFun := Sum.elim L R
    map_rel' := by
      intro x y hxy
      rcases x with x | x <;> rcases y with y | y
      · simp [K44] at hxy
      · exact hE x y
      · exact (hE y x).symm
      · simp [K44] at hxy }
  apply hasPair_K44.map f
  intro x y hxy
  rcases x with x | x <;> rcases y with y | y
  · exact congrArg Sum.inl (hL hxy)
  · exact False.elim (hLR x y hxy)
  · exact False.elim (hLR y x hxy.symm)
  · exact congrArg Sum.inr (hR hxy)

private def insertFirst {V : Type*} (v : V) (f : Fin 3 → V) : Fin 4 → V :=
  Fin.cases v f

private lemma insertFirst_injective {V : Type*} (v : V) (f : Fin 3 → V)
    (hf : Function.Injective f) (hv : ∀ i, v ≠ f i) :
    Function.Injective (insertFirst v f) := by
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · intro _; rfl
    · intro hij; exact False.elim (hv j hij)
  · intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · intro hij; exact False.elim (hv i hij.symm)
    · intro hij; exact congrArg Fin.succ (hf hij)

theorem missing_cross_edge {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (hG : ¬ HasPairF G) (L R : Fin 6 → V)
    (hL : Function.Injective L) (hR : Function.Injective R)
    (hLR : ∀ i j, L i ≠ R j)
    (hleft : ∀ j, G.Adj (L 0) (R j)) (hright : ∀ i, G.Adj (L i) (R 0))
    (A B : Finset (Fin 5)) (hA : 3 ≤ A.card) (hB : 3 ≤ B.card) :
    ∃ a ∈ A, ∃ b ∈ B, ¬ G.Adj (L a.succ) (R b.succ) := by
  classical
  by_contra! hall
  obtain ⟨a⟩ := Function.Embedding.nonempty_of_card_le
    (show Fintype.card (Fin 3) ≤ Fintype.card A by simpa using hA)
  obtain ⟨b⟩ := Function.Embedding.nonempty_of_card_le
    (show Fintype.card (Fin 3) ≤ Fintype.card B by simpa using hB)
  let l : Fin 3 → V := fun i => L (a i).val.succ
  let r : Fin 3 → V := fun i => R (b i).val.succ
  have hl : Function.Injective l := fun i j hij =>
    a.injective (Subtype.ext (Fin.succ_inj.mp (hL hij)))
  have hr : Function.Injective r := fun i j hij =>
    b.injective (Subtype.ext (Fin.succ_inj.mp (hR hij)))
  apply hG (hasPair_of_biclique_four G (insertFirst (L 0) l) (insertFirst (R 0) r)
    (insertFirst_injective _ _ hl (fun i he => Fin.succ_ne_zero _ (hL he).symm))
    (insertFirst_injective _ _ hr (fun i he => Fin.succ_ne_zero _ (hR he).symm)) ?_ ?_)
  · intro i j
    refine Fin.cases ?_ (fun i => ?_) i <;>
      refine Fin.cases ?_ (fun j => ?_) j <;> apply hLR
  · intro i j
    refine Fin.cases ?_ (fun i => ?_) i
    · refine Fin.cases ?_ (fun j => ?_) j
      · exact hleft 0
      · exact hleft _
    · refine Fin.cases ?_ (fun j => ?_) j
      · exact hright _
      · exact hall _ (a i).property _ (b j).property

private def tripleEmbedding (a b c : Fin 5) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) : Fin 3 ↪ Fin 5 where
  toFun := ![a,b,c]
  inj' := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all

/-- Three missing cross edges can be chosen with distinct endpoints at both ends. -/
theorem missing_matching_three {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (hG : ¬ HasPairF G) (L R : Fin 6 → V)
    (hL : Function.Injective L) (hR : Function.Injective R)
    (hLR : ∀ i j, L i ≠ R j)
    (hleft : ∀ j, G.Adj (L 0) (R j)) (hright : ∀ i, G.Adj (L i) (R 0)) :
    ∃ a b : Fin 3 ↪ Fin 5, ∀ i, ¬ G.Adj (L (a i).succ) (R (b i).succ) := by
  classical
  obtain ⟨a₀, _, b₀, _, h₀⟩ := missing_cross_edge G hG L R hL hR hLR hleft hright
    univ univ (by decide) (by decide)
  obtain ⟨a₁, ha₁, b₁, hb₁, h₁⟩ := missing_cross_edge G hG L R hL hR hLR hleft hright
    (univ.erase a₀) (univ.erase b₀) (by simp) (by simp)
  have ha10 : a₁ ≠ a₀ := (mem_erase.mp ha₁).1
  have hb10 : b₁ ≠ b₀ := (mem_erase.mp hb₁).1
  obtain ⟨a₂, ha₂, b₂, hb₂, h₂⟩ := missing_cross_edge G hG L R hL hR hLR hleft hright
    ((univ.erase a₀).erase a₁) ((univ.erase b₀).erase b₁)
    (by simp [ha10]) (by simp [hb10])
  have ha21 : a₂ ≠ a₁ := (mem_erase.mp ha₂).1
  have ha20 : a₂ ≠ a₀ := (mem_erase.mp (mem_erase.mp ha₂).2).1
  have hb21 : b₂ ≠ b₁ := (mem_erase.mp hb₂).1
  have hb20 : b₂ ≠ b₀ := (mem_erase.mp (mem_erase.mp hb₂).2).1
  refine ⟨tripleEmbedding a₀ a₁ a₂ ha10.symm ha20.symm ha21.symm,
    tripleEmbedding b₀ b₁ b₂ hb10.symm hb20.symm hb21.symm, ?_⟩
  intro i
  fin_cases i
  · exact h₀
  · exact h₁
  · exact h₂

end Erdos585.BipartiteObstruction
