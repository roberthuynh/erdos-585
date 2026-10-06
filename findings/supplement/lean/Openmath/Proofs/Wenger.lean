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
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
import Mathlib.Tactic
import FormalConjecturesUtil.Linters.ModuleDocstringLinter

/-! # The standard Wenger graph W₂ over a field

Points `(a,b,c)` and lines `(x,y,z)` satisfy `y+b=x*a`, `z+c=x*b`.
This is the usual recursive equation representation of W₂ with its shores
exchanged. The six-cycle obstruction below is a characteristic-free
Vandermonde calculation on actual vertices and edges, not a girth axiom.
-/

namespace Erdos585.Wenger
open SimpleGraph Finset

variable (K : Type*)
abbrev Coord := K × K × K
abbrev Vertex := Coord K × Bool

variable {K} [Field K]

def Incident (P L : Coord K) : Prop :=
  L.2.1 + P.2.1 = L.1 * P.1 ∧ L.2.2 + P.2.2 = L.1 * P.2.1

instance [DecidableEq K] (P L : Coord K) : Decidable (Incident P L) :=
  inferInstanceAs (Decidable (_ ∧ _))

def graph : SimpleGraph (Vertex K) where
  Adj u v :=
    (u.2 = false ∧ v.2 = true ∧ Incident u.1 v.1) ∨
    (v.2 = false ∧ u.2 = true ∧ Incident v.1 u.1)
  symm := ⟨fun _ _ h => h.elim Or.inr Or.inl⟩
  loopless := ⟨by
    intro x h
    rcases h with h | h <;> exact Bool.false_ne_true (h.1.symm.trans h.2.1)⟩

instance [DecidableEq K] : DecidableRel (graph (K := K)).Adj := fun _ _ =>
  inferInstanceAs (Decidable (_ ∨ _))

@[simp] theorem graph_cross (P L : Coord K) :
    (graph (K := K)).Adj (P, false) (L, true) ↔ Incident P L := by
  simp [graph]

@[simp] theorem graph_same (P L : Coord K) (b : Bool) :
    ¬ (graph (K := K)).Adj (P, b) (L, b) := by
  cases b <;> simp [graph]

theorem graph_bipartite : (graph (K := K)).IsBipartite := by
  refine ⟨⟨fun x => if x.2 then 1 else 0, ?_⟩⟩
  intro x y hxy
  rcases hxy with hxy | hxy <;> simp [hxy.1, hxy.2.1]

theorem point_eq_of_first_eq {P Q L : Coord K}
    (hP : Incident P L) (hQ : Incident Q L) (h : P.1 = Q.1) : P = Q := by
  have hb : P.2.1 = Q.2.1 := by linear_combination hP.1 - hQ.1 + L.1 * h
  have hc : P.2.2 = Q.2.2 := by linear_combination hP.2 - hQ.2 + L.1 * hb
  exact Prod.ext h (Prod.ext hb hc)

theorem line_eq_of_first_eq {P L M : Coord K}
    (hL : Incident P L) (hM : Incident P M) (h : L.1 = M.1) : L = M := by
  have hy : L.2.1 = M.2.1 := by linear_combination hL.1 - hM.1 + P.1 * h
  have hz : L.2.2 = M.2.2 := by linear_combination hL.2 - hM.2 + P.2.1 * h
  exact Prod.ext h (Prod.ext hy hz)

theorem point_step {P Q L : Coord K} (hP : Incident P L) (hQ : Incident Q L) :
    Q.2.1 - P.2.1 = L.1 * (Q.1 - P.1) ∧
      Q.2.2 - P.2.2 = L.1 ^ 2 * (Q.1 - P.1) := by
  constructor
  · linear_combination hQ.1 - hP.1
  · linear_combination hQ.2 - hP.2 + L.1 * (hQ.1 - hP.1)

/-- Six distinct alternating vertices cannot satisfy the six incidence equations. -/
theorem no_six_incident (P₀ P₁ P₂ L₀ L₁ L₂ : Coord K)
    (hP : P₀ ≠ P₁) (hL₀₁ : L₀ ≠ L₁) (hL₀₂ : L₀ ≠ L₂)
    (_hL₁₂ : L₁ ≠ L₂)
    (h₀ : Incident P₀ L₀) (h₁ : Incident P₁ L₀)
    (h₂ : Incident P₁ L₁) (h₃ : Incident P₂ L₁)
    (h₄ : Incident P₂ L₂) (h₅ : Incident P₀ L₂) : False := by
  have ht : P₁.1 - P₀.1 ≠ 0 := sub_ne_zero.mpr (fun h =>
    hP (point_eq_of_first_eq h₀ h₁ h.symm))
  have hx₀₁ : L₀.1 - L₁.1 ≠ 0 := sub_ne_zero.mpr (fun h =>
    hL₀₁ (line_eq_of_first_eq h₁ h₂ h))
  have hx₀₂ : L₀.1 - L₂.1 ≠ 0 := sub_ne_zero.mpr (fun h =>
    hL₀₂ (line_eq_of_first_eq h₀ h₅ h))
  have s₀ := point_step h₀ h₁
  have s₁ := point_step h₂ h₃
  have s₂ := point_step h₄ h₅
  have hpoly : (L₀.1 - L₁.1) * (L₀.1 - L₂.1) * (P₁.1 - P₀.1) = 0 := by
    linear_combination
      -(s₀.2 + s₁.2 + s₂.2) + (L₁.1 + L₂.1) * (s₀.1 + s₁.1 + s₂.1)
  exact (mul_ne_zero (mul_ne_zero hx₀₁ hx₀₂) ht) hpoly

/-- The actual graph has no six-vertex simple cyclic configuration, regardless of shore names. -/
theorem no_six_cycle (x₀ x₁ x₂ x₃ x₄ x₅ : Vertex K)
    (hd : [x₀, x₁, x₂, x₃, x₄, x₅].Nodup)
    (h₀ : graph.Adj x₀ x₁) (h₁ : graph.Adj x₁ x₂)
    (h₂ : graph.Adj x₂ x₃) (h₃ : graph.Adj x₃ x₄)
    (h₄ : graph.Adj x₄ x₅) (h₅ : graph.Adj x₅ x₀) : False := by
  rcases x₀ with ⟨P₀, b₀⟩
  rcases x₁ with ⟨P₁, b₁⟩
  rcases x₂ with ⟨P₂, b₂⟩
  rcases x₃ with ⟨P₃, b₃⟩
  rcases x₄ with ⟨P₄, b₄⟩
  rcases x₅ with ⟨P₅, b₅⟩
  cases b₀ <;> cases b₁ <;> cases b₂ <;> cases b₃ <;> cases b₄ <;> cases b₅ <;>
    simp_all [graph, List.nodup_cons]
  · exact no_six_incident P₀ P₂ P₄ P₁ P₃ P₅ (by aesop) (by aesop)
      (by aesop) (by aesop) h₀ h₁ h₂ h₃ h₄ h₅
  · exact no_six_incident P₁ P₃ P₅ P₂ P₄ P₀ (by aesop) (by aesop)
      (by aesop) (by aesop) h₁ h₂ h₃ h₄ h₅ h₀

section Finite
variable [Fintype K] [DecidableEq K]

omit [Field K] [DecidableEq K] in
theorem card_vertex : Fintype.card (Vertex K) = 2 * Fintype.card K ^ 3 := by
  simp only [Vertex, Coord, Fintype.card_prod, Fintype.card_bool]
  ring

theorem degree_false (P : Coord K) : graph.degree (P, false) = Fintype.card K := by
  rw [← card_neighborFinset_eq_degree, ← Finset.card_univ (α := K)]
  symm
  apply Finset.card_bij (fun x _ => ((x, x * P.1 - P.2.1, x * P.2.1 - P.2.2), true))
  · intro x _
    simp [Incident]
  · intro x _ y _ h
    exact congrArg (fun v : Vertex K => v.1.1) h
  · rintro ⟨L, b⟩ hL
    cases b
    · simp at hL
    · have h := (graph_cross P L).mp ((mem_neighborFinset _ _ _).mp hL)
      refine ⟨L.1, mem_univ _, ?_⟩
      have hy : L.1 * P.1 - P.2.1 = L.2.1 := by linear_combination -h.1
      have hz : L.1 * P.2.1 - P.2.2 = L.2.2 := by linear_combination -h.2
      simp [hy, hz]

theorem degree_true (L : Coord K) : graph.degree (L, true) = Fintype.card K := by
  rw [← card_neighborFinset_eq_degree, ← Finset.card_univ (α := K)]
  symm
  apply Finset.card_bij (fun a _ => ((a, L.1 * a - L.2.1,
    L.1 * (L.1 * a - L.2.1) - L.2.2), false))
  · intro a _
    apply (mem_neighborFinset _ _ _).mpr
    apply Adj.symm
    rw [graph_cross]
    simp [Incident]
  · intro a _ b _ h
    exact congrArg (fun v : Vertex K => v.1.1) h
  · rintro ⟨P, b⟩ hP
    cases b
    · have h := (graph_cross P L).mp ((mem_neighborFinset _ _ _).mp hP).symm
      refine ⟨P.1, mem_univ _, ?_⟩
      have hb : L.1 * P.1 - L.2.1 = P.2.1 := by linear_combination -h.1
      have hc : L.1 * P.2.1 - L.2.2 = P.2.2 := by linear_combination -h.2
      simp [hb, hc]
    · simp at hP

theorem degree_eq (x : Vertex K) : graph.degree x = Fintype.card K := by
  obtain ⟨x, b⟩ := x
  cases b
  · exact degree_false x
  · exact degree_true x

theorem card_edges : (graph (K := K)).edgeFinset.card = Fintype.card K ^ 4 := by
  have h := (graph (K := K)).sum_degrees_eq_twice_card_edges
  simp only [degree_eq, sum_const, card_univ, smul_eq_mul, card_vertex] at h
  have hp : 2 * Fintype.card K ^ 3 * Fintype.card K = 2 * Fintype.card K ^ 4 := by ring
  omega

end Finite
end Erdos585.Wenger
