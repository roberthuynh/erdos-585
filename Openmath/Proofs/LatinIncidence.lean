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
import Openmath.Proofs.IncidenceHubs

/-! # Two hubs joined to a linear triple-incidence graph -/
open SimpleGraph Finset
namespace Erdos585.LatinIncidence

variable {L P : Type*} [Fintype L] [Fintype P] [DecidableEq L] [DecidableEq P]
    (r : L → P → Prop) [DecidableRel r]

def rightAdj (x : L) : P ⊕ Fin 2 → Prop | .inl p => r x p | .inr _ => True

def graph : SimpleGraph (L ⊕ (P ⊕ Fin 2)) where
  Adj a b := match a,b with
    | .inl x, .inr y => rightAdj r x y
    | .inr y, .inl x => rightAdj r x y
    | _, _ => False
  symm := ⟨by intro a b h; cases a <;> cases b <;> exact h⟩
  loopless := ⟨by intro a; cases a <;> simp⟩

instance : DecidableRel (graph r).Adj := by
  intro a b
  cases a with
  | inl x => cases b with
    | inl y => exact isFalse id
    | inr y => cases y <;> dsimp [graph,rightAdj] <;> infer_instance
  | inr x => cases b with
    | inl y => cases x <;> dsimp [graph,rightAdj] <;> infer_instance
    | inr y => exact isFalse id

def color : L ⊕ (P ⊕ Fin 2) → Bool | .inl _ => true | .inr _ => false

def pointEmbedding : P ↪ L ⊕ (P ⊕ Fin 2) :=
  ⟨fun x => .inr (.inl x), by intro a b h; simpa using h⟩
def hubEmbedding : Fin 2 ↪ L ⊕ (P ⊕ Fin 2) :=
  ⟨fun x => .inr (.inr x), by intro a b h; simpa using h⟩

@[simp] lemma pointEmbedding_apply (x : P) :
    (pointEmbedding : P ↪ L ⊕ (P ⊕ Fin 2)) x = .inr (.inl x) := rfl
@[simp] lemma hubEmbedding_apply (x : Fin 2) :
    (hubEmbedding : Fin 2 ↪ L ⊕ (P ⊕ Fin 2)) x = .inr (.inr x) := rfl

def hubs : Finset (L ⊕ (P ⊕ Fin 2)) := univ.map hubEmbedding

lemma outside_neighbors (x : L) :
    (univ.filter fun y => (graph r).Adj (.inl x) y ∧ y ∉ hubs) =
      (univ.filter (r x)).map pointEmbedding := by
  apply Finset.ext
  intro y
  simp only [mem_filter,mem_univ,true_and,mem_map]
  cases y with
  | inl y => simp [graph,hubs]
  | inr y => cases y <;> simp [graph,rightAdj,hubs]

/-- Linear triple incidence with two hubs avoids the forbidden pair. -/
theorem pairfree
    (hd : ∀ x, (univ.filter (r x)).card ≤ 3)
    (hs : ∀ a b, a ≠ b → ∀ x y, r x a → r x b → r y a → r y b → x = y) :
    ¬ HasPairF (graph r) := by
  apply IncidenceHubs.not_hasPair color hubs
  · intro a b ha
    cases a <;> cases b <;> simp_all [graph,color]
  · simp [hubs]
  · intro x hx
    cases x with
    | inl x => rw [outside_neighbors,card_map]; exact hd x
    | inr x => simp [color] at hx
  · intro a ha b hb hab x y hx hy hxa hxb hya hyb
    cases x with
    | inr x => simp [color] at hx
    | inl x => cases y with
      | inr y => simp [color] at hy
      | inl y =>
        cases a with
        | inl a => exact False.elim hxa
        | inr a => cases a with
          | inr a => exact False.elim (ha (mem_map.mpr ⟨a,mem_univ _,rfl⟩))
          | inl a => cases b with
            | inl b => exact False.elim hxb
            | inr b => cases b with
              | inr b => exact False.elim (hb (mem_map.mpr ⟨b,mem_univ _,rfl⟩))
              | inl b =>
                have he := hs a b (by simpa using hab) x y hxa hxb hya hyb
                exact congrArg Sum.inl he

lemma left_degree (x : L) : (graph r).degree (.inl x) = (univ.filter (r x)).card + 2 := by
  have he : (graph r).neighborFinset (.inl x) =
      ((univ.filter (r x)).disjSum (univ : Finset (Fin 2))).map Function.Embedding.inr := by
    apply Finset.ext
    intro y
    simp only [mem_neighborFinset]
    cases y with
    | inl y => simp [graph]
    | inr y => cases y <;> simp [graph,rightAdj]
  rw [← card_neighborFinset_eq_degree,he]
  simp

lemma bipartite : (graph r).IsBipartiteWith
    (↑((univ : Finset L).map (Function.Embedding.inl : L ↪ L ⊕ (P ⊕ Fin 2))))
    (↑((univ : Finset (P ⊕ Fin 2)).map (Function.Embedding.inr : P ⊕ Fin 2 ↪ L ⊕ (P ⊕ Fin 2)))) := by
  constructor
  · apply Set.disjoint_left.mpr
    intro x hx hy
    cases x <;> simp_all
  · intro a b ha
    cases a <;> cases b <;> simp_all [graph]

/-- If every left vertex belongs to a triple, the graph has five edges per left vertex. -/
theorem edge_count (hd : ∀ x, (univ.filter (r x)).card = 3) :
    (graph r).edgeFinset.card = 5 * Fintype.card L := by
  have hh := SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges (bipartite r)
  simp only [sum_map] at hh
  change (∑ x : L, (graph r).degree (.inl x)) = _ at hh
  simp_rw [left_degree,hd] at hh
  simpa [mul_comm] using hh.symm


section Latin
variable {A : Type*} [Fintype A] [DecidableEq A] [AddCancelCommMonoid A]

/-- Triples from the addition table of a finite cancellative commutative monoid. -/
def triple (x : A × A) (p : Fin 3 × A) : Prop :=
  p = (0,x.1) ∨ p = (1,x.2) ∨ p = (2,x.1+x.2)
instance : DecidableRel (triple (A := A)) := by unfold triple; infer_instance

lemma triple_degree (x : A × A) : (univ.filter (triple x)).card = 3 := by
  have he : univ.filter (triple x) = {(0,x.1),(1,x.2),(2,x.1+x.2)} := by
    apply Finset.ext
    intro p
    simp only [mem_filter,mem_univ,true_and,triple,mem_insert,mem_singleton]
  rw [he]
  simp

lemma triple_linear (a b : Fin 3 × A) (hab : a ≠ b) (x y : A × A)
    (hxa : triple x a) (hxb : triple x b) (hya : triple y a) (hyb : triple y b) : x = y := by
  rcases x with ⟨x₁,x₂⟩
  rcases y with ⟨y₁,y₂⟩
  rcases hxa with rfl | rfl | rfl <;> rcases hxb with rfl | rfl | rfl <;>
    simp_all [triple,Prod.ext_iff]

/-- The incidence construction from a Latin square is pair-free. -/
theorem latin_pairfree : ¬ HasPairF (graph (triple (A := A))) :=
  pairfree _ (fun x => (triple_degree x).le) triple_linear

/-- Its exact edge count is five times the square of the alphabet size. -/
theorem latin_edge_count : (graph (triple (A := A))).edgeFinset.card =
    5 * (Fintype.card A)^2 := by
  rw [edge_count _ triple_degree]
  simp [pow_two]

end Latin

/-- A second explicit linear family, with coefficient tending to five. -/
theorem five_mul_sq_le (m : ℕ) : 5*m^2 ≤ maxEdges (m^2+3*m+2) := by
  by_cases hm : m = 0
  · simp [hm]
  haveI : NeZero m := ⟨hm⟩
  have hc : Fintype.card ((ZMod m × ZMod m) ⊕ ((Fin 3 × ZMod m) ⊕ Fin 2)) =
      m^2+3*m+2 := by simp [pow_two]; omega
  have hh := card_edges_le_maxEdges (graph (triple (A := ZMod m))) latin_pairfree hc
  rw [latin_edge_count] at hh
  simpa using hh


/-- Any selected set of Latin triples gives five edges per selected left vertex. -/
theorem partial_latin_lower_bound (m p : ℕ) (hm : 0 < m) (hp : p ≤ m^2) :
    5*p ≤ maxEdges (p+3*m+2) := by
  classical
  have : NeZero m := ⟨by omega⟩
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le
    (show Fintype.card (Fin p) ≤ Fintype.card (ZMod m × ZMod m) by simpa [pow_two] using hp)
  let rel := fun x : Fin p => triple (f x)
  have hd : ∀ x, (univ.filter (rel x)).card = 3 := fun x => triple_degree (f x)
  have hs : ∀ a b, a ≠ b → ∀ x y, rel x a → rel x b → rel y a → rel y b → x = y := by
    intro a b hab x y hxa hxb hya hyb
    exact f.injective (triple_linear a b hab (f x) (f y) hxa hxb hya hyb)
  have hf := pairfree rel (fun x => (hd x).le) hs
  have hc : Fintype.card (Fin p ⊕ ((Fin 3 × ZMod m) ⊕ Fin 2)) = p+3*m+2 := by
    simp; omega
  have hh := card_edges_le_maxEdges (graph rel) hf hc
  rw [edge_count rel hd] at hh
  simpa using hh

/-- A uniform bound approaching five edges per vertex. -/
theorem five_mul_sub_sqrt_le (n : ℕ) (hn : 16 ≤ n) :
    5*n - 15*Nat.sqrt n - 10 ≤ maxEdges n := by
  let m := Nat.sqrt n
  have hm4 : 4 ≤ m := by
    exact (Nat.le_sqrt).mpr (by omega)
  have hsq : m*m ≤ n := Nat.sqrt_le n
  have hnext : n < (m+1)*(m+1) := Nat.lt_succ_sqrt n
  have hfit : 3*m+2 ≤ n := by nlinarith
  have hsum : n-3*m-2+3*m+2 = n := by omega
  have hcap : n-3*m-2 ≤ m^2 := by nlinarith
  have hh := partial_latin_lower_bound m (n-3*m-2) (by omega) hcap
  have he : n-3*m-2+3*m+2 = n := by omega
  rw [he] at hh
  omega

end Erdos585.LatinIncidence


