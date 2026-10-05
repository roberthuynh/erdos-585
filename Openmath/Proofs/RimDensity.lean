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
import Openmath.Proofs.TwoHub

/-! # Sparse rims and separated degree-two additions -/
open SimpleGraph Finset
namespace Erdos585.RimDensity

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Edges induced on a finite set, including when the ambient type is infinite. -/
def edges (S : Finset V) : Finset (Sym2 V) := S.sym2.filter (· ∈ G.edgeSet)

omit [DecidableEq V] in
@[simp] lemma mem_edges {S : Finset V} {a b : V} :
    s(a,b) ∈ edges G S ↔ a ∈ S ∧ b ∈ S ∧ G.Adj a b := by
  simp [edges, and_assoc]

def NoSquare : Prop := ∀ a b x y : V, a ≠ b → x ≠ y →
  G.Adj a x → G.Adj a y → G.Adj b x → G.Adj b y → False

lemma edges_insert (S : Finset V) (v : V) :
    edges G (insert v S) = edges G S ∪ (S.filter (G.Adj v)).image (fun x => s(v,x)) := by
  ext e
  induction e using Sym2.inductionOn with | _ a b => ?_
  constructor
  · intro he
    obtain ⟨ha,hb,hab⟩ := (mem_edges G).mp he
    rcases mem_insert.mp ha with rfl | haS
    · exact mem_union_right _ (mem_image.mpr ⟨b,
        mem_filter.mpr ⟨(mem_insert.mp hb).resolve_left (G.ne_of_adj hab).symm,hab⟩,rfl⟩)
    · rcases mem_insert.mp hb with rfl | hbS
      · exact mem_union_right _ (mem_image.mpr ⟨a,mem_filter.mpr ⟨haS,hab.symm⟩,
          Sym2.eq_swap⟩)
      · exact mem_union_left _ ((mem_edges G).mpr ⟨haS,hbS,hab⟩)
  · intro he
    rcases mem_union.mp he with he | he
    · obtain ⟨ha,hb,hab⟩ := (mem_edges G).mp he
      exact (mem_edges G).mpr ⟨mem_insert_of_mem ha,mem_insert_of_mem hb,hab⟩
    · obtain ⟨x,hx,heq⟩ := mem_image.mp he
      rw [← heq]
      exact (mem_edges G).mpr ⟨mem_insert_self _ _,mem_insert_of_mem (mem_filter.mp hx).1,
        (mem_filter.mp hx).2⟩

lemma edges_insert_card (S : Finset V) (v : V) (hv : v ∉ S) :
    (edges G (insert v S)).card = (edges G S).card + (S.filter (G.Adj v)).card := by
  rw [edges_insert, card_union_of_disjoint]
  · congr 1
    apply card_image_of_injective
    intro a b hab
    have h : a = b ∨ v = b ∧ a = v := by simpa using hab
    exact h.elim id (fun h => h.2.trans h.1)
  · apply Finset.disjoint_left.mpr
    intro e he hf
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hf
    exact hv ((mem_edges G).mp he).1

omit [DecidableEq V] in
lemma edges_map {W : Type*} [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj]
    (f : V ↪ W) (S : Finset V) :
    edges H (S.map f) = (edges (H.comap f) S).map f.sym2Map := by
  unfold edges
  rw [sym2_map, filter_map]
  congr 1
  ext e
  induction e using Sym2.inductionOn with | _ a b => simp

omit [DecidableEq V] in
lemma finite_model {S : Finset V} (hS : S.card = 4) :
    ∃ f : Fin 4 ↪ V, univ.map f = S := by
  let e : Fin 4 ≃ (↑S : Set V) := (Fintype.equivFinOfCardEq (by simpa using hS)).symm
  let f : Fin 4 ↪ V := ⟨fun x => (e x).val, Subtype.val_injective.comp e.injective⟩
  refine ⟨f, ?_⟩
  ext x
  constructor
  · intro hx
    obtain ⟨y,_,rfl⟩ := mem_map.mp hx
    exact (e y).property
  · intro hx
    exact mem_map.mpr ⟨e.symm ⟨x,hx⟩,mem_univ _,by simp [f]⟩

/-- A computable encoding of all graphs on four labeled vertices. -/
def small (b : Fin 6 → Bool) : SimpleGraph (Fin 4) := .fromRel fun x y =>
  (x = 0 ∧ y = 1 ∧ b 0 = true) ∨ (x = 0 ∧ y = 2 ∧ b 1 = true) ∨
  (x = 0 ∧ y = 3 ∧ b 2 = true) ∨ (x = 1 ∧ y = 2 ∧ b 3 = true) ∨
  (x = 1 ∧ y = 3 ∧ b 4 = true) ∨ (x = 2 ∧ y = 3 ∧ b 5 = true)

instance (b : Fin 6 → Bool) : DecidableRel (small b).Adj := by
  intro a c
  dsimp [small, SimpleGraph.fromRel]
  infer_instance

set_option synthInstance.maxSize 2048 in
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
lemma small_bounds : ∀ b : Fin 6 → Bool,
    (NoSquare (small b) → (edges (small b) univ).card ≤ 4) ∧
    (∀ a c : Fin 4, a ≠ c → ¬ (small b).Adj a c →
      (∀ x, ¬ ((small b).Adj a x ∧ (small b).Adj c x)) →
      (edges (small b) univ).card ≤ 3) := by
  have test : ∀ b0 b1 b2 b3 b4 b5 : Bool,
      let H := small ![b0,b1,b2,b3,b4,b5]
      (NoSquare H → (edges H univ).card ≤ 4) ∧
      (∀ a c : Fin 4, a ≠ c → ¬ H.Adj a c →
        (∀ x, ¬ (H.Adj a x ∧ H.Adj c x)) → (edges H univ).card ≤ 3) := by
    intro b0 b1 b2 b3 b4 b5
    cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;>
      dsimp only <;> unfold NoSquare <;> decide
  intro b
  have hb : b = ![b 0,b 1,b 2,b 3,b 4,b 5] := by
    funext i
    fin_cases i <;> rfl
  rw [hb]
  exact test _ _ _ _ _ _


lemma small_representation (H : SimpleGraph (Fin 4)) [DecidableRel H.Adj] :
    ∃ b, small b = H := by
  refine ⟨![decide (H.Adj 0 1),decide (H.Adj 0 2),decide (H.Adj 0 3),
    decide (H.Adj 1 2),decide (H.Adj 1 3),decide (H.Adj 2 3)], ?_⟩
  ext a b
  fin_cases a <;> fin_cases b <;> simp [small, SimpleGraph.fromRel_adj, adj_comm] <;> exact H.adj_comm 0 1

lemma four_bounds {S : Finset V} (hS : S.card = 4) :
    (NoSquare G → (edges G S).card ≤ 4) ∧
    (∀ a ∈ S, ∀ b ∈ S, a ≠ b → ¬ G.Adj a b →
      (∀ x ∈ S, ¬ (G.Adj a x ∧ G.Adj b x)) → (edges G S).card ≤ 3) := by
  classical
  obtain ⟨f,hf⟩ := finite_model hS
  let H := G.comap f
  obtain ⟨bits,hbits⟩ := small_representation H
  have hb := small_bounds bits
  simp only [hbits] at hb
  have hc : (edges H univ).card = (edges G S).card := by
    rw [← hf, edges_map, card_map]
  constructor
  · intro hs
    rw [← hc]
    apply hb.1
    intro a b x y hab hxy hax hay hbx hby
    exact hs (f a) (f b) (f x) (f y) (f.injective.ne hab) (f.injective.ne hxy)
      hax hay hbx hby
  · intro a ha b hbS hab hn hfar
    rw [← hf] at ha hbS
    obtain ⟨a,_,rfl⟩ := mem_map.mp ha
    obtain ⟨b,_,rfl⟩ := mem_map.mp hbS
    rw [← hc]
    apply hb.2 a b (fun h => hab (congrArg f h)) hn
    intro x
    exact hfar (f x) (hf ▸ mem_map.mpr ⟨x,mem_univ _,rfl⟩)

set_option synthInstance.maxSize 2048 in
set_option maxRecDepth 32768 in
lemma small_low_degree : ∀ b : Fin 6 → Bool, NoSquare (small b) →
    ∃ x, (univ.filter ((small b).Adj x)).card ≤ 1 := by
  have test : ∀ b0 b1 b2 b3 b4 b5 : Bool,
      let H := small ![b0,b1,b2,b3,b4,b5]
      NoSquare H → ∃ x, (univ.filter (H.Adj x)).card ≤ 1 := by
    intro b0 b1 b2 b3 b4 b5
    cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;>
      dsimp only <;> unfold NoSquare <;> decide
  intro b
  have hb : b = ![b 0,b 1,b 2,b 3,b 4,b 5] := by
    funext i
    fin_cases i <;> rfl
  rw [hb]
  exact test _ _ _ _ _ _

lemma four_low_degree {S : Finset V} (hS : S.card = 4) (hs : NoSquare G) :
    ∃ x ∈ S, (S.filter (G.Adj x)).card ≤ 1 := by
  classical
  obtain ⟨f,hf⟩ := finite_model hS
  let H := G.comap f
  obtain ⟨bits,hbits⟩ := small_representation H
  have hb := small_low_degree bits
  simp only [hbits] at hb
  have hsq : NoSquare H := by
    intro a b x y hab hxy hax hay hbx hby
    exact hs (f a) (f b) (f x) (f y) (f.injective.ne hab) (f.injective.ne hxy)
      hax hay hbx hby
  obtain ⟨a,ha⟩ := hb hsq
  refine ⟨f a, hf ▸ mem_map.mpr ⟨a,mem_univ _,rfl⟩, ?_⟩
  rw [← hf, filter_map, card_map]
  exact ha

end Erdos585.RimDensity
