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
import Openmath.Proofs.RimStrip
import Openmath.Proofs.SmallExact

/-! # Uniform two-hub graphs with four edges per vertex minus thirteen -/
open SimpleGraph Finset
namespace Erdos585.TwoHubFamily

variable {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]

/-- Adjoin two independent vertices, each adjacent to the entire rim. -/
def cone : SimpleGraph (V ⊕ Fin 2) where
  Adj a b := match a,b with
    | .inl x, .inl y => H.Adj x y
    | .inl _, .inr _ => True
    | .inr _, .inl _ => True
    | .inr _, .inr _ => False
  symm := ⟨by intro a b h; cases a <;> cases b <;> simp_all [H.adj_comm]⟩
  loopless := ⟨by intro a; cases a <;> simp⟩

instance : DecidableRel (cone H).Adj := by
  intro a b
  cases a <;> cases b <;> dsimp [cone] <;> infer_instance

def color : V ⊕ Fin 2 → Bool | .inl _ => true | .inr _ => false

lemma comap_inl : (cone H).comap Function.Embedding.inl = H := by ext a b; rfl

lemma rim_set {R : Finset (V ⊕ Fin 2)} (hR : ∀ x ∈ R, color x = true) :
    R.toLeft.map Function.Embedding.inl = R := by
  ext x
  cases x with
  | inl x => simp
  | inr x =>
    have hn : Sum.inr x ∉ R := fun hx => Bool.false_ne_true (hR _ hx)
    simp [hn]

lemma inside_eq_edges (R : Finset V) :
    DensityCore.inside H R = RimDensity.edges H R := by
  ext e
  induction e using Sym2.inductionOn with | _ a b => simp [DensityCore.inside, RimDensity.edges, and_comm]

lemma rim_edge_count (R : Finset V) :
    (DensityCore.inside (cone H) (R.map Function.Embedding.inl)).card =
      (RimDensity.edges H R).card := by
  rw [inside_eq_edges, RimDensity.edges_map]
  simp only [comap_inl, card_map]

lemma rim_neighbor_count (R : Finset V) (x : V) :
    ((R.map Function.Embedding.inl).filter ((cone H).Adj (.inl x))).card =
      (R.filter (H.Adj x)).card := by
  rw [filter_map]
  simp only [card_map]
  rfl

/-- A square-free sparse rim certifies that its two-hub cone has no forbidden pair. -/
theorem pairfree (h4 : RimDensity.NoSquare H)
    (hs : ∀ R : Finset V, 5 ≤ R.card → (RimDensity.edges H R).card + 5 ≤ 2 * R.card) :
    ¬ HasPairF (cone H) := by
  apply TwoHub.not_hasPair color
  · intro a b hab
    cases a <;> cases b <;> simp_all [color,cone]
  · have he : ((univ : Finset (V ⊕ Fin 2)).filter fun x => color x = false) =
        (univ : Finset (Fin 2)).map Function.Embedding.inr := by
      apply Finset.ext
      intro x
      simp only [mem_filter, mem_univ, true_and]
      cases x <;> simp [color]
    rw [he]
    simp
  · intro R hR hcard hdeg
    have he := rim_set hR
    rw [← he, card_map] at hcard
    rw [← he, rim_edge_count, card_map]
    by_cases h5 : 5 ≤ R.toLeft.card
    · have hh := hs R.toLeft h5
      omega
    have hfour : R.toLeft.card = 4 := by omega
    obtain ⟨x,hx,hd⟩ := RimDensity.four_low_degree H hfour h4
    have hxR : Sum.inl x ∈ R := mem_toLeft.mp hx
    have hh := hdeg _ hxR
    rw [← he, rim_neighbor_count] at hh
    omega

lemma rim_degree (x : V) : (cone H).degree (.inl x) = H.degree x + 2 := by
  have he : (cone H).neighborFinset (.inl x) = (H.neighborFinset x).disjSum univ := by
    ext y
    cases y <;> simp only [mem_neighborFinset] <;> simp [cone]
  rw [← card_neighborFinset_eq_degree, he, card_disjSum]
  simp

lemma hub_degree (x : Fin 2) : (cone H).degree (.inr x) = Fintype.card V := by
  have he : (cone H).neighborFinset (.inr x) =
      (univ : Finset V).map Function.Embedding.inl := by
    ext y
    cases y <;> simp only [mem_neighborFinset] <;> simp [cone]
  rw [← card_neighborFinset_eq_degree, he]
  simp

/-- The two hubs contribute exactly twice the number of rim vertices. -/
theorem edge_count : (cone H).edgeFinset.card = H.edgeFinset.card + 2 * Fintype.card V := by
  have hh := (cone H).sum_degrees_eq_twice_card_edges
  simp only [Fintype.sum_sum_type, rim_degree, hub_degree, sum_add_distrib,
    H.sum_degrees_eq_twice_card_edges, sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at hh
  omega

/-- The first `t` vertices of the explicit infinite strip. -/
def rim (t : ℕ) : SimpleGraph (Fin t) := RimStrip.graph.comap Fin.val
instance (t : ℕ) : DecidableRel (rim t).Adj := inferInstanceAs
  (DecidableRel (RimStrip.graph.comap Fin.val).Adj)

def valEmbedding (t : ℕ) : Fin t ↪ ℕ := ⟨Fin.val, Fin.val_injective⟩

lemma rim_edges (t : ℕ) (R : Finset (Fin t)) :
    (RimDensity.edges (rim t) R).card =
      (RimDensity.edges RimStrip.graph (R.map (valEmbedding t))).card := by
  rw [RimDensity.edges_map, card_map]
  rfl

lemma rim_no_square (t : ℕ) : RimDensity.NoSquare (rim t) := by
  intro a b x y hab hxy hax hay hbx hby
  exact RimStrip.no_square a.val b.val x.val y.val
    (fun h => hab (Fin.ext h)) (fun h => hxy (Fin.ext h)) hax hay hbx hby

lemma rim_sparse (t : ℕ) (R : Finset (Fin t)) (hR : 5 ≤ R.card) :
    (RimDensity.edges (rim t) R).card + 5 ≤ 2 * R.card := by
  rw [rim_edges]
  simpa using RimStrip.sparse (R.map (valEmbedding t)) (by simpa using hR)

/-- The uniform family has a kernel-checked forbidden-pair exclusion. -/
theorem family_pairfree (t : ℕ) : ¬ HasPairF (cone (rim t)) :=
  pairfree (rim t) (rim_no_square t) (rim_sparse t)

lemma rim_edge_count_formula (t : ℕ) (ht : 8 ≤ t) : (rim t).edgeFinset.card + 5 = 2*t := by
  have he : (univ : Finset (Fin t)).map (valEmbedding t) = range t := by
    ext x
    simp only [mem_map, mem_univ, true_and, mem_range]
    exact ⟨fun ⟨y,hy⟩ => hy ▸ y.isLt, fun hx => ⟨⟨x,hx⟩,rfl⟩⟩
  have hi : RimDensity.edges (rim t) univ = (rim t).edgeFinset := by
    ext e
    induction e using Sym2.inductionOn with | _ a b => simp
  have hh := rim_edges t univ
  rw [hi,he] at hh
  rw [hh]
  exact RimStrip.edge_count t ht

/-- The family on `t + 2` vertices has exactly `4 * t - 5` edges. -/
theorem family_edge_count (t : ℕ) (ht : 8 ≤ t) :
    (cone (rim t)).edgeFinset.card + 5 = 4*t := by
  rw [edge_count]
  have h := rim_edge_count_formula t ht
  simp only [Fintype.card_fin]
  omega

/-- A uniform explicit lower bound, with no assertion of novelty. -/
theorem four_mul_sub_thirteen_le (n : ℕ) (hn : 10 ≤ n) : 4*n-13 ≤ maxEdges n := by
  have ht : 8 ≤ n-2 := by omega
  have hc : Fintype.card (Fin (n-2) ⊕ Fin 2) = n := by simp; omega
  have hh := card_edges_le_maxEdges (cone (rim (n-2))) (family_pairfree (n-2)) hc
  have he := family_edge_count (n-2) ht
  omega

end Erdos585.TwoHubFamily
