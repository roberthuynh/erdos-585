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
import Openmath.Proofs.CutGluing

/-!
# A bipartite five-regular graph without a forbidden cycle pair

Eight copies of a 13-vertex bipartite block are joined by 20 edges. The block is built from
`K_{3,3}` by adding seven vertices of degree three, so it has no pair. The copies are grouped by
edge cuts of sizes two and three, so every pair would lie inside one copy.
The construction is not a novelty claim.
-/

open SimpleGraph Finset
namespace Erdos585.BipartiteFive

set_option maxRecDepth 8192
set_option maxHeartbeats 20000000

/-- Removing the last vertex when it has degree at most three: if the rest maps into a pair-free
graph, the whole graph is pair-free. -/
theorem peel_last {n : ℕ} (G : SimpleGraph (Fin (n + 1))) (H : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hdeg : G.degree (Fin.last n) ≤ 3)
    (hadj : ∀ i j : Fin n, G.Adj i.castSucc j.castSucc → H.Adj i j)
    (hH : ¬ HasPairF H) : ¬ HasPairF G := by
  rintro ⟨u, w, p, q, hp, hq, hS, hE⟩
  have hlast : Fin.last n ∉ p.support :=
    not_mem_support_of_degree_le_three hp hq hS hE hdeg
  have hlast' : Fin.last n ∉ q.support := by
    rwa [← List.mem_toFinset, ← hS, List.mem_toFinset]
  have hps : ∀ x ∈ p.support, x ∈ {x : Fin (n + 1) | x ≠ Fin.last n} := by
    rintro x hx rfl
    exact hlast hx
  have hqs : ∀ x ∈ q.support, x ∈ {x : Fin (n + 1) | x ≠ Fin.last n} := by
    rintro x hx rfl
    exact hlast' hx
  have h1 := (pair_map_iff (Embedding.induce {x : Fin (n + 1) | x ≠ Fin.last n}).toHom
    (Embedding.induce (G := G) _).injective (p.induce _ hps) (q.induce _ hqs)).1
    (by rw [Walk.map_induce, Walk.map_induce]; exact ⟨hp, hq, hS, hE⟩)
  let pull : G.induce {x : Fin (n + 1) | x ≠ Fin.last n} →g H :=
    { toFun := fun x => x.1.castPred x.2
      map_rel' := fun {x y} h => by
        have h' := induce_adj.1 h
        rw [← Fin.castSucc_castPred x.1 x.2, ← Fin.castSucc_castPred y.1 y.2] at h'
        exact hadj _ _ h' }
  have hinj : Function.Injective pull := fun x y h => by
    change x.1.castPred x.2 = y.1.castPred y.2 at h
    exact Subtype.ext (Fin.castPred_inj.1 h)
  have h2 := (pair_map_iff pull hinj _ _).2 h1
  exact hH ⟨_, _, _, _, h2⟩

/-- The block, listed in construction order: `K_{3,3}` on `0..5`, then each later vertex with its
three earlier neighbors. Vertices `0,1,2,6,8,10` (one color class) and `3,4,5,7` (the other) have degree five;
`9` has degree four; `11` and `12` have degree three. -/
def blockEdges : List (ℕ × ℕ) :=
  [(0,3),(0,4),(0,5),(1,3),(1,4),(1,5),(2,3),(2,4),(2,5),
   (6,3),(6,4),(6,5),(7,0),(7,1),(7,6),(8,3),(8,4),(8,7),(9,2),(9,6),(9,8),
   (10,5),(10,7),(10,9),(11,0),(11,1),(11,10),(12,2),(12,8),(12,10)]

/-- The block truncated to its first `k` vertices. -/
def blockK (k : ℕ) : SimpleGraph (Fin k) := .fromRel fun a b => (a.val, b.val) ∈ blockEdges

instance (k : ℕ) : DecidableRel (blockK k).Adj :=
  inferInstanceAs (DecidableRel (SimpleGraph.fromRel _).Adj)

theorem block6_not_hasPair : ¬ HasPairF (blockK 6) := by
  rintro ⟨u, v, p, q, hp, hq, hS, hE⟩
  have h : ∀ x, (blockK 6).degree x ≤ 3 := by decide
  exact not_mem_support_of_degree_le_three hp hq hS hE (h u) p.start_mem_support

theorem block7_not_hasPair : ¬ HasPairF (blockK 7) :=
  peel_last (blockK 7) (blockK 6) (by decide) (by decide) block6_not_hasPair

theorem block8_not_hasPair : ¬ HasPairF (blockK 8) :=
  peel_last (blockK 8) (blockK 7) (by decide) (by decide) block7_not_hasPair

theorem block9_not_hasPair : ¬ HasPairF (blockK 9) :=
  peel_last (blockK 9) (blockK 8) (by decide) (by decide) block8_not_hasPair

theorem block10_not_hasPair : ¬ HasPairF (blockK 10) :=
  peel_last (blockK 10) (blockK 9) (by decide) (by decide) block9_not_hasPair

theorem block11_not_hasPair : ¬ HasPairF (blockK 11) :=
  peel_last (blockK 11) (blockK 10) (by decide) (by decide) block10_not_hasPair

theorem block12_not_hasPair : ¬ HasPairF (blockK 12) :=
  peel_last (blockK 12) (blockK 11) (by decide) (by decide) block11_not_hasPair

/-- The full 13-vertex block has no pair. -/
theorem block_not_hasPair : ¬ HasPairF (blockK 13) :=
  peel_last (blockK 13) (blockK 12) (by decide) (by decide) block12_not_hasPair

def mod13 (x : Fin 26) : Fin 13 := ⟨x.val % 13, Nat.mod_lt _ (by decide)⟩

/-- Two blocks joined by three edges between their deficient vertices `9`, `11`, `12`. -/
def pair26 : SimpleGraph (Fin 26) := .fromRel fun a b =>
  (a.val / 13 = b.val / 13 ∧ (blockK 13).Adj (mod13 a) (mod13 b)) ∨
    (a, b) ∈ ([(9,22),(11,24),(12,25)] : List (Fin 26 × Fin 26))

instance : DecidableRel pair26.Adj := inferInstanceAs (DecidableRel (SimpleGraph.fromRel _).Adj)

theorem pair26_not_hasPair : ¬ HasPairF pair26 := by
  apply not_hasPairF_of_small_cut_map (fun x : Fin 26 => x.val / 13)
    {s(9,22), s(11,24), s(12,25)} (by decide) (blockK 13) mod13 (by decide) block_not_hasPair
  · decide
  · decide

def mod26 (x : Fin 52) : Fin 26 := ⟨x.val % 26, Nat.mod_lt _ (by decide)⟩

/-- Two double blocks joined by three edges: a half of the graph. -/
def half52 : SimpleGraph (Fin 52) := .fromRel fun a b =>
  (a.val / 26 = b.val / 26 ∧ pair26.Adj (mod26 a) (mod26 b)) ∨
    (a, b) ∈ ([(11,50),(12,51),(37,24)] : List (Fin 52 × Fin 52))

instance : DecidableRel half52.Adj := inferInstanceAs (DecidableRel (SimpleGraph.fromRel _).Adj)

theorem half52_not_hasPair : ¬ HasPairF half52 := by
  apply not_hasPairF_of_small_cut_map (fun x : Fin 52 => x.val / 26)
    {s(11,50), s(12,51), s(37,24)} (by decide) pair26 mod26 (by decide) pair26_not_hasPair
  · decide
  · decide

def mod52 (x : Fin 104) : Fin 52 := ⟨x.val % 52, Nat.mod_lt _ (by decide)⟩

/-- The 104-vertex graph: two halves joined by two edges. -/
def graph : SimpleGraph (Fin 104) := .fromRel fun a b =>
  (a.val / 52 = b.val / 52 ∧ half52.Adj (mod52 a) (mod52 b)) ∨
    (a, b) ∈ ([(38,77),(90,25)] : List (Fin 104 × Fin 104))

instance : DecidableRel graph.Adj := inferInstanceAs (DecidableRel (SimpleGraph.fromRel _).Adj)

theorem graph_not_hasPair : ¬ HasPairF graph := by
  apply not_hasPairF_of_small_cut_map (fun x : Fin 104 => x.val / 52)
    {s(38,77), s(90,25)} (by decide) half52 mod52 (by decide) half52_not_hasPair
  · decide
  · decide

theorem graph_degree : ∀ v, graph.degree v = 5 := by decide

theorem graph_edge_count : graph.edgeFinset.card = 260 := by
  have h := sum_degrees_eq_twice_card_edges graph
  simp only [graph_degree, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul] at h
  omega

/-- A two-colouring: within a block the vertices `3,4,5,7,9,11,12` form one side; blocks with an
odd index are flipped. -/
def side (v : Fin 104) : Fin 2 :=
  if (v.val % 13 ∈ ([3,4,5,7,9,11,12] : List ℕ)) ↔ ((v.val / 13) % 2 = 1) then 0 else 1

theorem side_adj : ∀ a b, graph.Adj a b → side a ≠ side b := by decide

theorem graph_colorable : graph.Colorable 2 :=
  ⟨Coloring.mk side fun h => side_adj _ _ h⟩

/-- Bipartiteness and degree five together do not force two edge-disjoint cycles with the same
vertex set. -/
theorem exists_bipartite_five_regular_pairfree :
    ∃ G : SimpleGraph (Fin 104), (∀ v, (G.neighborSet v).ncard = 5) ∧ G.Colorable 2 ∧
      ¬ HasTwoEdgeDisjointCyclesSameVertexSet G := by
  refine ⟨graph, ?_, graph_colorable, ?_⟩
  · intro v
    simpa only [← card_neighborFinset_eq_degree, ← Set.ncard_coe_finset,
      coe_neighborFinset] using graph_degree v
  · exact (hasPairF_iff graph).not.mp graph_not_hasPair

end Erdos585.BipartiteFive
