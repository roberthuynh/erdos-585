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
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic

/-! # An explicit forest-law certificate from at most three forests

The edge intersection is taken with an actual cycle walk. A finite family
of actual acyclic subgraphs covering all edges supplies a single uniform
forest law that meets every bipartite simple cycle in expected size at
least four thirds. No cycle-law or independence hypothesis is assumed.
-/

noncomputable section
namespace Erdos585.CubelikeForest
open SimpleGraph Finset

universe u v
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V}

/-- Number of distinct walk edges belonging to a specified actual subgraph. -/
def intersectionCount {a b : V} (p : G.Walk a b) (F : SimpleGraph V) : ℕ := by
  classical
  exact (p.edges.toFinset.filter (fun e => e ∈ F.edgeSet)).card

omit [DecidableEq V] in
/-- An actual graph with at most one neighbor at every vertex is a forest. -/
theorem acyclic_of_neighbor_unique
    (h : ∀ x y z, G.Adj x y → G.Adj x z → y = z) : G.IsAcyclic := by
  intro a p hp
  have hl := hp.three_le_length
  have h02 := h (p.getVert 1) (p.getVert 0) (p.getVert 2)
    (p.adj_getVert_succ (i := 0) (by omega)).symm
    (p.adj_getVert_succ (i := 1) (by omega))
  exact hp.getVert_sub_one_ne_getVert_add_one (i := 1) (by omega) h02

omit [DecidableEq V] in
/-- Bipartite simple cycles have at least four edges. -/
theorem cycle_length_four (hb : G.IsBipartite) {a : V}
    (p : G.Walk a a) (hp : p.IsCycle) : 4 ≤ p.length := by
  obtain ⟨c⟩ := hb
  let col : G.Coloring Bool := recolorOfEquiv G finTwoEquiv c
  have hthree := hp.three_le_length
  have heven : Even p.length := (col.even_length_iff_congr p).2 Iff.rfl
  obtain ⟨k, hk⟩ := heven
  omega

/-- Covering each edge is enough; a partition is a special case. -/
theorem sum_intersectionCount_ge_length {I : Type v} [Fintype I]
    (F : I → SimpleGraph V)
    (hcover : ∀ e ∈ G.edgeSet, ∃ i, e ∈ (F i).edgeSet)
    {a : V} (p : G.Walk a a) (hp : p.IsCycle) :
    p.length ≤ ∑ i, intersectionCount p (F i) := by
  classical
  have hc : p.edges.toFinset.card = p.length := by
    rw [List.toFinset_card_of_nodup hp.edges_nodup, Walk.length_edges]
  rw [← hc]
  simp only [intersectionCount, Finset.card_filter]
  rw [Finset.sum_comm]
  calc
    p.edges.toFinset.card = ∑ e ∈ p.edges.toFinset, (1 : ℕ) := by simp
    _ ≤ ∑ e ∈ p.edges.toFinset, ∑ i, if e ∈ (F i).edgeSet then 1 else 0 := by
      apply Finset.sum_le_sum
      intro e he
      obtain ⟨i, hi⟩ := hcover e (p.edges_subset_edgeSet (List.mem_toFinset.mp he))
      simpa [hi] using
        (Finset.single_le_sum (fun j _ => Nat.zero_le
          (if e ∈ (F j).edgeSet then 1 else 0)) (Finset.mem_univ i))

/-- The one uniform distribution meets every actual cycle in at least four thirds. -/
theorem uniform_intersection_ge_four_thirds {I : Type v} [Fintype I]
    (F : I → SimpleGraph V)
    (hpos : 0 < Fintype.card I) (hcard : Fintype.card I ≤ 3)
    (hcover : ∀ e ∈ G.edgeSet, ∃ i, e ∈ (F i).edgeSet)
    (hb : G.IsBipartite) {a : V} (p : G.Walk a a) (hp : p.IsCycle) :
    (4 : ℝ) / 3 ≤ ∑ i, (1 / (Fintype.card I : ℝ)) *
      (intersectionCount p (F i) : ℝ) := by
  have hc : (0 : ℝ) < Fintype.card I := by exact_mod_cast hpos
  have hc3 : (Fintype.card I : ℝ) ≤ 3 := by exact_mod_cast hcard
  have hl : (4 : ℝ) ≤ ∑ i, (intersectionCount p (F i) : ℝ) := by
    exact_mod_cast (cycle_length_four hb p hp).trans
      (sum_intersectionCount_ge_length F hcover p hp)
  rw [← Finset.mul_sum, one_div_mul_eq_div]
  apply (le_div_iff₀ hc).2
  nlinarith

/-- An explicit probability distribution on actual forests, valid for every actual cycle. -/
theorem forest_cover_certificate {I : Type v} [Fintype I]
    (F : I → SimpleGraph V)
    (hpos : 0 < Fintype.card I) (hcard : Fintype.card I ≤ 3)
    (hle : ∀ i, F i ≤ G) (hforest : ∀ i, (F i).IsAcyclic)
    (hcover : ∀ e ∈ G.edgeSet, ∃ i, e ∈ (F i).edgeSet)
    (hb : G.IsBipartite) :
    ∃ w : I → ℝ, (∀ i, 0 ≤ w i) ∧ (∑ i, w i) = 1 ∧
      (∀ i, F i ≤ G ∧ (F i).IsAcyclic) ∧
      ∀ (a : V) (p : G.Walk a a), p.IsCycle →
        (4 : ℝ) / 3 ≤ ∑ i, w i * (intersectionCount p (F i) : ℝ) := by
  refine ⟨fun _ => 1 / (Fintype.card I : ℝ), fun _ => by positivity, ?_,
    fun i => ⟨hle i, hforest i⟩, ?_⟩
  · have hc : (Fintype.card I : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
    simp [hc]
  · intro a p hp
    exact uniform_intersection_ge_four_thirds F hpos hcard hcover hb p hp

/-- A forest-law certificate gives an actual forest against every finite law on actual cycles.
The forest may depend on the cycle law; no independence or distinctness is required. -/
theorem cycle_law_forest_of_certificate {I : Type v} [Fintype I]
    (F : I → SimpleGraph V) (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hwsum : ∑ i, w i = 1)
    (hF : ∀ i, F i ≤ G ∧ (F i).IsAcyclic) (c : ℝ)
    (hcert : ∀ (a : V) (p : G.Walk a a), p.IsCycle →
      c ≤ ∑ i, w i * (intersectionCount p (F i) : ℝ))
    {J : Type*} [Fintype J] (base : J → V)
    (p : ∀ j, G.Walk (base j) (base j)) (hp : ∀ j, (p j).IsCycle)
    (lam : J → ℝ) (hlam : ∀ j, 0 ≤ lam j) (hlamsum : ∑ j, lam j = 1) :
    ∃ H : SimpleGraph V, H ≤ G ∧ H.IsAcyclic ∧
      c ≤ ∑ j, lam j * (intersectionCount (p j) H : ℝ) := by
  classical
  have havg : c ≤ ∑ i, w i * (∑ j, lam j * (intersectionCount (p j) (F i) : ℝ)) := by
    calc
      c = ∑ j, lam j * c := by rw [← Finset.sum_mul, hlamsum, one_mul]
      _ ≤ ∑ j, lam j * (∑ i, w i * (intersectionCount (p j) (F i) : ℝ)) := by
        exact Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_left (hcert (base j) (p j) (hp j)) (hlam j)
      _ = ∑ i, w i * (∑ j, lam j * (intersectionCount (p j) (F i) : ℝ)) := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
  have hpos : ∃ i, 0 < w i := by
    by_contra h
    push Not at h
    have hz : ∑ i, w i ≤ 0 := Finset.sum_nonpos fun i _ => h i
    linarith
  have hex : ∃ i, c ≤ ∑ j, lam j * (intersectionCount (p j) (F i) : ℝ) := by
    by_contra h
    push Not at h
    obtain ⟨i, hi⟩ := hpos
    have hlt :
        (∑ i, w i * (∑ j, lam j * (intersectionCount (p j) (F i) : ℝ))) <
          ∑ i, w i * c :=
      Finset.sum_lt_sum
        (fun k _ => mul_le_mul_of_nonneg_left (h k).le (hw k))
        ⟨i, Finset.mem_univ i, mul_lt_mul_of_pos_left (h i) hi⟩
    rw [← Finset.sum_mul, hwsum, one_mul] at hlt
    exact (not_lt_of_ge havg) hlt
  obtain ⟨i, hi⟩ := hex
  exact ⟨F i, (hF i).1, (hF i).2, hi⟩

/-- The cycle-law form of the four-thirds certificate from at most three actual forests. -/
theorem cycle_law_forest {I : Type v} [Fintype I]
    (F : I → SimpleGraph V)
    (hpos : 0 < Fintype.card I) (hcard : Fintype.card I ≤ 3)
    (hle : ∀ i, F i ≤ G) (hforest : ∀ i, (F i).IsAcyclic)
    (hcover : ∀ e ∈ G.edgeSet, ∃ i, e ∈ (F i).edgeSet)
    (hb : G.IsBipartite)
    {J : Type*} [Fintype J] (base : J → V)
    (p : ∀ j, G.Walk (base j) (base j)) (hp : ∀ j, (p j).IsCycle)
    (lam : J → ℝ) (hlam : ∀ j, 0 ≤ lam j) (hlamsum : ∑ j, lam j = 1) :
    ∃ H : SimpleGraph V, H ≤ G ∧ H.IsAcyclic ∧
      (4 : ℝ) / 3 ≤ ∑ j, lam j * (intersectionCount (p j) H : ℝ) := by
  obtain ⟨w, hw, hwsum, hF, hcert⟩ :=
    forest_cover_certificate F hpos hcard hle hforest hcover hb
  exact cycle_law_forest_of_certificate F w hw hwsum hF (4 / 3) hcert
    base p hp lam hlam hlamsum

end Erdos585.CubelikeForest
