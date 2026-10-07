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
import Mathlib.Combinatorics.SimpleGraph.Bipartite

/-!
# Bipartiteness does not guarantee separation of two edges

An explicit quartic bipartite graph has Hamilton decompositions, but two
specified disjoint edges occur in the same member of every decomposition.
Five four-edge cuts supply the obstruction; no enumeration is used in the proof.
-/
open SimpleGraph Finset
namespace Erdos585.BipartiteSeparation
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

def graph : SimpleGraph (Fin 18) := .fromRel fun a b =>
  (a,b) ∈ ([
    (0,9),(0,11),(0,12),(0,17),(1,9),(1,10),
    (1,11),(1,13),(2,9),(2,10),(2,11),(2,12),
    (3,9),(3,10),(3,11),(3,12),(4,10),(4,12),
    (4,13),(4,16),(5,13),(5,14),(5,15),(5,17),
    (6,14),(6,15),(6,16),(6,17),(7,13),(7,14),
    (7,15),(7,16),(8,14),(8,15),(8,16),(8,17)
  ] : List (Fin 18 × Fin 18))
instance : DecidableRel graph.Adj := inferInstanceAs (DecidableRel (SimpleGraph.fromRel _).Adj)

theorem bipartite : graph.IsBipartite := by
  refine ⟨⟨fun x => if x.val < 9 then 0 else 1, ?_⟩⟩
  decide

theorem regular : ∀ v, graph.degree v = 4 := by decide

def side : Fin 5 → Finset (Fin 18) := ![
  {0,1,2,3,9,10,11,12}, {0,1,2,3,4,9,10,11,12}, {4},
  {5,6,7,8,14,15,16,17}, {13}]
def cut : Fin 5 → Finset (Sym2 (Fin 18)) := ![
  {s(0,17),s(1,13),s(4,10),s(4,12)},
  {s(0,17),s(1,13),s(4,13),s(4,16)},
  {s(4,10),s(4,12),s(4,13),s(4,16)},
  {s(5,13),s(7,13),s(4,16),s(0,17)},
  {s(1,13),s(4,13),s(5,13),s(7,13)}]

def color (i : Fin 5) (v : Fin 18) : Bool := decide (v ∈ side i)
lemma cut_valid : ∀ i a b, graph.Adj a b → color i a ≠ color i b → s(a,b) ∈ cut i :=
  by decide
lemma cut_card : ∀ i, (cut i).card = 4 := by decide
lemma color_nonconstant : ∀ i, ∃ a b, color i a ≠ color i b := by decide

lemma two_le_cut {u : Fin 18} (p : graph.Walk u u) (hp : p.IsCycle)
    (hspan : p.support.toFinset = univ) (i : Fin 5) :
    2 ≤ (cut i ∩ p.edges.toFinset).card := by
  obtain ⟨a,b,hab⟩ := color_nonconstant i
  have hmem : ∀ v, v ∈ p.support := by
    intro v
    rw [← List.mem_toFinset, hspan]
    exact mem_univ v
  by_cases h : color i u = color i a
  · exact two_le_card_cut_edges (color i) (cut i) (cut_valid i) p hp.isTrail (hmem b)
      (fun he => hab (h.symm.trans he))
  · exact two_le_card_cut_edges (color i) (cut i) (cut_valid i) p hp.isTrail (hmem a) h

lemma two_at_each_cut {u v : Fin 18} (p : graph.Walk u u) (q : graph.Walk v v)
    (hp : p.IsCycle) (hq : q.IsCycle)
    (hps : p.support.toFinset = univ) (hqs : q.support.toFinset = univ)
    (hdisj : Disjoint p.edges.toFinset q.edges.toFinset) (i : Fin 5) :
    (cut i ∩ p.edges.toFinset).card = 2 := by
  have hp2 := two_le_cut p hp hps i
  have hq2 := two_le_cut q hq hqs i
  have hd : Disjoint (cut i ∩ p.edges.toFinset) (cut i ∩ q.edges.toFinset) :=
    hdisj.mono inter_subset_right inter_subset_right
  have hc := card_le_card (union_subset
    (inter_subset_left : cut i ∩ p.edges.toFinset ⊆ cut i)
    (inter_subset_left : cut i ∩ q.edges.toFinset ⊆ cut i))
  rw [card_union_of_disjoint hd, cut_card] at hc
  omega

def indicator (R : Finset (Sym2 (Fin 18))) (e : Sym2 (Fin 18)) : ℕ :=
  if e ∈ R then 1 else 0

lemma membership_forced (R : Finset (Sym2 (Fin 18)))
    (h : ∀ i, (cut i ∩ R).card = 2) : s(0,17) ∈ R ↔ s(4,13) ∈ R := by
  have count : ∀ i, ∑ e ∈ cut i, indicator R e = 2 := by
    intro i
    simpa [indicator, sum_ite] using h i
  have h0 := count 0
  have h1 := count 1
  have h2 := count 2
  have h3 := count 3
  have h4 := count 4
  change (∑ e ∈ ({s(0,17),s(1,13),s(4,10),s(4,12)} : Finset _), indicator R e) = 2 at h0
  change (∑ e ∈ ({s(0,17),s(1,13),s(4,13),s(4,16)} : Finset _), indicator R e) = 2 at h1
  change (∑ e ∈ ({s(4,10),s(4,12),s(4,13),s(4,16)} : Finset _), indicator R e) = 2 at h2
  change (∑ e ∈ ({s(5,13),s(7,13),s(4,16),s(0,17)} : Finset _), indicator R e) = 2 at h3
  change (∑ e ∈ ({s(1,13),s(4,13),s(5,13),s(7,13)} : Finset _), indicator R e) = 2 at h4
  rw [sum_insert (by decide), sum_insert (by decide),
    sum_insert (by decide), sum_singleton] at h0
  rw [sum_insert (by decide), sum_insert (by decide),
    sum_insert (by decide), sum_singleton] at h1
  rw [sum_insert (by decide), sum_insert (by decide),
    sum_insert (by decide), sum_singleton] at h2
  rw [sum_insert (by decide), sum_insert (by decide),
    sum_insert (by decide), sum_singleton] at h3
  rw [sum_insert (by decide), sum_insert (by decide),
    sum_insert (by decide), sum_singleton] at h4
  unfold indicator at h0 h1 h2 h3 h4
  split_ifs at * <;> simp_all

/-- Every Hamilton decomposition assigns the two marked edges the same color. -/
theorem inseparable {u v : Fin 18} (p : graph.Walk u u) (q : graph.Walk v v)
    (hp : p.IsCycle) (hq : q.IsCycle)
    (hps : p.support.toFinset = univ) (hqs : q.support.toFinset = univ)
    (hdisj : Disjoint p.edges.toFinset q.edges.toFinset) :
    s(0,17) ∈ p.edges.toFinset ↔ s(4,13) ∈ p.edges.toFinset :=
  membership_forced _ (two_at_each_cut p q hp hq hps hqs hdisj)

def red : graph.Walk 0 0 :=
  .cons (v := 9) (by decide) (
    .cons (v := 1) (by decide) (
    .cons (v := 10) (by decide) (
    .cons (v := 2) (by decide) (
    .cons (v := 11) (by decide) (
    .cons (v := 3) (by decide) (
    .cons (v := 12) (by decide) (
    .cons (v := 4) (by decide) (
    .cons (v := 13) (by decide) (
    .cons (v := 5) (by decide) (
    .cons (v := 14) (by decide) (
    .cons (v := 6) (by decide) (
    .cons (v := 15) (by decide) (
    .cons (v := 7) (by decide) (
    .cons (v := 16) (by decide) (
    .cons (v := 8) (by decide) (
    .cons (v := 17) (by decide) (
    .cons (by decide) .nil)))))))))))))))))
lemma red_cycle : red.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  exact ⟨by decide, by simp [red], by decide⟩

def blue : graph.Walk 7 7 :=
  .cons (v := 14) (by decide) (
    .cons (v := 8) (by decide) (
    .cons (v := 15) (by decide) (
    .cons (v := 5) (by decide) (
    .cons (v := 17) (by decide) (
    .cons (v := 6) (by decide) (
    .cons (v := 16) (by decide) (
    .cons (v := 4) (by decide) (
    .cons (v := 10) (by decide) (
    .cons (v := 3) (by decide) (
    .cons (v := 9) (by decide) (
    .cons (v := 2) (by decide) (
    .cons (v := 12) (by decide) (
    .cons (v := 0) (by decide) (
    .cons (v := 11) (by decide) (
    .cons (v := 1) (by decide) (
    .cons (v := 13) (by decide) (
    .cons (by decide) .nil)))))))))))))))))
lemma blue_cycle : blue.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  exact ⟨by decide, by simp [blue], by decide⟩

theorem hasPair : HasPairF graph :=
  ⟨_, _, red, blue, red_cycle, blue_cycle, by decide, by decide⟩

/-- A nonvacuous counterexample to arbitrary edge separation in bipartite hosts. -/
theorem counterexample :
    graph.IsBipartite ∧ (∀ v, graph.degree v = 4) ∧
    red.IsCycle ∧ blue.IsCycle ∧
    red.support.toFinset = univ ∧ blue.support.toFinset = univ ∧
    Disjoint red.edges.toFinset blue.edges.toFinset ∧
    ∀ (u v : Fin 18) (p : graph.Walk u u) (q : graph.Walk v v),
      p.IsCycle → q.IsCycle → p.support.toFinset = univ →
      q.support.toFinset = univ → Disjoint p.edges.toFinset q.edges.toFinset →
      (s(0,17) ∈ p.edges.toFinset ↔ s(4,13) ∈ p.edges.toFinset) := by
  refine ⟨bipartite, regular, red_cycle, blue_cycle, by decide, by decide,
    by decide, ?_⟩
  exact fun _ _ p q hp hq hps hqs hd => inseparable p q hp hq hps hqs hd

end Erdos585.BipartiteSeparation
