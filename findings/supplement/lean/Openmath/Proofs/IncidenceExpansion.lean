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
import Openmath.Proofs.Compat
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Tactic

/-! # An expanded incidence graph with three Hamilton cycles

This is the original bipartite graph behind the rainbow splitting obstruction.
An Euler tour of K7 supplies the three explicit cycles. Only this finite
instance, not the general Euler-tour construction, is formalized here.
-/
open SimpleGraph Finset
namespace Erdos585.IncidenceExpansion
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

def baseEdge : Fin 21 → Fin 7 × Fin 7 := ![
  (0,1),
  (0,2),
  (0,3),
  (0,4),
  (0,5),
  (0,6),
  (1,2),
  (1,3),
  (1,4),
  (1,5),
  (1,6),
  (2,3),
  (2,4),
  (2,5),
  (2,6),
  (3,4),
  (3,5),
  (3,6),
  (4,5),
  (4,6),
  (5,6)]

def graph : SimpleGraph (Fin 42) := .fromRel fun a b =>
  ∃ i : Fin 21, a.val = i.val ∧ 21 ≤ b.val ∧
    ((b.val-21)/3 = (baseEdge i).1.val ∨ (b.val-21)/3 = (baseEdge i).2.val)
instance : DecidableRel graph.Adj := inferInstanceAs (DecidableRel (SimpleGraph.fromRel _).Adj)

theorem bipartite : graph.IsBipartite := by
  refine ⟨⟨fun x => if x.val < 21 then 0 else 1, ?_⟩⟩
  decide

theorem regular : ∀ v, graph.degree v = 6 := by decide

def first : graph.Walk 21 21 :=
  .cons (v := 5) (by decide) (
  .cons (v := 39) (by decide) (
  .cons (v := 20) (by decide) (
  .cons (v := 36) (by decide) (
  .cons (v := 18) (by decide) (
  .cons (v := 33) (by decide) (
  .cons (v := 19) (by decide) (
  .cons (v := 40) (by decide) (
  .cons (v := 17) (by decide) (
  .cons (v := 30) (by decide) (
  .cons (v := 16) (by decide) (
  .cons (v := 37) (by decide) (
  .cons (v := 13) (by decide) (
  .cons (v := 27) (by decide) (
  .cons (v := 14) (by decide) (
  .cons (v := 41) (by decide) (
  .cons (v := 10) (by decide) (
  .cons (v := 24) (by decide) (
  .cons (v := 9) (by decide) (
  .cons (v := 38) (by decide) (
  .cons (v := 4) (by decide) (
  .cons (v := 22) (by decide) (
  .cons (v := 3) (by decide) (
  .cons (v := 34) (by decide) (
  .cons (v := 15) (by decide) (
  .cons (v := 31) (by decide) (
  .cons (v := 11) (by decide) (
  .cons (v := 28) (by decide) (
  .cons (v := 12) (by decide) (
  .cons (v := 35) (by decide) (
  .cons (v := 8) (by decide) (
  .cons (v := 25) (by decide) (
  .cons (v := 7) (by decide) (
  .cons (v := 32) (by decide) (
  .cons (v := 2) (by decide) (
  .cons (v := 23) (by decide) (
  .cons (v := 1) (by decide) (
  .cons (v := 29) (by decide) (
  .cons (v := 6) (by decide) (
  .cons (v := 26) (by decide) (
  .cons (v := 0) (by decide) (
  .cons (by decide) .nil)))))))))))))))))))))))))))))))))))))))))
lemma first_cycle : first.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  exact ⟨by decide, by simp [first], by decide⟩

def second : graph.Walk 22 22 :=
  .cons (v := 5) (by decide) (
  .cons (v := 40) (by decide) (
  .cons (v := 20) (by decide) (
  .cons (v := 37) (by decide) (
  .cons (v := 18) (by decide) (
  .cons (v := 34) (by decide) (
  .cons (v := 19) (by decide) (
  .cons (v := 41) (by decide) (
  .cons (v := 17) (by decide) (
  .cons (v := 31) (by decide) (
  .cons (v := 16) (by decide) (
  .cons (v := 38) (by decide) (
  .cons (v := 13) (by decide) (
  .cons (v := 28) (by decide) (
  .cons (v := 14) (by decide) (
  .cons (v := 39) (by decide) (
  .cons (v := 10) (by decide) (
  .cons (v := 25) (by decide) (
  .cons (v := 9) (by decide) (
  .cons (v := 36) (by decide) (
  .cons (v := 4) (by decide) (
  .cons (v := 23) (by decide) (
  .cons (v := 3) (by decide) (
  .cons (v := 35) (by decide) (
  .cons (v := 15) (by decide) (
  .cons (v := 32) (by decide) (
  .cons (v := 11) (by decide) (
  .cons (v := 29) (by decide) (
  .cons (v := 12) (by decide) (
  .cons (v := 33) (by decide) (
  .cons (v := 8) (by decide) (
  .cons (v := 26) (by decide) (
  .cons (v := 7) (by decide) (
  .cons (v := 30) (by decide) (
  .cons (v := 2) (by decide) (
  .cons (v := 21) (by decide) (
  .cons (v := 1) (by decide) (
  .cons (v := 27) (by decide) (
  .cons (v := 6) (by decide) (
  .cons (v := 24) (by decide) (
  .cons (v := 0) (by decide) (
  .cons (by decide) .nil)))))))))))))))))))))))))))))))))))))))))
lemma second_cycle : second.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  exact ⟨by decide, by simp [second], by decide⟩

def third : graph.Walk 23 23 :=
  .cons (v := 5) (by decide) (
  .cons (v := 41) (by decide) (
  .cons (v := 20) (by decide) (
  .cons (v := 38) (by decide) (
  .cons (v := 18) (by decide) (
  .cons (v := 35) (by decide) (
  .cons (v := 19) (by decide) (
  .cons (v := 39) (by decide) (
  .cons (v := 17) (by decide) (
  .cons (v := 32) (by decide) (
  .cons (v := 16) (by decide) (
  .cons (v := 36) (by decide) (
  .cons (v := 13) (by decide) (
  .cons (v := 29) (by decide) (
  .cons (v := 14) (by decide) (
  .cons (v := 40) (by decide) (
  .cons (v := 10) (by decide) (
  .cons (v := 26) (by decide) (
  .cons (v := 9) (by decide) (
  .cons (v := 37) (by decide) (
  .cons (v := 4) (by decide) (
  .cons (v := 21) (by decide) (
  .cons (v := 3) (by decide) (
  .cons (v := 33) (by decide) (
  .cons (v := 15) (by decide) (
  .cons (v := 30) (by decide) (
  .cons (v := 11) (by decide) (
  .cons (v := 27) (by decide) (
  .cons (v := 12) (by decide) (
  .cons (v := 34) (by decide) (
  .cons (v := 8) (by decide) (
  .cons (v := 24) (by decide) (
  .cons (v := 7) (by decide) (
  .cons (v := 31) (by decide) (
  .cons (v := 2) (by decide) (
  .cons (v := 22) (by decide) (
  .cons (v := 1) (by decide) (
  .cons (v := 28) (by decide) (
  .cons (v := 6) (by decide) (
  .cons (v := 25) (by decide) (
  .cons (v := 0) (by decide) (
  .cons (by decide) .nil)))))))))))))))))))))))))))))))))))))))))
lemma third_cycle : third.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  exact ⟨by decide, by simp [third], by decide⟩

theorem hasPair : HasPairF graph :=
  ⟨_, _, first, second, first_cycle, second_cycle, by decide, by decide⟩

/-- Three edge-disjoint spanning cycles in the six-regular bipartite host. -/
theorem three_hamilton_cycles :
    graph.IsBipartite ∧ (∀ v, graph.degree v = 6) ∧
    first.IsCycle ∧ second.IsCycle ∧ third.IsCycle ∧
    first.support.toFinset = univ ∧ second.support.toFinset = univ ∧
    third.support.toFinset = univ ∧
    Disjoint first.edges.toFinset second.edges.toFinset ∧
    Disjoint first.edges.toFinset third.edges.toFinset ∧
    Disjoint second.edges.toFinset third.edges.toFinset :=
  ⟨bipartite, regular, first_cycle, second_cycle, third_cycle,
    by decide, by decide, by decide, by decide, by decide, by decide⟩

end Erdos585.IncidenceExpansion
