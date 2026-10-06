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
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

/-!
# A genuine two-sheet cover need not preserve faithful-pair avoidance

The base consists of two copies of K₄,₄ minus one edge, joined by two
crossed port edges. It is connected, bipartite, four-regular, and avoids
the faithful pair on every support. An explicit mixed signing has a
thirty-two-vertex lift decomposed into two actual Hamilton cycles.
The projection has fibers of size two and unique lifting of each neighbor.

This is a finite transfer counterexample, not an extremal growth claim.
The cycles follow the Euler-occurrence construction recorded in Paper85.
-/

open SimpleGraph Finset

namespace Erdos585.CoverTransfer

set_option maxRecDepth 16384
set_option maxHeartbeats 16000000

/-- Block b has left vertices 8b+i and right vertices 8b+4+i. -/
def base : SimpleGraph (Fin 16) := .fromRel fun a b =>
  (a,b) ∈ ([
    (0,5),(0,6),(0,7),(1,4),(1,5),(1,6),(1,7),
    (2,4),(2,5),(2,6),(2,7),(3,4),(3,5),(3,6),(3,7),
    (8,13),(8,14),(8,15),(9,12),(9,13),(9,14),(9,15),
    (10,12),(10,13),(10,14),(10,15),(11,12),(11,13),(11,14),(11,15),
    (0,12),(8,4)] : List (Fin 16 × Fin 16))

instance : DecidableRel base.Adj :=
  inferInstanceAs (DecidableRel (SimpleGraph.fromRel _).Adj)

theorem base_bipartite : base.IsBipartite := by
  refine ⟨⟨fun v => if v.val % 8 < 4 then 0 else 1, ?_⟩⟩
  decide

theorem base_regular : base.IsRegularOfDegree 4 := by
  change ∀ v, base.degree v = 4
  decide

theorem base_connected : base.Connected := by decide

/-- Quartic support closure and the two-edge cut exclude every faithful pair. -/
theorem base_avoiding : ¬ HasPairF base := by
  rintro ⟨u, v, p, q, hp, hq, hS, hE⟩
  have step : ∀ x, x ∈ p.support.toFinset → ∀ y, base.Adj x y →
      y ∈ p.support.toFinset := by
    intro x hx y hxy
    have h4 := card_neighbors_of_pair hp hq hS hE (List.mem_toFinset.mp hx)
    have hsub : p.support.toFinset.filter
        (fun w => s(x,w) ∈ p.edges.toFinset ∪ q.edges.toFinset) ⊆
        base.neighborFinset x := by
      intro z hz
      exact (mem_neighborFinset _ _ _).2
        (mem_support_and_adj_of_mem_union_edges hS (mem_filter.mp hz).2).2
    have heq := Finset.eq_of_subset_of_card_le hsub
      (by rw [card_neighborFinset_eq_degree, base_regular x, h4])
    have hy := (mem_neighborFinset _ _ _).2 hxy
    rw [← heq] at hy
    exact (mem_filter.mp hy).1
  have follow : ∀ {a b : Fin 16}, base.Walk a b →
      a ∈ p.support.toFinset → b ∈ p.support.toFinset := by
    intro a b w
    induction w with
    | nil => exact id
    | @cons a b c hab w ih => exact fun ha => ih (step a ha b hab)
  have hall (x : Fin 16) : x ∈ p.support := by
    exact List.mem_toFinset.mp (follow (base_connected.preconnected u x).some
      (List.mem_toFinset.mpr p.start_mem_support))
  have confined := pair_constant_of_small_cut (fun x : Fin 16 => x.val / 8)
    ({s(0,12),s(8,4)} : Finset (Sym2 (Fin 16))) (by decide)
    hp hq hS hE (by decide)
  have h0 := confined 0 (hall 0)
  have h8 := confined 8 (hall 8)
  norm_num at h0 h8
  omega

/-- The twelve crossed-fiber edges; all other base edges preserve the sheet. -/
def sign (e : Sym2 (Fin 16)) : ℕ :=
  if e ∈ ({s(2,5),s(3,5),s(1,6),s(1,7),s(2,7),
      s(10,13),s(11,13),s(9,14),s(9,15),s(10,15),s(0,12),s(8,4)} :
      Finset (Sym2 (Fin 16))) then 1 else 0

/-- Label (v,a) by 2v+a. -/
def project (x : Fin 32) : Fin 16 := ⟨x.val / 2, by omega⟩

def sheet (x : Fin 32) : ℕ := x.val % 2

/-- Actual signed two-lift, with no vertical edges. -/
def lift : SimpleGraph (Fin 32) where
  Adj a b := base.Adj (project a) (project b) ∧
    (sheet a + sheet b) % 2 = sign s(project a,project b)
  symm := ⟨by
    intro a b h
    refine ⟨base.adj_symm h.1, ?_⟩
    simpa only [Nat.add_comm, Sym2.eq_swap] using h.2⟩
  loopless := ⟨by intro a h; exact base.loopless.irrefl _ h.1⟩

instance : DecidableRel lift.Adj := fun a b =>
  inferInstanceAs (Decidable (base.Adj (project a) (project b) ∧
    (sheet a + sheet b) % 2 = sign s(project a,project b)))

theorem lift_bipartite : lift.IsBipartite := by
  refine ⟨⟨fun v => if (project v).val % 8 < 4 then 0 else 1, ?_⟩⟩
  decide

theorem lift_regular : lift.IsRegularOfDegree 4 := by
  change ∀ v, lift.degree v = 4
  decide

theorem projection_surjective : Function.Surjective project := by decide

theorem projection_fibers : ∀ v : Fin 16,
    (univ.filter fun x : Fin 32 => project x = v).card = 2 := by decide

theorem projection_adjacency {x y : Fin 32} (h : lift.Adj x y) :
    base.Adj (project x) (project y) := h.1

/-- Each actual base neighbor has exactly one neighbor in the lifted star. -/
theorem unique_neighbor_lift : ∀ (x : Fin 32) (v : Fin 16),
    base.Adj (project x) v ↔ ∃! y : Fin 32, lift.Adj x y ∧ project y = v := by
  simp only [ExistsUnique]
  decide

def red : lift.Walk 0 0 :=
  .cons (v := 10) (by decide) (
  .cons (v := 2) (by decide) (
  .cons (v := 8) (by decide) (
  .cons (v := 4) (by decide) (
  .cons (v := 11) (by decide) (
  .cons (v := 6) (by decide) (
  .cons (v := 12) (by decide) (
  .cons (v := 3) (by decide) (
  .cons (v := 14) (by decide) (
  .cons (v := 5) (by decide) (
  .cons (v := 13) (by decide) (
  .cons (v := 1) (by decide) (
  .cons (v := 15) (by decide) (
  .cons (v := 7) (by decide) (
  .cons (v := 9) (by decide) (
  .cons (v := 16) (by decide) (
  .cons (v := 26) (by decide) (
  .cons (v := 18) (by decide) (
  .cons (v := 24) (by decide) (
  .cons (v := 20) (by decide) (
  .cons (v := 27) (by decide) (
  .cons (v := 22) (by decide) (
  .cons (v := 28) (by decide) (
  .cons (v := 19) (by decide) (
  .cons (v := 30) (by decide) (
  .cons (v := 21) (by decide) (
  .cons (v := 29) (by decide) (
  .cons (v := 17) (by decide) (
  .cons (v := 31) (by decide) (
  .cons (v := 23) (by decide) (
  .cons (v := 25) (by decide) (
  .cons (by decide) .nil)))))))))))))))))))))))))))))))

def blue : lift.Walk 1 1 :=
  .cons (v := 11) (by decide) (
  .cons (v := 3) (by decide) (
  .cons (v := 9) (by decide) (
  .cons (v := 5) (by decide) (
  .cons (v := 10) (by decide) (
  .cons (v := 7) (by decide) (
  .cons (v := 13) (by decide) (
  .cons (v := 2) (by decide) (
  .cons (v := 15) (by decide) (
  .cons (v := 4) (by decide) (
  .cons (v := 12) (by decide) (
  .cons (v := 0) (by decide) (
  .cons (v := 14) (by decide) (
  .cons (v := 6) (by decide) (
  .cons (v := 8) (by decide) (
  .cons (v := 17) (by decide) (
  .cons (v := 27) (by decide) (
  .cons (v := 19) (by decide) (
  .cons (v := 25) (by decide) (
  .cons (v := 21) (by decide) (
  .cons (v := 26) (by decide) (
  .cons (v := 23) (by decide) (
  .cons (v := 29) (by decide) (
  .cons (v := 18) (by decide) (
  .cons (v := 31) (by decide) (
  .cons (v := 20) (by decide) (
  .cons (v := 28) (by decide) (
  .cons (v := 16) (by decide) (
  .cons (v := 30) (by decide) (
  .cons (v := 22) (by decide) (
  .cons (v := 24) (by decide) (
  .cons (by decide) .nil)))))))))))))))))))))))))))))))

theorem red_cycle : red.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  exact ⟨by decide, by simp [red], by decide⟩

theorem blue_cycle : blue.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  exact ⟨by decide, by simp [blue], by decide⟩

theorem red_spanning : red.support.toFinset = univ := by decide

theorem blue_spanning : blue.support.toFinset = univ := by decide

theorem cycles_disjoint : Disjoint red.edges.toFinset blue.edges.toFinset := by decide

theorem lift_hasPair : HasPairF lift :=
  ⟨0, 1, red, blue, red_cycle, blue_cycle,
    red_spanning.trans blue_spanning.symm, cycles_disjoint⟩

/-- Both hosts are actual quartic bipartite graphs, the base avoids the upstream
pattern, the lift contains it, and the displayed projection is a two-sheet cover. -/
theorem counterexample :
    base.IsBipartite ∧ base.IsRegularOfDegree 4 ∧
    ¬ HasTwoEdgeDisjointCyclesSameVertexSet base ∧
    lift.IsBipartite ∧ lift.IsRegularOfDegree 4 ∧
    HasTwoEdgeDisjointCyclesSameVertexSet lift ∧
    Function.Surjective project ∧
    (∀ v : Fin 16, (univ.filter fun x : Fin 32 => project x = v).card = 2) ∧
    (∀ x y : Fin 32, lift.Adj x y → base.Adj (project x) (project y)) ∧
    (∀ (x : Fin 32) (v : Fin 16), base.Adj (project x) v ↔
      ∃! y : Fin 32, lift.Adj x y ∧ project y = v) ∧
    red.IsCycle ∧ blue.IsCycle ∧
    red.support.toFinset = univ ∧ blue.support.toFinset = univ ∧
    Disjoint red.edges.toFinset blue.edges.toFinset := by
  exact ⟨base_bipartite, base_regular,
    fun h => base_avoiding ((hasPairF_iff base).mpr h),
    lift_bipartite, lift_regular, (hasPairF_iff lift).mp lift_hasPair,
    projection_surjective, projection_fibers, fun _ _ h => projection_adjacency h,
    unique_neighbor_lift, red_cycle, blue_cycle, red_spanning, blue_spanning,
    cycles_disjoint⟩

end Erdos585.CoverTransfer
