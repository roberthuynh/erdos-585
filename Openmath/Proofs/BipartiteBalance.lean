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
# A vertex-balance constraint on forbidden pairs

If one color class is independent, two simple cycles with the same vertex support
use equally many edges within the other class. In particular, when at most three
such edges are available, an edge-disjoint pair uses at most one in each cycle.
-/

open SimpleGraph Finset
open scoped Classical
namespace Erdos585.BipartiteBalance

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

/-- Sum of the endpoint weights of an unordered edge. -/
def edgeWeight (w : V → ℤ) : Sym2 V → ℤ :=
  Sym2.lift ⟨fun a b => w a + w b, fun a b => add_comm (w a) (w b)⟩

omit [DecidableEq V] in
@[simp] lemma edgeWeight_mk (w : V → ℤ) (a b : V) :
    edgeWeight w s(a,b) = w a + w b := rfl

omit [DecidableEq V] in
lemma walk_weight_sum (w : V → ℤ) {a b : V} (p : G.Walk a b) :
    (p.edges.map (edgeWeight w)).sum =
      2 * (p.support.tail.map w).sum + w a - w b := by
  induction p with
  | nil => simp
  | @cons a b z hab p ih =>
    have hs : (p.support.map w).sum = w b + (p.support.tail.map w).sum := by
      have h := congrArg (fun l : List V => (l.map w).sum) p.cons_tail_support
      simpa only [List.map_cons, List.sum_cons] using h.symm
    simp only [Walk.edges_cons, List.map_cons, List.sum_cons, edgeWeight_mk,
      Walk.support_cons, List.tail_cons]
    rw [ih, hs]
    ring

lemma cycle_tail_support {a : V} {p : G.Walk a a} (hp : p.IsCycle) :
    p.support.tail.toFinset = p.support.toFinset := by
  ext x
  simp only [List.mem_toFinset]
  constructor
  · exact List.mem_of_mem_tail
  · intro hx
    rw [← p.cons_tail_support, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact p.end_mem_tail_support hp.not_nil
    · exact hx

lemma cycle_weight_sum (w : V → ℤ) {a : V} {p : G.Walk a a} (hp : p.IsCycle) :
    ∑ e ∈ p.edges.toFinset, edgeWeight w e = 2 * ∑ v ∈ p.support.toFinset, w v := by
  rw [List.sum_toFinset _ hp.edges_nodup, walk_weight_sum]
  rw [← List.sum_toFinset _ hp.support_nodup, cycle_tail_support hp]
  ring

/-- The edges whose two endpoints have color true. -/
def sameTrue (c : V → Bool) (e : Sym2 V) : Prop := ∀ v ∈ e, c v = true

omit [DecidableEq V] in
lemma weight_when_false_independent (c : V → Bool)
    (hc : ∀ a b, G.Adj a b → c a = true ∨ c b = true) {e : Sym2 V}
    (he : e ∈ G.edgeSet) :
    edgeWeight (fun v => if c v then 1 else -1) e =
      if sameTrue c e then 2 else 0 := by
  induction e using Sym2.inductionOn with | _ a b => ?_
  have h := hc a b (G.mem_edgeSet.mp he)
  cases ha : c a <;> cases hb : c b <;> simp_all [sameTrue]

lemma walk_true_weight (c : V → Bool)
    (hc : ∀ a b, G.Adj a b → c a = true ∨ c b = true)
    {a : V} (p : G.Walk a a) :
    2 * ((p.edges.toFinset.filter (sameTrue c)).card : ℤ) =
      ∑ e ∈ p.edges.toFinset, edgeWeight (fun v => if c v then 1 else -1) e := by
  classical
  symm
  calc
    _ = ∑ e ∈ p.edges.toFinset, (if sameTrue c e then (2 : ℤ) else 0) := by
      apply sum_congr rfl
      intro e he
      exact weight_when_false_independent c hc (p.edges_subset_edgeSet (List.mem_toFinset.mp he))
    _ = _ := by simp [sum_ite, mul_comm]

/-- Equal vertex support forces equal numbers of edges within the non-independent class. -/
theorem equal_true_edge_counts (c : V → Bool)
    (hc : ∀ a b, G.Adj a b → c a = true ∨ c b = true)
    {a b : V} {p : G.Walk a a} {q : G.Walk b b}
    (hp : p.IsCycle) (hq : q.IsCycle)
    (hS : p.support.toFinset = q.support.toFinset) :
    (p.edges.toFinset.filter (sameTrue c)).card =
      (q.edges.toFinset.filter (sameTrue c)).card := by
  classical
  have h1 := walk_true_weight c hc p
  have h2 := walk_true_weight c hc q
  rw [cycle_weight_sum _ hp, hS] at h1
  rw [cycle_weight_sum _ hq] at h2
  omega

/-- At most three exceptional edges force at most one per member of a forbidden pair. -/
theorem at_most_one_exceptional (c : V → Bool) (exceptions : Finset (Sym2 V))
    (hc : ∀ a b, G.Adj a b → c a = true ∨ c b = true)
    (hex : ∀ e ∈ G.edgeSet, sameTrue c e → e ∈ exceptions)
    (hsize : exceptions.card ≤ 3)
    {a b : V} {p : G.Walk a a} {q : G.Walk b b}
    (hp : p.IsCycle) (hq : q.IsCycle)
    (hS : p.support.toFinset = q.support.toFinset)
    (hE : Disjoint p.edges.toFinset q.edges.toFinset) :
    (p.edges.toFinset.filter (sameTrue c)).card ≤ 1 ∧
      (p.edges.toFinset.filter (sameTrue c)).card =
        (q.edges.toFinset.filter (sameTrue c)).card := by
  classical
  have heq := equal_true_edge_counts c hc hp hq hS
  have hsub : p.edges.toFinset.filter (sameTrue c) ∪
      q.edges.toFinset.filter (sameTrue c) ⊆ exceptions := by
    intro e he
    rcases mem_union.mp he with he | he
    · exact hex e (p.edges_subset_edgeSet (List.mem_toFinset.mp (mem_filter.mp he).1))
        (mem_filter.mp he).2
    · exact hex e (q.edges_subset_edgeSet (List.mem_toFinset.mp (mem_filter.mp he).1))
        (mem_filter.mp he).2
  have hdis : Disjoint (p.edges.toFinset.filter (sameTrue c))
      (q.edges.toFinset.filter (sameTrue c)) :=
    hE.mono (filter_subset _ _) (filter_subset _ _)
  have hcount := card_le_card hsub
  rw [card_union_of_disjoint hdis, heq] at hcount
  exact ⟨by omega, heq⟩

end Erdos585.BipartiteBalance
