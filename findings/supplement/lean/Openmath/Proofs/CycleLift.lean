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
import Openmath.Proofs.BipartiteBalance

/-! # Replacing at most one edge of a cycle through a new vertex -/

open SimpleGraph Finset
namespace Erdos585.CycleLift

variable {V : Type*} [DecidableEq V] {G H : SimpleGraph V}
variable (M : Finset (Sym2 V)) (w : V)
variable (keep : ∀ {a b}, G.Adj a b → s(a,b) ∉ M → H.Adj a b)
variable (replace : ∀ {a b}, G.Adj a b → s(a,b) ∈ M → H.Adj a w ∧ H.Adj w b)

/-- Number of traversals of replacement edges. -/
def count {a b : V} (p : G.Walk a b) : ℕ :=
  (p.edges.filter fun e => decide (e ∈ M)).length

@[simp] lemma count_nil (a : V) : count M (Walk.nil : G.Walk a a) = 0 := rfl

@[simp] lemma count_cons {a b c : V} (h : G.Adj a b) (p : G.Walk b c) :
    count M (Walk.cons h p) = (if s(a,b) ∈ M then 1 else 0) + count M p := by
  by_cases he : s(a,b) ∈ M <;> simp [count, he, Nat.add_comm]

/-- Expand each designated edge through `w`. -/
def expand {a b : V} : G.Walk a b → H.Walk a b
  | .nil => .nil
  | .cons hab p => if he : s(a,_) ∈ M then
      .cons (replace hab he).1 (.cons (replace hab he).2 (expand p))
    else .cons (keep hab he) (expand p)

@[simp] lemma length_expand {a b : V} (p : G.Walk a b) :
    (expand M w keep replace p).length = p.length + count M p := by
  induction p with
  | nil => rfl
  | @cons a b c hab p ih =>
    by_cases he : s(a,b) ∈ M <;> simp [expand, he, ih] <;> omega

lemma mem_support_expand {a b : V} (p : G.Walk a b) (x : V) :
    x ∈ (expand M w keep replace p).support ↔
      x ∈ p.support ∨ x = w ∧ 0 < count M p := by
  induction p with
  | nil => simp [expand]
  | @cons a b c hab p ih =>
    by_cases he : s(a,b) ∈ M
    · simp only [expand, dif_pos he, Walk.support_cons, List.mem_cons, ih,
        count_cons, if_pos he]
      have hpos : 0 < 1 + count M p := by omega
      simp only [hpos, and_true]
      tauto
    · simp only [expand, dif_neg he, Walk.support_cons, List.mem_cons, ih,
        count_cons, if_neg he, Nat.zero_add]
      tauto

lemma isPath_expand {a b : V} (p : G.Walk a b) (hp : p.IsPath)
    (hw : w ∉ p.support) (hc : count M p ≤ 1) :
    (expand M w keep replace p).IsPath := by
  induction p with
  | nil => simp [expand]
  | @cons a b c hab p ih =>
    have hpath : p.IsPath := hp.of_cons
    have ha : a ∉ p.support := by
      have h := hp.support_nodup
      simp only [Walk.support_cons, List.nodup_cons] at h
      exact h.1
    have hwa : w ≠ a := by simpa using (show w ≠ a ∧ w ∉ p.support by simpa using hw).1
    have hwp : w ∉ p.support := (show w ≠ a ∧ w ∉ p.support by simpa using hw).2
    have hc' : count M p ≤ 1 := by
      rw [count_cons] at hc
      split_ifs at hc <;> omega
    have ih := ih hpath hwp hc'
    have ha' : a ∉ (expand M w keep replace p).support := by
      rw [mem_support_expand]
      exact fun h => h.elim ha (fun h => hwa h.1.symm)
    by_cases he : s(a,b) ∈ M
    · have hz : count M p = 0 := by simpa [he] using hc
      have hw' : w ∉ (expand M w keep replace p).support := by
        simp [mem_support_expand, hwp, hz]
      simp only [expand, dif_pos he]
      apply Walk.IsPath.mk'
      simpa only [Walk.support_cons, List.nodup_cons, List.mem_cons, not_or]
        using And.intro (And.intro (Ne.symm hwa) ha') (And.intro hw' ih.support_nodup)
    · simp only [expand, dif_neg he]
      exact Walk.IsPath.mk' (by simpa using And.intro ha' ih.support_nodup)

set_option backward.isDefEq.respectTransparency.types false in
lemma isCycle_expand {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hw : w ∉ p.support) (hc : count M p ≤ 1) :
    (expand M w keep replace p).IsCycle := by
  cases p with
  | nil => exact False.elim (Walk.not_isCycle_nil hp)
  | @cons a b z hab p =>
    have hpath := (Walk.cons_isCycle_iff p hab).mp hp |>.1
    have hwp : w ∉ p.support := (show w ≠ a ∧ w ∉ p.support by simpa using hw).2
    have hc' : count M p ≤ 1 := by
      rw [count_cons] at hc
      split_ifs at hc <;> omega
    have hpath' := isPath_expand M w keep replace p hpath hwp hc'
    have hlen : 2 ≤ p.length := by
      have h := hp.three_le_length
      simpa only [Walk.length_cons, Nat.add_one_le_add_one_iff] using h
    by_cases he : s(a,b) ∈ M
    · rw [expand, dif_pos he]
      apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
      constructor
      · have hz : count M p = 0 := by simpa [he] using hc
        have hw' : w ∉ (expand M w keep replace p).support := by
          simp [mem_support_expand, hwp, hz]
        change (Walk.cons (replace hab he).2 (expand M w keep replace p)).IsPath
        exact Walk.IsPath.mk' (by simpa using And.intro hw' hpath'.support_nodup)
      · simp only [Walk.length_cons, length_expand]
        omega
    · rw [expand, dif_neg he]
      apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
      constructor
      · simpa only [Walk.getVert_cons_succ, Walk.tail_cons, Walk.isPath_copy] using hpath'
      · simp only [Walk.length_cons, length_expand]
        omega

/-- Every new edge is an old edge or joins the new vertex to a replaced endpoint. -/
lemma edge_source {a b : V} (p : G.Walk a b) {e : Sym2 V}
    (he : e ∈ (expand M w keep replace p).edges) :
    e ∈ p.edges ∨ ∃ f ∈ p.edges, f ∈ M ∧ ∃ x ∈ f, e = s(x,w) := by
  induction p with
  | nil => simp [expand] at he
  | @cons a b c hab p ih =>
    have lift : (e ∈ p.edges ∨ ∃ f ∈ p.edges, f ∈ M ∧ ∃ x ∈ f, e = s(x,w)) →
        e ∈ (Walk.cons hab p).edges ∨
          ∃ f ∈ (Walk.cons hab p).edges, f ∈ M ∧ ∃ x ∈ f, e = s(x,w) := by
      rintro (h | ⟨f,hf,hm,x,hx,heq⟩)
      · exact Or.inl (by simp [h])
      · exact Or.inr ⟨f,by simp [hf],hm,x,hx,heq⟩
    by_cases hm : s(a,b) ∈ M
    · simp only [expand, dif_pos hm, Walk.edges_cons, List.mem_cons] at he
      rcases he with rfl | rfl | he
      · exact Or.inr ⟨s(a,b),by simp,hm,a,Sym2.mem_mk_left _ _,rfl⟩
      · exact Or.inr ⟨s(a,b),by simp,hm,b,Sym2.mem_mk_right _ _,Sym2.eq_swap⟩
      · exact lift (ih he)
    · simp only [expand, dif_neg hm, Walk.edges_cons, List.mem_cons] at he
      rcases he with rfl | he
      · exact Or.inl (by simp)
      · exact lift (ih he)

lemma disjoint_expand {a b : V} (p : G.Walk a a) (q : G.Walk b b)
    (hpw : w ∉ p.support) (hqw : w ∉ q.support)
    (hmatch : ∀ e ∈ M, ∀ f ∈ M, ∀ x, x ∈ e → x ∈ f → e = f)
    (hE : Disjoint p.edges.toFinset q.edges.toFinset) :
    Disjoint (expand M w keep replace p).edges.toFinset
      (expand M w keep replace q).edges.toFinset := by
  apply Finset.disjoint_left.mpr
  intro e he hf
  have hd : ∀ e, e ∈ p.edges → e ∈ q.edges → False := by
    intro e he hf
    exact Finset.disjoint_left.mp hE (List.mem_toFinset.mpr he) (List.mem_toFinset.mpr hf)
  rcases edge_source M w keep replace p (List.mem_toFinset.mp he) with he | ⟨e1,he1,hm1,x,hx,rfl⟩
  · rcases edge_source M w keep replace q (List.mem_toFinset.mp hf) with hf | ⟨e2,he2,hm2,y,hy,rfl⟩
    · exact hd e he hf
    · exact hpw (p.snd_mem_support_of_mem_edges he)
  · rcases edge_source M w keep replace q (List.mem_toFinset.mp hf) with hf | ⟨e2,he2,hm2,y,hy,heq⟩
    · exact hqw (q.snd_mem_support_of_mem_edges hf)
    · have hxy : x = y := by
        have hh : x = y ∨ x = w ∧ w = y := by simpa using heq
        exact hh.elim id (fun h => h.1.trans h.2)
      subst y
      have heq := hmatch e1 hm1 e2 hm2 x hx hy
      exact hd e1 he1 (heq ▸ he2)

lemma count_eq_card {a : V} {p : G.Walk a a} (hp : p.IsCycle) :
    count M p = (p.edges.toFinset.filter (· ∈ M)).card := by
  rw [count, ← List.toFinset_card_of_nodup (hp.edges_nodup.filter _)]
  congr 1
  ext e
  simp

include keep replace in
/-- Matching-edge replacements lift a pair when each cycle uses at most one,
and both use the same number. -/
theorem lift_pair {a b : V} (p : G.Walk a a) (q : G.Walk b b)
    (hp : p.IsCycle) (hq : q.IsCycle)
    (hS : p.support.toFinset = q.support.toFinset)
    (hE : Disjoint p.edges.toFinset q.edges.toFinset)
    (hpw : w ∉ p.support) (hqw : w ∉ q.support)
    (hmatch : ∀ e ∈ M, ∀ f ∈ M, ∀ x, x ∈ e → x ∈ f → e = f)
    (hc : count M p ≤ 1) (heq : count M p = count M q) : HasPairF H := by
  refine ⟨a,b,expand M w keep replace p,expand M w keep replace q,
    isCycle_expand M w keep replace p hp hpw hc,
    isCycle_expand M w keep replace q hq hqw (heq ▸ hc),?_,
    disjoint_expand M w keep replace p q hpw hqw hmatch hE⟩
  ext x
  have hs : x ∈ p.support ↔ x ∈ q.support := by
    simpa only [List.mem_toFinset] using Finset.ext_iff.mp hS x
  simp only [List.mem_toFinset, mem_support_expand, hs, heq]

/-- The new vertex is absent from cycles if it is isolated before lifting. -/
lemma not_mem_support_of_isolated {a : V} {p : G.Walk a a} (hp : p.IsCycle)
    (hw : ∀ x, ¬ G.Adj w x) : w ∉ p.support := by
  intro hmem
  have hcyc := hp.rotate hmem
  exact hw _ ((p.rotate w hmem).adj_snd hcyc.not_nil)

include keep replace in
/-- Full cycle-pair lift through a vertex from at most three matching edges.
The independent color class supplies the required balance. -/
theorem hasPairF_of_three_matching_edges
    (c : V → Bool)
    (hc : ∀ a b, G.Adj a b → c a = true ∨ c b = true)
    (hex : ∀ e ∈ G.edgeSet, BipartiteBalance.sameTrue c e ↔ e ∈ M)
    (hsize : M.card ≤ 3)
    (hmatch : ∀ e ∈ M, ∀ f ∈ M, ∀ x, x ∈ e → x ∈ f → e = f)
    (hw : ∀ x, ¬ G.Adj w x) (hp : HasPairF G) : HasPairF H := by
  classical
  rcases hp with ⟨a,b,p,q,hp,hq,hS,hE⟩
  have hcounts := BipartiteBalance.at_most_one_exceptional c M hc
    (fun e he => (hex e he).mp) hsize hp hq hS hE
  have eqfilter : ∀ {a : V} (p : G.Walk a a),
      p.edges.toFinset.filter (BipartiteBalance.sameTrue c) =
      p.edges.toFinset.filter (· ∈ M) := by
    intro a p
    apply Finset.filter_congr
    intro e he
    exact hex e (p.edges_subset_edgeSet (List.mem_toFinset.mp he))
  rw [eqfilter p, eqfilter q, ← count_eq_card M hp, ← count_eq_card M hq] at hcounts
  exact lift_pair M w keep replace p q hp hq hS hE
    (not_mem_support_of_isolated w hp hw) (not_mem_support_of_isolated w hq hw)
    hmatch hcounts.1 hcounts.2

/-- Delete `w` and add the designated matching edges on the remaining vertices.
The deleted vertex is retained as an isolated vertex in the ambient type. -/
def splitGraph (G : SimpleGraph V) (w : V) (M : Finset (Sym2 V)) : SimpleGraph V where
  Adj a b := a ≠ b ∧ a ≠ w ∧ b ≠ w ∧ (G.Adj a b ∨ s(a,b) ∈ M)
  symm := ⟨by
    intro a b h
    refine ⟨h.1.symm,h.2.2.1,h.2.1,?_⟩
    exact h.2.2.2.elim (fun h => Or.inl h.symm)
      (fun h => Or.inr (by simpa only [Sym2.eq_swap] using h))⟩
  loopless := ⟨fun a h => h.1 rfl⟩

/-- Splitting up to six neighbors of a bipartite vertex into a matching
preserves absence of the faithful forbidden pair. -/
theorem splitGraph_pairfree (G : SimpleGraph V) (w : V) (M : Finset (Sym2 V))
    (c : V → Bool) (hcw : c w = false)
    (hc : ∀ a b, G.Adj a b → c a ≠ c b)
    (hneighbors : ∀ a b, s(a,b) ∈ M → G.Adj w a ∧ G.Adj w b)
    (hsize : M.card ≤ 3)
    (hmatch : ∀ e ∈ M, ∀ f ∈ M, ∀ x, x ∈ e → x ∈ f → e = f)
    (hfree : ¬ HasPairF G) : ¬ HasPairF (splitGraph G w M) := by
  intro hpair
  apply hfree
  have hcolor : ∀ a b, s(a,b) ∈ M → c a = true ∧ c b = true := by
    intro a b he
    have ha := hc w a (hneighbors a b he).1
    have hb := hc w b (hneighbors a b he).2
    cases hca : c a <;> cases hcb : c b <;> simp_all
  refine hasPairF_of_three_matching_edges (G := splitGraph G w M) (H := G) M w
    (fun {a b} hab he => hab.2.2.2.resolve_right he)
    (fun {a b} _ he => ⟨(hneighbors a b he).1.symm,(hneighbors a b he).2⟩)
    c ?_ ?_ hsize hmatch (fun _ h => h.2.1 rfl) hpair
  · intro a b hab
    rcases hab.2.2.2 with hab | hm
    · have h := hc a b hab
      cases hca : c a <;> cases hcb : c b <;> simp_all
    · exact Or.inl (hcolor a b hm).1
  · intro e he
    induction e using Sym2.inductionOn with | _ a b => ?_
    have hab : (splitGraph G w M).Adj a b := he
    constructor
    · intro ht
      rcases hab.2.2.2 with hg | hm
      · have h := hc a b hg
        exact False.elim (h ((ht a (Sym2.mem_mk_left _ _)).trans
          (ht b (Sym2.mem_mk_right _ _)).symm))
      · exact hm
    · intro hm x hx
      have hcols := hcolor a b hm
      rcases Sym2.mem_iff.mp hx with rfl | rfl
      · exact hcols.1
      · exact hcols.2

end Erdos585.CycleLift
