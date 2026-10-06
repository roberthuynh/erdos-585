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
import Openmath.Proofs.MatchingJoinDefs

/-! # Actual disjoint-support path bridges and closing cycles -/

open SimpleGraph Finset
namespace Erdos585.MatchingJoin

variable {V : Type*} {G : SimpleGraph V}

def bridge {a b c d : V} (p : G.Walk a b) (q : G.Walk c d) (h : G.Adj b c) :
    G.Walk a d := p.append (q.cons h)

@[simp] theorem support_bridge {a b c d : V} (p : G.Walk a b) (q : G.Walk c d)
    (h : G.Adj b c) : (bridge p q h).support = p.support ++ q.support := by
  simp [bridge, Walk.support_append]

@[simp] theorem edges_bridge {a b c d : V} (p : G.Walk a b) (q : G.Walk c d)
    (h : G.Adj b c) : (bridge p q h).edges = p.edges ++ s(b,c) :: q.edges := by
  simp [bridge]

theorem bridge_isPath {a b c d : V} (p : G.Walk a b) (q : G.Walk c d)
    (h : G.Adj b c) (hp : p.IsPath) (hq : q.IsPath)
    (hd : p.support.Disjoint q.support) : (bridge p q h).IsPath := by
  apply Walk.IsPath.mk'
  rw [support_bridge, List.nodup_append']
  exact ⟨hp.support_nodup, hq.support_nodup, hd⟩

def Mono (color : V → Bool) (s : Bool) {a b : V} (p : G.Walk a b) : Prop :=
  ∀ v ∈ p.support, color v = s

theorem Mono.edge {color : V → Bool} {s : Bool} {a b : V} {p : G.Walk a b}
    (hp : Mono color s p) {e : Sym2 V} (he : e ∈ p.edges) :
    Sym2.map color e = s(s,s) := by
  induction e using Sym2.inductionOn with
  | _ u v =>
    simp only [Sym2.map_mk]
    rw [hp u (p.fst_mem_support_of_mem_edges he), hp v (p.snd_mem_support_of_mem_edges he)]

theorem Mono.support_disjoint {color : V → Bool} {a b c d : V}
    {p : G.Walk a b} {q : G.Walk c d} (hp : Mono color false p) (hq : Mono color true q) :
    p.support.Disjoint q.support := by
  intro x hx hy
  exact Bool.false_ne_true ((hp x hx).symm.trans (hq x hy))

theorem Mono.edges_disjoint {color : V → Bool} {a b c d : V}
    {p : G.Walk a b} {q : G.Walk c d} (hp : Mono color false p) (hq : Mono color true q) :
    p.edges.Disjoint q.edges := by
  intro e he hf
  have hh := (hp.edge he).symm.trans (hq.edge hf)
  exact (by decide : s(false,false) ≠ s(true,true)) hh

theorem Mono.not_cross {color : V → Bool} {s : Bool} {a b u v : V}
    {p : G.Walk a b} (hp : Mono color s p) (hu : color u = false) (hv : color v = true) :
    s(u,v) ∉ p.edges := by
  intro he
  have hh := hp.edge he
  simp only [Sym2.map_mk, hu, hv] at hh
  cases s <;> exact (by decide : s(false,true) ≠ _) hh

theorem cross_ne {color : V → Bool} {a b c d : V}
    (ha : color a = false) (_hb : color b = true)
    (_hc : color c = false) (hd : color d = true) (hac : a ≠ c) : s(a,b) ≠ s(c,d) := by
  intro h
  rcases (Sym2.eq_iff.mp h) with h | h
  · exact hac h.1
  · have hh := congrArg color h.1
    rw [ha, hd] at hh
    exact Bool.false_ne_true hh

theorem bridge_close_cycle {a b c d : V} (p : G.Walk a b) (q : G.Walk c d)
    (hbc : G.Adj b c) (hda : G.Adj d a) (hp : p.IsPath) (hq : q.IsPath)
    (hd : p.support.Disjoint q.support) (hab : a ≠ b) :
    ((bridge p q hbc).cons hda).IsCycle := by
  rw [Walk.cons_isCycle_iff]
  refine ⟨bridge_isPath p q hbc hp hq hd, ?_⟩
  rw [edges_bridge]
  simp only [List.mem_append, List.mem_cons, not_or]
  refine ⟨?_, ?_, ?_⟩
  · intro he
    exact hd (p.fst_mem_support_of_mem_edges he) q.end_mem_support
  · intro he
    rcases Sym2.eq_iff.mp he with h | h
    · exact hd p.end_mem_support (h.1 ▸ q.end_mem_support)
    · exact hab h.2
  · intro he
    exact hd p.start_mem_support (q.snd_mem_support_of_mem_edges he)

theorem bridges_disjoint [DecidableEq V] {color : V → Bool}
    {a₀ b₀ c₀ d₀ a₁ b₁ c₁ d₁ : V}
    (r₀ : G.Walk a₀ b₀) (t₀ : G.Walk c₀ d₀)
    (r₁ : G.Walk a₁ b₁) (t₁ : G.Walk c₁ d₁)
    (hr : G.Adj b₀ a₁) (ht : G.Adj d₀ c₁)
    (hmr₀ : Mono color false r₀) (hmt₀ : Mono color false t₀)
    (hmr₁ : Mono color true r₁) (hmt₁ : Mono color true t₁)
    (he₀ : Disjoint r₀.edges.toFinset t₀.edges.toFinset)
    (he₁ : Disjoint r₁.edges.toFinset t₁.edges.toFinset) (hbd : b₀ ≠ d₀) :
    Disjoint (bridge r₀ r₁ hr).edges.toFinset (bridge t₀ t₁ ht).edges.toFinset := by
  have hnrt₀ := hmt₀.not_cross (hmr₀ _ r₀.end_mem_support) (hmr₁ _ r₁.start_mem_support)
  have hnrt₁ := hmt₁.not_cross (hmr₀ _ r₀.end_mem_support) (hmr₁ _ r₁.start_mem_support)
  have hntr₀ := hmr₀.not_cross (hmt₀ _ t₀.end_mem_support) (hmt₁ _ t₁.start_mem_support)
  have hntr₁ := hmr₁.not_cross (hmt₀ _ t₀.end_mem_support) (hmt₁ _ t₁.start_mem_support)
  have hne := cross_ne (hmr₀ _ r₀.end_mem_support) (hmr₁ _ r₁.start_mem_support)
    (hmt₀ _ t₀.end_mem_support) (hmt₁ _ t₁.start_mem_support) hbd
  apply Finset.disjoint_left.mpr
  intro e he hf
  simp only [List.mem_toFinset, edges_bridge, List.mem_append, List.mem_cons] at he hf
  rcases he with he | rfl | he
  · rcases hf with hf | rfl | hf
    · exact Finset.disjoint_left.mp he₀ (List.mem_toFinset.mpr he) (List.mem_toFinset.mpr hf)
    · exact hntr₀ he
    · exact hmr₀.edges_disjoint hmt₁ he hf
  · rcases hf with hf | hf | hf
    · exact hnrt₀ hf
    · exact hne hf
    · exact hnrt₁ hf
  · rcases hf with hf | rfl | hf
    · exact hmt₀.edges_disjoint hmr₁ hf he
    · exact hntr₁ he
    · exact Finset.disjoint_left.mp he₁ (List.mem_toFinset.mpr he) (List.mem_toFinset.mpr hf)

end Erdos585.MatchingJoin
