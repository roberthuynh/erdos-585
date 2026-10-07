import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# A deterministic probe for a local matching

An edge is selected when its priority is strictly smaller than that of every
other incident edge. Add a new vertex on the left, joined to a test set on the
right. The unmatched counts before and after adding the probe differ only
through selected probe edges and new column records.

This is an auxiliary matching lemma, not a cycle theorem for Erdős 585.
-/

namespace Erdos585.LocalMatchingProbe

variable {A B P : Type*} [LinearOrder P]

def selected (E : A → B → Prop) (r : A → B → P) (a : A) (b : B) : Prop :=
  E a b ∧
    (∀ b', E a b' → b' ≠ b → r a b < r a b') ∧
    (∀ a', E a' b → a' ≠ a → r a b < r a' b)

def retained (E : A → B → Prop) (r : A → B → P)
    (T : Finset B) (s : B → P) (a : A) (b : B) : Prop :=
  selected E r a b ∧ (b ∈ T → r a b < s b)

def starSelected (E : A → B → Prop) (r : A → B → P)
    (T : Finset B) (s : B → P) (b : B) : Prop :=
  b ∈ T ∧ (∀ b' ∈ T, b' ≠ b → s b < s b') ∧ (∀ a, E a b → s b < r a b)

def record (E : A → B → Prop) (r : A → B → P) (s : B → P) (b : B) : Prop :=
  ∀ a, E a b → s b ≤ r a b

def augmentedEdges (E : A → B → Prop) (T : Finset B) : Option A → B → Prop
  | none, b => b ∈ T
  | some a, b => E a b

def augmentedPriority (r : A → B → P) (s : B → P) : Option A → B → P
  | none, b => s b
  | some a, b => r a b

theorem selected_some_iff (E : A → B → Prop) (r : A → B → P)
    (T : Finset B) (s : B → P) (a : A) (b : B) :
    selected (augmentedEdges E T) (augmentedPriority r s) (some a) b ↔
      retained E r T s a b := by
  constructor
  · rintro ⟨he, hr, hc⟩
    refine ⟨⟨he, hr, ?_⟩, ?_⟩
    · intro a' he' hne
      exact hc (some a') he' (by simpa using hne)
    · intro hb
      exact hc none hb (by simp)
  · rintro ⟨⟨he, hr, hc⟩, hs⟩
    refine ⟨he, hr, ?_⟩
    intro a' he' hne
    cases a' with
    | none => exact hs he'
    | some a' => exact hc a' he' (by simpa using hne)

theorem selected_none_iff (E : A → B → Prop) (r : A → B → P)
    (T : Finset B) (s : B → P) (b : B) :
    selected (augmentedEdges E T) (augmentedPriority r s) none b ↔
      starSelected E r T s b := by
  constructor
  · rintro ⟨he, hr, hc⟩
    refine ⟨he, hr, ?_⟩
    intro a ha
    exact hc (some a) ha (by simp)
  · rintro ⟨he, hr, hc⟩
    refine ⟨he, hr, ?_⟩
    intro a' he' hne
    cases a' with
    | none => exact False.elim (hne rfl)
    | some a => exact hc a he'

theorem star_unique (E : A → B → Prop) (r : A → B → P)
    (T : Finset B) (s : B → P) {b c : B}
    (hb : starSelected E r T s b) (hc : starSelected E r T s c) : b = c := by
  by_contra hne
  exact lt_asymm (hb.2.1 c hc.1 (Ne.symm hne)) (hc.2.1 b hb.1 hne)

theorem lost_implies_record (E : A → B → Prop) (r : A → B → P)
    (T : Finset B) (s : B → P) {a : A} {b : B}
    (hsel : selected E r a b) (hlost : ¬retained E r T s a b) :
    record E r s b := by
  have hs : s b ≤ r a b := by
    by_contra h
    exact hlost ⟨hsel, fun _ => lt_of_not_ge h⟩
  intro a' he'
  by_cases ha : a' = a
  · subst a'
    exact hs
  · exact hs.trans (hsel.2.2 a' he' ha).le

noncomputable def oldUnmatched (E : A → B → Prop) (r : A → B → P)
    (T : Finset B) : Finset B := by
  classical
  exact T.filter (fun b => ¬∃ a, selected E r a b)

noncomputable def newUnmatched (E : A → B → Prop) (r : A → B → P)
    (T : Finset B) (s : B → P) : Finset B := by
  classical
  exact T.filter (fun b => ¬∃ a, selected (augmentedEdges E T) (augmentedPriority r s) a b)

noncomputable def records (E : A → B → Prop) (r : A → B → P)
    (T : Finset B) (s : B → P) : Finset B := by
  classical
  exact T.filter (record E r s)

theorem probe_unmatched_bounds (E : A → B → Prop) (r : A → B → P)
    (T : Finset B) (s : B → P) :
    (oldUnmatched E r T).card ≤ (newUnmatched E r T s).card + 1 ∧
    (newUnmatched E r T s).card ≤
      (oldUnmatched E r T).card + (records E r T s).card := by
  classical
  let S := T.filter (starSelected E r T s)
  have hS : S.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro b hb c hc
    exact star_unique E r T s (Finset.mem_filter.mp hb).2 (Finset.mem_filter.mp hc).2
  have hold : oldUnmatched E r T ⊆ newUnmatched E r T s ∪ S := by
    intro b hb
    obtain ⟨hbT, hbOld⟩ := Finset.mem_filter.mp hb
    by_cases hn : b ∈ newUnmatched E r T s
    · exact Finset.mem_union_left _ hn
    · have hc : ∃ a, selected (augmentedEdges E T) (augmentedPriority r s) a b := by
        by_contra h
        exact hn (Finset.mem_filter.mpr ⟨hbT, h⟩)
      obtain ⟨a, ha⟩ := hc
      cases a with
      | none =>
        exact Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨hbT, (selected_none_iff E r T s b).mp ha⟩)
      | some a =>
        exact False.elim (hbOld ⟨a, ((selected_some_iff E r T s a b).mp ha).1⟩)
  have hnew : newUnmatched E r T s ⊆ oldUnmatched E r T ∪ records E r T s := by
    intro b hb
    obtain ⟨hbT, hbNew⟩ := Finset.mem_filter.mp hb
    by_cases ho : b ∈ oldUnmatched E r T
    · exact Finset.mem_union_left _ ho
    · have hc : ∃ a, selected E r a b := by
        by_contra h
        exact ho (Finset.mem_filter.mpr ⟨hbT, h⟩)
      obtain ⟨a, ha⟩ := hc
      have hlost : ¬retained E r T s a b := by
        intro hr
        exact hbNew ⟨some a, (selected_some_iff E r T s a b).mpr hr⟩
      exact Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨hbT, lost_implies_record E r T s ha hlost⟩)
  constructor
  · have h := (Finset.card_le_card hold).trans (Finset.card_union_le _ _)
    omega
  · exact (Finset.card_le_card hnew).trans (Finset.card_union_le _ _)

end Erdos585.LocalMatchingProbe
