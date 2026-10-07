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
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Tactic

/-! # Prime-field closure of the characteristic-three parabola

The span is over `ZMod 3`, not the ambient field. Every affine span of
three parabola points contains no fourth point, including repeated colors.
The full parabola spans the whole product over the prime field.
-/

namespace Erdos585.Parabola104

variable {F : Type*} [Field F]

/-- The literal translation assigned to color `a`. -/
def point (a : F) : F × F := (a, a ^ 2)

@[simp] theorem point_fst (a : F) : (point a).1 = a := rfl

@[simp] theorem point_snd (a : F) : (point a).2 = a ^ 2 := rfl

@[simp] theorem point_zero : point (0 : F) = 0 := by simp [point]

theorem point_injective : Function.Injective (point : F → F × F) := by
  intro a b h
  exact congrArg Prod.fst h

variable [CharP F 3]

private theorem two_ne_zero : (2 : F) ≠ 0 := by
  intro h
  have hd : 3 ∣ 2 := (CharP.cast_eq_zero_iff F 3 2).mp h
  norm_num at hd

/-- Pair sums on the parabola determine the unordered pair, with multiplicity. -/
theorem point_pair_sum {a b c d : F}
    (h : point a + point b = point c + point d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have h₁ : a + b = c + d := congrArg Prod.fst h
  have h₂ : a ^ 2 + b ^ 2 = c ^ 2 + d ^ 2 := congrArg Prod.snd h
  have hp : (2 : F) * ((a - c) * (a - d)) = 0 := by
    linear_combination h₂ - (b - a + c + d) * h₁
  have hp' : (a - c) * (a - d) = 0 :=
    (mul_eq_zero.mp hp).resolve_left two_ne_zero
  rcases mul_eq_zero.mp hp' with hac | had
  · have hac' : a = c := sub_eq_zero.mp hac
    exact Or.inl ⟨hac', by linear_combination h₁ - hac'⟩
  · have had' : a = d := sub_eq_zero.mp had
    exact Or.inr ⟨had', by linear_combination h₁ - had'⟩

/-- A zero sum of three parabola points has three equal color parameters. -/
theorem point_triple_sum {a b c : F}
    (h : point a + point b + point c = 0) : a = b ∧ b = c := by
  have h₁ : a + b + c = 0 := congrArg Prod.fst h
  have h₂ : a ^ 2 + b ^ 2 + c ^ 2 = 0 := congrArg Prod.snd h
  have h₃ : (3 : F) = 0 := CharP.cast_eq_zero F 3
  have hp : (2 : F) * (a - b) ^ 2 = 0 := by
    linear_combination h₂ - (c - a - b) * h₁ - (2 * a * b) * h₃
  have hs : (a - b) ^ 2 = 0 := (mul_eq_zero.mp hp).resolve_left two_ne_zero
  have hab : a = b := sub_eq_zero.mp (eq_zero_of_pow_eq_zero hs)
  refine ⟨hab, ?_⟩
  linear_combination -h₁ + hab + b * h₃

private theorem point_triple_self (a : F) : point a + point a + point a = 0 := by
  have h₃ : (3 : F) = 0 := CharP.cast_eq_zero F 3
  apply Prod.ext
  · change a + a + a = 0
    linear_combination a * h₃
  · change a ^ 2 + a ^ 2 + a ^ 2 = 0
    linear_combination a ^ 2 * h₃

private theorem scalar_three_cases (u : ZMod 3) : u = 0 ∨ u = 1 ∨ u = -1 := by
  fin_cases u
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

variable [Algebra (ZMod 3) F]

/-- The prime-field affine span of at most three colors has no additional color. -/
theorem point_span_pair (a b c z : F)
    (h : point z - point a ∈ Submodule.span (ZMod 3)
      ({point b - point a, point c - point a} : Set (F × F))) :
    z = a ∨ z = b ∨ z = c := by
  obtain ⟨u, v, huv⟩ := Submodule.mem_span_pair.mp h
  rcases scalar_three_cases u with rfl | rfl | rfl <;>
    rcases scalar_three_cases v with rfl | rfl | rfl <;>
    simp only [zero_smul, one_smul, neg_one_smul, zero_add, add_zero] at huv
  · left
    apply point_injective
    linear_combination -huv
  · right; right
    apply point_injective
    linear_combination -huv
  · have hp : point z + point c = point a + point a := by
      linear_combination -huv
    rcases point_pair_sum hp with ⟨hza, _⟩ | ⟨hza, _⟩ <;> exact Or.inl hza
  · right; left
    apply point_injective
    linear_combination -huv
  · have hp : point z + point a = point b + point c := by
      linear_combination -huv
    rcases point_pair_sum hp with ⟨hzb, _⟩ | ⟨hzc, _⟩
    · exact Or.inr (Or.inl hzb)
    · exact Or.inr (Or.inr hzc)
  · have hp : point z + point c = point a + point b := by
      linear_combination -huv
    rcases point_pair_sum hp with ⟨hza, _⟩ | ⟨hzb, _⟩
    · exact Or.inl hza
    · exact Or.inr (Or.inl hzb)
  · have hp : point z + point b = point a + point a := by
      linear_combination -huv
    rcases point_pair_sum hp with ⟨hza, _⟩ | ⟨hza, _⟩ <;> exact Or.inl hza
  · have hp : point z + point b = point a + point c := by
      linear_combination -huv
    rcases point_pair_sum hp with ⟨hza, _⟩ | ⟨hzc, _⟩
    · exact Or.inl hza
    · exact Or.inr (Or.inr hzc)
  · have hp : point z + point b + point c = 0 := by
      linear_combination -huv + point_triple_self a
    exact Or.inr (Or.inl (point_triple_sum hp).1)

/-- The whole parabola spans the product over the prime field. -/
theorem span_range_point_eq_top :
    Submodule.span (ZMod 3) (Set.range (point : F → F × F)) = ⊤ := by
  let W := Submodule.span (ZMod 3) (Set.range (point : F → F × F))
  have hp (a : F) : point a ∈ W := Submodule.subset_span ⟨a, rfl⟩
  have h₃ : (3 : F) = 0 := CharP.cast_eq_zero F 3
  have hs (a : F) : (0, a ^ 2) ∈ W := by
    have he : -(point a + point (-a)) = (0, a ^ 2) := by
      apply Prod.ext
      · change -(a + -a) = 0
        simp
      · change -(a ^ 2 + (-a) ^ 2) = a ^ 2
        linear_combination -(a ^ 2) * h₃
    rw [← he]
    exact W.neg_mem (W.add_mem (hp a) (hp (-a)))
  have hv (z : F) : (0, z) ∈ W := by
    have he : ((0, (z + 1) ^ 2) : F × F) - (0, (z - 1) ^ 2) = (0, z) := by
      apply Prod.ext
      · simp
      · change (z + 1) ^ 2 - (z - 1) ^ 2 = z
        linear_combination z * h₃
    rw [← he]
    exact W.sub_mem (hs (z + 1)) (hs (z - 1))
  have hh (x : F) : (x, 0) ∈ W := by
    have he : point x - (0, x ^ 2) = (x, 0) := by
      ext <;> simp [point]
    rw [← he]
    exact W.sub_mem (hp x) (hv (x ^ 2))
  change W = ⊤
  apply top_unique
  rintro ⟨x, y⟩ _
  simpa using W.add_mem (hh x) (hv y)

end Erdos585.Parabola104
