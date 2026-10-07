import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-!+# Numerical growth for the characteristic-three parabola family

The literal degree `3^k` eventually exceeds every fixed real power of
the logarithm of the literal vertex count `2 * 3^(2*k)`.
-/

namespace Erdos585.ParabolaGrowth104

open Filter

/-- The exact logarithmic ledger for the vertex count. -/
theorem log_vertex_count (k : ℕ) :
    Real.log (2 * (3 : ℝ) ^ (2 * k)) =
      Real.log 2 + 2 * (k : ℝ) * Real.log 3 := by
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
    (pow_ne_zero (2 * k) (by norm_num : (3 : ℝ) ≠ 0)), Real.log_pow]
  simp only [Nat.cast_mul, Nat.cast_ofNat]

/-- The logarithm of the vertex count is nonnegative, including at `k = 0`. -/
theorem log_vertex_count_nonneg (k : ℕ) :
    0 ≤ Real.log (2 * (3 : ℝ) ^ (2 * k)) := by
  rw [log_vertex_count]
  have h₂ := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
  have h₃ := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3)
  positivity

/-- A uniform linear upper bound for the literal logarithm. -/
theorem log_vertex_count_le_five_mul (k : ℕ) (hk : 1 ≤ k) :
    Real.log (2 * (3 : ℝ) ^ (2 * k)) ≤ 5 * (k : ℝ) := by
  rw [log_vertex_count]
  have hk' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have h₂ : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have h₃ : Real.log 3 ≤ 2 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    linarith
  calc
    Real.log 2 + 2 * (k : ℝ) * Real.log 3 ≤ 1 + 2 * (k : ℝ) * 2 :=
      add_le_add h₂ (mul_le_mul_of_nonneg_left h₃ (by positivity))
    _ ≤ 5 * (k : ℝ) := by linarith

/-- Every fixed real polylogarithmic threshold is eventually below the degree. -/
theorem eventually_polylog_lt_pow_three (C A : ℝ) (hC : 0 < C) (hA : 0 ≤ A) :
    ∀ᶠ k : ℕ in Filter.atTop,
      C * Real.rpow (Real.log (2 * (3 : ℝ) ^ (2 * k))) A < (3 : ℝ) ^ k := by
  have hlim : Tendsto
      (fun k : ℕ => Real.exp (Real.log 3 * (k : ℝ)) / (k : ℝ) ^ A) atTop atTop :=
    (tendsto_exp_mul_div_rpow_atTop A (Real.log 3)
      (Real.log_pos (by norm_num : (1 : ℝ) < 3))).comp tendsto_natCast_atTop_atTop
  filter_upwards [hlim.eventually_gt_atTop (C * (5 : ℝ) ^ A),
    eventually_ge_atTop (1 : ℕ)] with k hlarge hk
  have hkpos : (0 : ℝ) < (k : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hpowpos : 0 < (k : ℝ) ^ A := Real.rpow_pos_of_pos hkpos A
  have hexp : Real.exp (Real.log 3 * (k : ℝ)) = (3 : ℝ) ^ k := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
  rw [hexp] at hlarge
  have hdom : C * (5 : ℝ) ^ A * (k : ℝ) ^ A < (3 : ℝ) ^ k :=
    (lt_div_iff₀ hpowpos).mp hlarge
  calc
    C * Real.rpow (Real.log (2 * (3 : ℝ) ^ (2 * k))) A ≤
        C * Real.rpow (5 * (k : ℝ)) A :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (log_vertex_count_nonneg k)
          (log_vertex_count_le_five_mul k hk) hA) hC.le
    _ = C * (5 : ℝ) ^ A * (k : ℝ) ^ A := by
      change C * ((5 * (k : ℝ)) ^ A) = C * (5 : ℝ) ^ A * (k : ℝ) ^ A
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 5) (Nat.cast_nonneg k)]
      ring
    _ < (3 : ℝ) ^ k := hdom

/-- The degree beats a fixed real polylogarithm at arbitrarily large indices `k ≥ 2`. -/
theorem exists_polylog_lt_pow_three (C A : ℝ) (hC : 0 < C) (hA : 0 ≤ A)
    (K : ℕ) :
    ∃ k : ℕ, K ≤ k ∧ 2 ≤ k ∧
      C * Real.rpow (Real.log (2 * (3 : ℝ) ^ (2 * k))) A < (3 : ℝ) ^ k := by
  obtain ⟨k, hineq, hK, htwo⟩ :=
    ((eventually_polylog_lt_pow_three C A hC hA).and
      ((eventually_ge_atTop K).and (eventually_ge_atTop (2 : ℕ)))).exists
  exact ⟨k, hK, htwo, hineq⟩

end Erdos585.ParabolaGrowth104
