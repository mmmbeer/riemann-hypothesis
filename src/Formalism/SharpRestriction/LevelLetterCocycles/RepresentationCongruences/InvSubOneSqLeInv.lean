import Mathlib

namespace Formalism.MainNotions.N.FrobeniusPowerSeries.NumericInequalities

variable {x : ℝ}

lemma p_le (hx : 11 ≤ x) : (x - 1)⁻¹ ≤ 1 / 10 := by
  have h0 : 0 < x := by linarith
  have h1 : 0 < x - 1 := by linarith
  have h2 : 0 < x - 2 := by linarith
  have h : 0 ≤ x - 11 := by linarith
  have n0 : x ≠ 0 := h0.ne'
  have n1 : x - 1 ≠ 0 := h1.ne'
  have n2 : x - 2 ≠ 0 := h2.ne'
  have e : 1 / 10 - (x - 1)⁻¹ = (x - 11) / (10 * (x - 1)) := by
    field_simp <;> ring
  have hd : 0 ≤ 1 / 10 - (x - 1)⁻¹ := by
    rw [e]
    exact div_nonneg (by linarith) (mul_nonneg (by norm_num) h1.le)
  linarith

lemma q_le (hx : 11 ≤ x) : x / (x - 1) ^ 2 ≤ 121 / 100 * x⁻¹ := by
  have h0 : 0 < x := by linarith
  have h1 : 0 < x - 1 := by linarith
  have h2 : 0 < x - 2 := by linarith
  have h : 0 ≤ x - 11 := by linarith
  have n0 : x ≠ 0 := h0.ne'
  have n1 : x - 1 ≠ 0 := h1.ne'
  have n2 : x - 2 ≠ 0 := h2.ne'
  have e : 121 / 100 * x⁻¹ - x / (x - 1) ^ 2 = (21 * x ^ 2 - 242 * x + 121) / (100 * x * (x - 1) ^ 2) := by
    field_simp <;> ring
  have hd : 0 ≤ 121 / 100 * x⁻¹ - x / (x - 1) ^ 2 := by
    rw [e]
    exact div_nonneg (by nlinarith [h, mul_nonneg h h]) (mul_nonneg (mul_nonneg (by norm_num) h0.le) (sq_nonneg _))
  linarith


lemma p_le_u (hx : 11 ≤ x) : (x - 1)⁻¹ ≤ 11 / 10 * x⁻¹ := by
  have h0 : 0 < x := by linarith
  have h1 : 0 < x - 1 := by linarith
  have h2 : 0 < x - 2 := by linarith
  have h : 0 ≤ x - 11 := by linarith
  have n0 : x ≠ 0 := h0.ne'
  have n1 : x - 1 ≠ 0 := h1.ne'
  have n2 : x - 2 ≠ 0 := h2.ne'
  have e : 11 / 10 * x⁻¹ - (x - 1)⁻¹ = (x - 11) / (10 * x * (x - 1)) := by
    field_simp <;> ring
  have hd : 0 ≤ 11 / 10 * x⁻¹ - (x - 1)⁻¹ := by
    rw [e]
    exact div_nonneg (by linarith) (mul_nonneg (mul_nonneg (by norm_num) h0.le) h1.le)
  linarith



end Formalism.MainNotions.N.FrobeniusPowerSeries.NumericInequalities
