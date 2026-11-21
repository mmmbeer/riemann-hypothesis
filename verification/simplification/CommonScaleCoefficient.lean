import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open Finset

namespace CommonScale

/-- The total absolute deviation of numbers in [-1,1] from their mean is at
most the sample size. The variance bound also covers singleton samples. -/
private theorem sum_abs_centered_le {ι : Type*} (T : Finset ι) (d : ι → ℝ)
    (hd : ∀ t ∈ T, |d t| ≤ 1) (μ : ℝ) (hμ : ∑ t ∈ T, d t = T.card * μ) :
    ∑ t ∈ T, |d t - μ| ≤ T.card := by
  have hpoint (t) (ht : t ∈ T) :
      2 * |d t - μ| ≤ 2 - 2 * μ * d t + μ ^ 2 := by
    obtain ⟨hl, hu⟩ := abs_le.mp (hd t ht)
    nlinarith [sq_nonneg (|d t - μ| - 1), sq_abs (d t - μ),
      mul_nonneg (sub_nonneg.mpr hu) (show 0 ≤ 1 + d t by linarith)]
  have h := Finset.sum_le_sum hpoint
  simp only [← mul_sum, sum_add_distrib, sum_sub_distrib, sum_const, nsmul_eq_mul, hμ] at h
  nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) T.card) (sq_nonneg μ)]

/-- For orders a(t)/b = x + d(t), replacing uniform weights by a(t)/x
changes each normalized character coefficient by at most 1/(x-1).
The observable z may be any function bounded by one in norm. -/
theorem coefficient_change {ι : Type*} (T : Finset ι) (hT : T.Nonempty)
    (d : ι → ℝ) (z : ι → ℂ) (hd : ∀ t ∈ T, |d t| ≤ 1)
    (hz : ∀ t ∈ T, ‖z t‖ ≤ 1) {x : ℝ} (hx : 1 < x) :
    ‖(∑ t ∈ T, ((x + d t : ℝ) : ℂ) * z t) / ((∑ t ∈ T, (x + d t) : ℝ) : ℂ)
      - (∑ t ∈ T, z t) / (T.card : ℂ)‖ ≤ 1 / (x - 1) := by
  let n : ℝ := T.card
  have hn : 0 < n := Nat.cast_pos.mpr (Finset.card_pos.mpr hT)
  let μ := (∑ t ∈ T, d t) / n
  have hμ : ∑ t ∈ T, d t = n * μ := by dsimp [μ]; field_simp [hn.ne']
  have hlo : -n ≤ ∑ t ∈ T, d t := by
    calc
      -n = ∑ _t ∈ T, (-1 : ℝ) := by simp [n]
      _ ≤ _ := Finset.sum_le_sum fun t ht => (abs_le.mp (hd t ht)).1
  have hm : -1 ≤ μ := (le_div_iff₀ hn).mpr (by simpa using hlo)
  let W := ∑ t ∈ T, (x + d t)
  have hW : W = n * (x + μ) := by
    change ∑ t ∈ T, (x + d t) = n * (x + μ)
    rw [sum_add_distrib, sum_const, nsmul_eq_mul, hμ, mul_add]
  have hWpos : 0 < W := hW ▸ mul_pos hn (by linarith)
  have he : (∑ t ∈ T, ((x + d t : ℝ) : ℂ) * z t) / (W : ℂ) - (∑ t ∈ T, z t) / (n : ℂ)
      = (∑ t ∈ T, ((d t - μ : ℝ) : ℂ) * z t) / (W : ℂ) := by
    have hns : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    have hws : (W : ℂ) ≠ 0 := by exact_mod_cast hWpos.ne'
    field_simp [hns, hws]
    rw [hW]
    push_cast
    simp only [add_mul, sub_mul, sum_add_distrib, sum_sub_distrib, ← mul_sum]
    ring
  change ‖_ / (W : ℂ) - _ / (n : ℂ)‖ ≤ _
  rw [he, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hWpos]
  have hnum : ‖∑ t ∈ T, ((d t - μ : ℝ) : ℂ) * z t‖ ≤ n := by
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum ?_).trans (sum_abs_centered_le T d hd μ hμ))
    intro t ht
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg _) (hz t ht)
  rw [div_le_div_iff₀ hWpos (sub_pos.mpr hx), one_mul]
  exact (mul_le_mul_of_nonneg_right hnum (by linarith)).trans
    (hW ▸ mul_le_mul_of_nonneg_left (by linarith) hn.le)

end CommonScale

#print axioms CommonScale.coefficient_change
