import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Complex MeasureTheory Set

namespace OscillationCorrection

/-- In log coordinates t = log x, the nonnegative correction for a real pole
has a Laplace transform with poles at β and β ± iu. -/
theorem transform {β u : ℝ} {s : ℂ} (hs : β < s.re) :
    (∫ t : ℝ in Ioi 0, Complex.exp (((β : ℂ) - s) * t) *
        (1 - ((Real.cos (u * t) : ℝ) : ℂ))) =
      1 / (s - β) - (1 / (s - β - u * I) + 1 / (s - β + u * I)) / 2 := by
  let a : ℂ := β - s
  let b : ℂ := u * I
  have ha : a.re < 0 := by simpa [a] using sub_neg.mpr hs
  have hab : (a + b).re < 0 := by simpa [b] using ha
  have hsub : (a - b).re < 0 := by simpa [b] using ha
  let E (q : ℂ) (t : ℝ) := Complex.exp (q * t)
  have hE (q : ℂ) (hq : q.re < 0) : IntegrableOn (E q) (Ioi 0) :=
    integrableOn_exp_mul_complex_Ioi hq 0
  have integralE (q : ℂ) (hq : q.re < 0) : ∫ t : ℝ in Ioi 0, E q t = -1 / q := by
    simpa [E] using integral_exp_mul_complex_Ioi hq 0
  have he (t : ℝ) : E a t * (1 - ((Real.cos (u * t) : ℝ) : ℂ)) =
      E a t - (E (a + b) t + E (a - b) t) / 2 := by
    rw [Complex.ofReal_cos, Complex.ofReal_mul]
    have hc := Complex.two_cos ((u : ℂ) * t)
    have hplus : E (a + b) t = E a t * Complex.exp ((u * t) * I) := by
      unfold E
      rw [← Complex.exp_add]
      congr 1
      dsimp [b]
      ring
    have hminus : E (a - b) t = E a t * Complex.exp (-(u * t) * I) := by
      unfold E
      rw [← Complex.exp_add]
      congr 1
      dsimp [b]
      ring
    rw [hplus, hminus]
    linear_combination -(E a t / 2) * hc
  change (∫ t : ℝ in Ioi 0, E a t * _) = _
  simp_rw [he]
  have hsum : IntegrableOn (fun t => E (a + b) t + E (a - b) t) (Ioi 0) :=
    (hE _ hab).add (hE _ hsub)
  rw [integral_sub (hE a ha) (hsum.div_const 2),
    integral_div, integral_add (hE _ hab) (hE _ hsub),
    integralE _ ha, integralE _ hab, integralE _ hsub]
  dsimp [a, b]
  rw [show (β : ℂ) - s = -(s - β) by ring,
    show -(s - β) + u * I = -(s - β - u * I) by ring,
    show -(s - β) - u * I = -(s - β + u * I) by ring]
  simp only [neg_div_neg_eq]

/-- Positive residues allow all real-pole corrections to be subtracted
simultaneously while preserving strict negativity on a good interval. -/
theorem corrected_neg {ι : Type*} (P : Finset ι) (r β : ι → ℝ)
    (hr : ∀ i ∈ P, 0 ≤ r i) {x θ K y u : ℝ} (hx : 0 < x) (hy : y ≤ K * x ^ θ) :
    y - (|K| + 1) * x ^ θ -
      ∑ i ∈ P, r i * x ^ β i * (1 - Real.cos (u * Real.log x)) < 0 := by
  have hs : 0 ≤ ∑ i ∈ P, r i * x ^ β i * (1 - Real.cos (u * Real.log x)) :=
    Finset.sum_nonneg fun i hi => mul_nonneg (mul_nonneg (hr i hi) (Real.rpow_nonneg hx.le _))
      (sub_nonneg.mpr (Real.cos_le_one _))
  have hk := mul_le_mul_of_nonneg_right (le_abs_self K) (Real.rpow_nonneg hx.le θ)
  nlinarith [Real.rpow_pos_of_pos hx θ]

/-- The positive excursions supplied by a quantitative sign-change theorem
cannot coexist with arbitrarily large nonpositive power windows. -/
theorem incompatible_power_windows (f : ℝ → ℝ) {power α : ℝ} (hpower : 1 ≤ power)
    (hfit : 1 ≤ power * (1 - α))
    (good : ∀ B : ℝ, ∃ Y ≥ B, ∀ x ∈ Icc Y (Y ^ power), f x ≤ 0)
    (excursion : ∃ B : ℝ, ∀ T ≥ B, ∃ x ∈ Icc (T ^ (1 - α)) T, 0 < f x) : False := by
  obtain ⟨B, hB⟩ := excursion
  obtain ⟨Y, hY, hgood⟩ := good (max 1 B)
  have h1 : 1 ≤ Y := (le_max_left _ _).trans hY
  have hpow {q : ℝ} (hq : 1 ≤ q) : Y ≤ Y ^ q := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le h1 hq
  obtain ⟨x, hx, hpos⟩ := hB (Y ^ power) ((le_max_right _ _).trans (hY.trans (hpow hpower)))
  have hleft : Y ≤ (Y ^ power) ^ (1 - α) := by
    rw [← Real.rpow_mul (zero_le_one.trans h1)]
    exact hpow hfit
  exact (hgood x ⟨hleft.trans hx.1, hx.2⟩).not_gt hpos

end OscillationCorrection

#print axioms OscillationCorrection.transform
#print axioms OscillationCorrection.corrected_neg
#print axioms OscillationCorrection.incompatible_power_windows
