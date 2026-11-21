import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Integrated rank loss for finite lists of Harder–Narasimhan slopes.
The frame estimate in `mean_slope_loss` is equation (2.2) of
https://hexagonmath.org/2611.00828v1. -/

open Finset MeasureTheory

namespace Formalism.HN

theorem clipped_deficit_bound {ι : Type*} [Fintype ι] (a : ι → ℝ) (s U H : ℝ)
    (hU : 0 ≤ U) (hH : 0 ≤ H) (hcap : ∀ i, a i ≤ s + U)
    (hmean : Fintype.card ι * s ≤ ∑ i, a i) :
    ∑ i, min H (max 0 (s - a i)) ≤ Fintype.card ι * (H * U / (H + U)) := by
  by_cases hden : H + U = 0
  · have : H = 0 := by linarith
    simp [this]
  have hpos : 0 < H + U := lt_of_le_of_ne (add_nonneg hH hU) (Ne.symm hden)
  have point (i : ι) : min H (max 0 (s - a i)) * (H + U) ≤ H * (s - a i + U) := by
    rcases le_total (s - a i) 0 with h | h
    · rw [max_eq_left h, min_eq_right hH, zero_mul]
      exact mul_nonneg hH (by linarith [hcap i])
    · rw [max_eq_right h]
      rcases le_total (s - a i) H with t | t
      · rw [min_eq_right t]
        nlinarith [mul_nonneg hU (sub_nonneg.mpr t)]
      · rw [min_eq_left t]
        nlinarith [mul_nonneg hH (sub_nonneg.mpr t)]
  have hsum := sum_le_sum fun i (_ : i ∈ (univ : Finset ι)) => point i
  rw [← sum_mul, ← mul_sum, sum_add_distrib, sum_sub_distrib] at hsum
  simp only [sum_const, card_univ, nsmul_eq_mul] at hsum
  rw [← mul_div_assoc, le_div_iff₀ hpos]
  nlinarith [mul_le_mul_of_nonneg_left hmean hH]
/-- The integral of each threshold count is the clipped deficit of the slope. -/
theorem integral_rank_count_eq {ι : Type*} [Fintype ι] (a : ι → ℝ) (s H : ℝ) (hH : 0 ≤ H) :
    (∫ t in (0 : ℝ)..H, ∑ i, (if t < s - a i then (1 : ℝ) else 0)) =
      ∑ i, min H (max 0 (s - a i)) := by
  let step (z t : ℝ) := if t < z then (1 : ℝ) else 0
  have anti (z : ℝ) : Antitone (step z) := by
    intro b c hbc
    by_cases hc : c < z
    · simp [step, hc, hbc.trans_lt hc]
    · simp [step, hc]; split <;> norm_num
  rw [intervalIntegral.integral_finsetSum (fun i _ => (anti (s - a i)).intervalIntegrable)]
  refine sum_congr rfl fun i _ => ?_
  let c := min H (max 0 (s - a i))
  have hc : c ∈ Set.Icc 0 H := ⟨le_min hH (le_max_left _ _), min_le_left _ _⟩
  calc
    _ = ∫ t in (0 : ℝ)..H, Set.indicator {y : ℝ | y ≤ c} (fun _ => (1 : ℝ)) t := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [volume.ae_ne c] with t hne ht
      rw [Set.uIoc_of_le hH] at ht
      have hi : t < s - a i ↔ t ≤ c := by
        dsimp [c] at *
        rw [le_min_iff, le_max_iff]
        constructor
        · intro h; exact ⟨ht.2, Or.inr h.le⟩
        · rintro ⟨hh, hl | hr⟩
          · exact (not_le_of_gt ht.1 hl).elim
          · apply lt_of_le_of_ne hr
            rintro rfl
            exact hne (by rw [max_eq_right ht.1.le, min_eq_right ht.2])
      simp only [step, Set.indicator, Set.mem_ofPred_eq, hi]
    _ = _ := by rw [intervalIntegral.integral_indicator hc]; simp [c]

theorem integrated_rank_loss {ι : Type*} [Fintype ι] (a : ι → ℝ) (s U H : ℝ)
    (hU : 0 ≤ U) (hH : 0 ≤ H) (hcap : ∀ i, a i ≤ s + U)
    (hmean : Fintype.card ι * s ≤ ∑ i, a i) :
    (∫ t in (0 : ℝ)..H, ∑ i, (if t < s - a i then (1 : ℝ) else 0)) ≤
      Fintype.card ι * (H * U / (H + U)) := by
  rw [integral_rank_count_eq a s H hH]
  exact clipped_deficit_bound a s U H hU hH hcap hmean

private noncomputable def slopeCount {ν : Type*} [Fintype ν] (v : ν → ℝ) (s t : ℝ) :=
  ∑ i, if t < s - v i then (1 : ℝ) else 0

private theorem slopeCount_integrable {ν : Type*} [Fintype ν] (v : ν → ℝ) (s H : ℝ) : IntervalIntegrable (slopeCount v s) volume 0 H := by
  apply Antitone.intervalIntegrable
  intro x y hxy
  apply sum_le_sum
  intro i _
  by_cases h : y < s - v i
  · simp [h, hxy.trans_lt h]
  · by_cases hx : x < s - v i <;> simp [h, hx]

/-- Integrating the actual discarded input ranks yields Proposition 2.1 for finite slope lists. -/
theorem mean_slope_loss {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty ι] [Nonempty κ]
    (a : ι → ℝ) (target : κ → ℝ) (s U H d A : ℝ) (hU : 0 ≤ U) (hH : 0 ≤ H)
    (hd : d < 1) (hcap : ∀ i, a i ≤ s + U) (hmean : Fintype.card ι * s ≤ ∑ i, a i)
    (hlower : ∀ j, s - H ≤ target j)
    (hframe : ∀ t ∈ Set.Icc 0 H,
      (1 - d) * ((∑ j, if t < s - target j then (1 : ℝ) else 0) / Fintype.card κ) ≤
        A + 4 * ((∑ i, if t < s - a i then (1 : ℝ) else 0) / Fintype.card ι)) :
    s - (∑ j, target j) / Fintype.card κ ≤ (A * H + 4 * (H * U / (H + U))) / (1 - d) := by
  have ni : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have nk : (0 : ℝ) < Fintype.card κ := by exact_mod_cast Fintype.card_pos
  have ht : Fintype.card κ * s - ∑ j, target j ≤ ∫ t in (0 : ℝ)..H, slopeCount target s t := by
    rw [show (∫ t in (0 : ℝ)..H, slopeCount target s t) = _ from integral_rank_count_eq target s H hH,
      ← nsmul_eq_mul, ← card_univ, ← sum_const, ← sum_sub_distrib]
    exact sum_le_sum fun j _ => le_min (by linarith [hlower j]) (le_max_right _ _)
  have hint := intervalIntegral.integral_mono_on hH (((slopeCount_integrable target s H).div_const _).const_mul (1 - d))
    (intervalIntegrable_const.add (((slopeCount_integrable a s H).div_const _).const_mul 4)) hframe
  simp only [intervalIntegral.integral_add intervalIntegrable_const (((slopeCount_integrable a s H).div_const _).const_mul 4),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_div, intervalIntegral.integral_const,
    sub_zero, smul_eq_mul] at hint
  have hinput : (∫ t in (0 : ℝ)..H, slopeCount a s t) / Fintype.card ι ≤ H * U / (H + U) := by
    rw [div_le_iff₀ ni, mul_comm]; exact integrated_rank_loss a s U H hU hH hcap hmean
  have hout : s - (∑ j, target j) / Fintype.card κ ≤ (∫ t in (0 : ℝ)..H, slopeCount target s t) / Fintype.card κ := by
    rw [le_div_iff₀ nk, sub_mul, div_mul_cancel₀ _ nk.ne', mul_comm]; exact ht
  rw [le_div_iff₀ (sub_pos.mpr hd), mul_comm]
  exact (mul_le_mul_of_nonneg_left hout (sub_nonneg.mpr hd.le)).trans
    (hint.trans (by linarith [hinput, mul_comm A H]))

/-- The rational loss implies the logarithmic allowance in `TheoremFSharp`. -/
theorem integrated_loss_le_log (U H : ℝ) (hU : 0 ≤ U) (hH : 0 ≤ H) :
    H * U / (H + U) ≤ U * Real.log (1 + H / U) := by
  rcases hU.eq_or_lt with hzero | hpos
  · simp [← hzero]
  have hsum : 0 < H + U := add_pos_of_nonneg_of_pos hH hpos
  have hx : 0 < 1 + H / U := by positivity
  calc
    _ = U * (1 - (1 + H / U)⁻¹) := by
      rw [one_add_div hpos.ne', inv_div]; field_simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos hx) hU

end Formalism.HN
