import Mathlib
import Formalism.MirabolicMackeyTheory.StatementT
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic

namespace Formalism.EigenvalueLevelCeiling

theorem depth_cases : DepthCases := by
  unfold DepthCases
  intro e ec F
  refine ⟨fun a h1 h2 => by linarith, fun h1 h2 h3 => by linarith,
    fun s T β h1 h2 h3 h4 => by linarith, fun s T h1 h2 h3 => by linarith,
    fun T nn nnc g2 h1 h2 h3 => by linarith⟩


theorem budget_numeric : BudgetNum := by
  unfold BudgetNum
  intro dK δq D B hδ hD hB hq
  rw [div_le_iff₀ (mul_pos hδ hD)]
  have h1 : dK ≤ 3 * D * δq := (div_le_iff₀ hδ).mp hq
  have h2 : dK * B ≤ 3 * D * δq * B := mul_le_mul_of_nonneg_right h1 hB
  linarith

theorem share_numeric : ShareNum := by
  unfold ShareNum
  intro dK d0 d U δq ep y del hU hδ hdK hd0 hep hey hy hdel hdel' h1 h2 h3
  rw [div_le_iff₀ hδ]
  have k1 : 7 / 8 * dK ≤ U * d0 := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 / 8 - ep) hdK]
  have k2 : 7 / 8 * U ≤ δq := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 / 8 - y) hU.le]
  have k3 : 3 / 4 * d0 ≤ d := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 / 4 - del) hd0]
  have hd : 0 ≤ d := by linarith
  have k4 : d * (7 / 8 * U) ≤ d * δq := mul_le_mul_of_nonneg_left k2 hd
  have k5 : 3 / 4 * d0 * U ≤ d * U := mul_le_mul_of_nonneg_right k3 hU.le
  nlinarith

end Formalism.EigenvalueLevelCeiling
