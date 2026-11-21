import ReciprocityTheory.L2DbarEstimates.JacobianInterpolationStatement
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.TsupportDbSubset

namespace ReciprocityTheory.L2DbarEstimates

open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal

noncomputable section

theorem inh_wd_coord (n : ℕ) (j k : Fin n) (y : V n) :
    wd n j (fun y : V n => y k) y = if j = k then 1 else 0 := by
  have h : (fun y : V n => y k) = ⇑((EuclideanSpace.proj k : V n →L[ℂ] ℂ).restrictScalars ℝ) := by
    funext y; simp
  unfold wd
  rw [h, ContinuousLinearMap.fderiv]
  simp only [ContinuousLinearMap.coe_restrictScalars', bas]
  by_cases hjk : j = k
  · subst hjk; simp
  · simp [hjk, Ne.symm hjk]

theorem inh_isChart_refl (n : ℕ) : IsChart n id (OpenPartialHomeomorph.refl (V n)) :=
  fun _ _ => rfl

end

end ReciprocityTheory.L2DbarEstimates
