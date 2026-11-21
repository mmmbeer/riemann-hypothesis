import Mathlib
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open InnerProductSpace Laplacian

def LaplacianDecayZero.Statement : Prop :=
  ∀ (v : ℂ → ℝ) (C R₀ : ℝ), ContDiff ℝ 2 v →
    (∀ y : ℂ, R₀ < ‖y‖ →
      ‖fderiv ℝ v y‖ ≤ C / ‖y‖ ^ 2 ∧ ‖iteratedFDeriv ℝ 2 v y‖ ≤ C / ‖y‖ ^ 3) →
    MeasureTheory.Integrable (Δ v) ∧ ∫ y, Δ v y = 0

end GroundTheory.Heights₂.Heights.LowerBoundFree
