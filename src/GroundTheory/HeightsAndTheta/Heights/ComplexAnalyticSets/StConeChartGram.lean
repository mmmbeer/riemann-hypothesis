import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StConePolar
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChartGram
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets

noncomputable section

def ConeChartGram.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ)) (ℓ : Fin n → ℂ)
    (g : (Fin n → ℂ) → ℝ) (A : Matrix (Fin e) (Fin n) ℂ),
    IsProjPrime J → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = ((e + 1 : ℕ) : WithBot ℕ∞) →
    linForm ℓ ∉ J → (∀ (t : ℂ) (x : Fin n → ℂ), t ≠ 0 → g (t • x) = g x) →
    ContinuousOn g {x | x ≠ 0} → IsFiniteProjection (J ⊔ Ideal.span {linForm ℓ - 1}) A →
      coneIntegral h J e g =
        ∫ y, sheetSum (J ⊔ Ideal.span {linForm ℓ - 1}) A
          (fun x s => g x * ((e.factorial : ℝ) / Real.pi ^ e *
            gramVol (fun y' => (h.matᵀ)⁻¹ *ᵥ s y') y / h.dualNorm x ^ (2 * (e + 1)))) y

end

end GroundTheory.Heights₂.Heights
