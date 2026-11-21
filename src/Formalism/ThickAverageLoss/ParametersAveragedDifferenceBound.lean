import Formalism.ThickAverageLoss.Statement

open Finset ArithmeticFunction

noncomputable section

namespace Formalism.D5

open Formalism Formalism.CMTypeGaloisData Formalism.WT Formalism.WeightedSieveThreeParameter

def ParametersAveragedDifferenceBound : Prop :=
  DLVP → ∀ ε C K : ℝ, 0 < ε → ε ≤ 1 / 20 → 0 ≤ C → ∃ K' x₀ : ℝ, 0 ≤ K' ∧ ∀ x : ℝ, x₀ ≤ x →
    ∀ P : SizeParameters, SizeConditions ε K x P →
    ∀ (nn : ℕ) (w y : Fin nn → ℝ) (d : ℕ) (χ : DirichletCharacter ℂ d) (large₂ : ExplicitFormulaData C ε x P w y d χ),
      -(C * x ^ ((1 : ℝ) / 2 + ε)) ≤ gavg w y (Gch large₂.ps large₂.ellPs) →
      gavg w y Gz - gavg w y (GJ d χ) - gavg w y (Gch large₂.chps large₂.ellChPs) ≤ K' * x ^ ((1 : ℝ) / 2 + 4 * ε)

end Formalism.D5
