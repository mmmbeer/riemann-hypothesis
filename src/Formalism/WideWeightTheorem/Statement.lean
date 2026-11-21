import Formalism.JacobiWeightFamilies.Statement

open Finset ArithmeticFunction

noncomputable section

namespace Formalism.WeightedSieveThreeParameter

open Formalism Formalism.CMTypeGaloisData Formalism.WT

def gavg {n : ℕ} (w y : Fin n → ℝ) (f : ℝ → ℝ) : ℝ := ∑ j, w j * f (y j)

end Formalism.WeightedSieveThreeParameter
