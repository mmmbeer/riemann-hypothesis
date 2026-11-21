import Mathlib
import Formalism.PeriodIntegrals.LeafCoeffVal

noncomputable section

namespace PI.LCV

open PowerSeries Finset

def W (p d : ℕ) (j : ℤ) (f : PowerSeries ℚ) : Prop :=
  ∀ m : ℕ, padicNorm p (coeff m f) ^ d ≤ (p : ℚ) ^ ((m : ℤ) - j)

end PI.LCV

end
