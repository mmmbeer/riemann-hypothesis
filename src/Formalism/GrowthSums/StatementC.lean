import Mathlib
import Formalism.GrowthSums.StatementA

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.GrowthSums

def LogCoefVal : Prop :=
  ∀ p t s : ℕ, p.Prime → 5 ≤ p → 1 ≤ s →
    ((s : ℝ) + 1) / 4 ≤
      (padicValRat p (((p ^ (t + 1) : ℕ) : ℚ) ^ s * (∑ y ∈ Ico 1 (p ^ (t + 1)), 1 / (y : ℚ) ^ s) / s) : ℝ)
        - 1 / ((p : ℝ) - 1)

end Formalism.GrowthSums
