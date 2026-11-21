import Mathlib
import Formalism.RankGapBounds.CloudMinFalse

noncomputable section

open Finset

namespace Formalism.CohomologicalDescent

def lamOf (N : ℕ) (U : ℕ → ℤ) (i : ℕ) : ℤ := U i - ((N : ℤ) - 1 - (i : ℤ))

def ParamsWindow : Prop :=
  ∀ (b h l t : ℕ) (lstar h0 η : ℝ), 1 ≤ lstar → (h : ℝ) ≤ 2 * b → lstar < (l : ℝ) →
    12 * b / lstar + 2 * t + 8 ≤ h0 → 2 * η + t + 8 * b / lstar + 7 < lstar → 0 ≤ η →
    ((h / (l - 1) : ℕ) : ℝ) ≤ h0 / 4 - t / 2 - 2 ∧ η + t + ((h / (l - 1) : ℕ) : ℝ) < l ∧
      0 < h0 / 2 - 1 - t / 2 - ((h / (l - 1) : ℕ) : ℝ)

end Formalism.CohomologicalDescent
