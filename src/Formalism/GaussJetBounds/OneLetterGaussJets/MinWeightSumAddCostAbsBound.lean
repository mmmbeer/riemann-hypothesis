import Formalism.GaussJetBounds.StatementQ

noncomputable section
open scoped BigOperators

universe u

namespace Formalism.DworkPowerSeriesWeights.OddLevelGainBounds

open Formalism.DworkPowerSeriesWeights

def MinWeightSumAddCostAbsBound : Prop :=
  ∀ (H : Type) [Fintype H] [DecidableEq H] (TT : Finset H) (c wt wt' : H → ℝ) (f k b b' : ℝ),
    (Fintype.card H : ℝ) = f / 2 → 1 ≤ k → 0 ≤ b → 0 ≤ b' → (∀ t, 0 ≤ c t) →
    (∀ t, t ∉ TT → c t ≤ 4 * k * b') → (∀ t, t ∈ TT → c t ≤ 4 * k * b' + 2 * b) →
    (∀ t, 0 ≤ wt t ∧ wt t ≤ 2 * b') → (∀ t, 0 ≤ wt' t) →
    |(-((k - 1) / 2) * ∑ t, min (wt t) (wt' t)) + (1 / 2) * ∑ t, c t| ≤
      (TT.card : ℝ) * b + f * k * b'

end Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
