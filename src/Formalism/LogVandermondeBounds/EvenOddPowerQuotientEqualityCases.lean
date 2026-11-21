import Mathlib

namespace Formalism.LogVandermondeBounds.TaylorLogMetric

open Finset

def EvenOddPowerQuotientEqualityCases : Prop :=
  ∀ (p : ℕ), 2 ≤ p →
    ((((p : ℚ) ^ 2) ^ 0 + (p : ℚ) * ((p : ℚ) ^ 2) ^ 1) / ((p : ℚ) ^ 2 - 1) - (0 + 1 + 1) =
      ((p : ℚ) - 2) + 1 / ((p : ℚ) - 1)) ∧
    ((((p : ℚ) ^ 2) ^ 1 + (p : ℚ) * ((p : ℚ) ^ 2) ^ 1) / ((p : ℚ) ^ 2 - 1) - (1 + 1 + 1) =
      ((p : ℚ) - 2) + 1 / ((p : ℚ) - 1))

open Classical in

noncomputable def coefL (p a : ℕ) : ℚ :=
  if h : ∃ j, a = (p ^ 2) ^ j then 1 / (p : ℚ) ^ (Classical.choose h) else 0

open Classical in
noncomputable def coefG (p a : ℕ) : ℚ :=
  if h : ∃ j, a = p * (p ^ 2) ^ j then 1 / (p : ℚ) ^ (Classical.choose h + 1) else 0

open Classical in

noncomputable def coefA (p a b : ℕ) : ℚ :=
  if h : ∃ i j, i ≤ j ∧ a = (p ^ 2) ^ i ∧ b = p * (p ^ 2) ^ j then
    1 / (p : ℚ) ^ (Classical.choose h + Classical.choose (Classical.choose_spec h) + 1) else 0

noncomputable def coefB (p a b : ℕ) : ℚ := coefA p b a

def LogarithmSeriesIdentities : Prop :=
  ∀ (p : ℕ), p.Prime →
    (∀ a : ℕ, (if p ∣ a then coefG p (a / p) else 0) = coefL p a - (if a = 1 then 1 else 0)) ∧
    (∀ a b : ℕ, (if p ∣ a ∧ p ∣ b then coefA p (a / p) (b / p) else 0) =
      (p : ℚ) * (coefG p a * coefL p b - coefB p a b))

end Formalism.LogVandermondeBounds.TaylorLogMetric
