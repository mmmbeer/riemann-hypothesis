import Mathlib

noncomputable section

namespace Formalism.LogFactorialBounds

open Finset

def DepthRadii : Prop :=
  ∀ (p : ℝ) (n : ℕ), 2 ≤ p → 1 ≤ n →
    2 / (p - 1) ≤ p ^ n * (2 / (p * (p - 1))) - ((n : ℝ) - 1) ∧
    2 / (p - 1) ≤ p ^ n * (2 / (p - 1)) - n

def DepthIIExponent : Prop :=
  ∀ p r : ℕ, 2 ≤ p →
    (p ^ 2 - 1) ∣ (p ^ (2 * r) - 1) ∧
    (p : ℝ) ^ (2 * r + 1) / ((p : ℝ) ^ 2 - 1)
        - p * (((p ^ (2 * r) - 1) / (p ^ 2 - 1) : ℕ) : ℝ) = p / ((p : ℝ) ^ 2 - 1)

def LegendreBounds : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (k c : ℕ) (α : Fin k → ℕ), (∀ j, α j ≤ c) →
    ((p : ℝ) - 1) * (∑ j, (padicValNat p (α j).factorial : ℝ)) ≤ ∑ j, (α j : ℝ) ∧
    (∑ j, (α j : ℝ)) / ((p : ℝ) - 1) - k * ((Nat.log p c : ℝ) + 1)
      ≤ ∑ j, (padicValNat p (α j).factorial : ℝ)

end Formalism.LogFactorialBounds
