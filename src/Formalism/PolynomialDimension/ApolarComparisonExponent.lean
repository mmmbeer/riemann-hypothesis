import Mathlib
import Formalism.PolynomialDimension.WeylDim

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.CountingSumsFrames

def logScale (C₀ : ℝ) (N₁ : ℕ) (a : ℝ) : ℝ := C₀ * (N₁ : ℝ) ^ 2 * Real.log a

def logBaseP (p : ℕ) (a : ℝ) (k : ℕ) : ℝ := Real.logb p (8 * a + k) + 1

def PolynomialDimensionIntervalConditions (C C₀ : ℝ) (p N N₁ J k n' G' : ℕ) (Y Yb a b' Ib cl D cStar : ℝ) : Prop :=
  2 ≤ p ∧ 1 ≤ Y ∧ (k : ℝ) ^ 2 * Y ^ 2 ≤ p ∧ 1 ≤ N ∧ 1 ≤ N₁ ∧ 2 * N₁ + 2 ≤ k - 1 ∧ 1 ≤ J ∧ J ≤ N ∧
  1 ≤ G' ∧ 2 ≤ n' ∧
  8 * Real.log (N * Y) ≤ logScale C₀ N₁ a ∧
  Yb * N * logScale C₀ N₁ a * b' / k ≤ Ib ∧ Ib ≤ b' / 2 ∧ C ≤ Yb ∧ 2 * Yb * N * logScale C₀ N₁ a < k ∧
  (k : ℝ) * Y ^ 2 * Yb * N * logScale C₀ N₁ a * Real.log a ≤ a / b' ∧ 0 < b' ∧ (p : ℝ) < a / b' ∧
  C * N * logScale C₀ N₁ a ^ 2 ≤ k ∧ 0 ≤ cl ∧ cl ≤ logScale C₀ N₁ a * b' / k ∧
  C * N * Y ^ 2 * ((N₁ : ℝ) ^ 5 + (k : ℝ) ^ 3) * Real.logb p a ≤ D ∧ 8 * (D + 1) ≤ cStar ∧
  C * (k : ℝ) ^ 3 * N * ((p : ℝ) ^ G') ^ 4 * (cStar + N * cl + n' * cl) * Y ≤ b'

def KapI : Prop :=
  ∀ CW C1 : ℝ, 0 ≤ CW → 0 ≤ C1 → ∃ C : ℝ, 1 ≤ C ∧ ∀ C₀ : ℝ, 1 ≤ C₀ →
    ∀ (p N N₁ J k n' G' : ℕ) (Y Yb a b' Ib cl D cStar : ℝ),
      PolynomialDimensionIntervalConditions C C₀ p N N₁ J k n' G' Y Yb a b' Ib cl D cStar →
      ∀ mH mHp : ℝ, mH ≤ C1 * N * N₁ / Y → mHp ≤ C1 * N * N₁ / Y →
        mH + 2 * mHp + CW * N * k * (2 * cl) / b' + N * cl * (1 / (a / (k * Y)) + 1 / Ib) ≤ C * N * N₁ / Y

end Formalism.CountingSumsFrames
