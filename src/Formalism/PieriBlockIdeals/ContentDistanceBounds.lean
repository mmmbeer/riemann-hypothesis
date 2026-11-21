import Mathlib
import Formalism.PieriBlockIdeals.Statement

noncomputable section

open Finset

namespace Formalism.CohomologicalDescent

open Classical

def ContentDistanceBounds : Prop :=
  ∀ (r w H : ℕ) (lam tau : ℕ → ℕ), Antitone lam → Antitone tau → (∀ a, lam a ≤ tau a) →
    lam 0 ≤ w → w ≤ H → 0 < r → (∀ a < r, ¬ (lam a ≤ a + w ∧ a + w < tau a)) →
    ∀ a < r, ∀ col : ℕ, lam a ≤ col → col < tau a →
      1 ≤ (w : ℤ) - ((col : ℤ) - (a : ℤ)) ∧ (w : ℤ) - ((col : ℤ) - (a : ℤ)) ≤ (H : ℤ) + r - 1

def NoResidue : Prop :=
  ∀ (l : ℕ) (b : ℤ) (t κ : ℕ) (U : Finset ℤ),
    (∀ u ∈ U, u ∉ Finset.Icc b (b + t - 1) → ∀ x ∈ Finset.Icc (b - κ) (b + t - 1 + κ),
      (0 < |u - x| ∧ |u - x| < (l : ℤ)) ∨ ¬ ((l : ℤ) ∣ u - x)) →
    mwCount l b t κ U = 0

def PrimeCount : Prop :=
  ∀ (L : ℝ) (T : Finset ℤ) (P : Finset ℕ), 0 ≤ L → (∀ n ∈ T, n ≠ 0 ∧ ((|n| : ℤ) : ℝ) < L ^ 2) →
    (∀ l ∈ P, l.Prime ∧ L < (l : ℝ) ∧ ∃ n ∈ T, (l : ℤ) ∣ n) → P.card ≤ T.card

def ISum : Prop :=
  ∀ (h : ℕ) (L : ℝ) (xm xp mB : ℤ) (P : Finset ℕ), 0 ≤ L → (h : ℝ) < L ^ 2 → 0 ≤ mB → mB < xm →
    xm ≤ xp → xp ≤ (h : ℤ) → (∀ l ∈ P, l.Prime ∧ L < (l : ℝ)) →
    ∑ l ∈ P, IlInd l xm xp mB * Real.log (l : ℝ) ≤ (((xp - xm : ℤ) : ℝ) + 1) * Real.log (h : ℝ)

end Formalism.CohomologicalDescent
