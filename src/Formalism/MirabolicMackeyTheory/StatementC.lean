import Mathlib
import Formalism.MirabolicMackeyTheory.StatementT

open Module NumberField IsDedekindDomain

noncomputable section

namespace Formalism.EigenvalueLevelCeiling

open Formalism.DivisionValues

def AbsorbOnC : Prop :=
  ∀ (c C Cb L xe f m b k ws Se Y X2 bad : ℝ), 0 ≤ c → 1 ≤ C → 0 ≤ Cb → 1 ≤ L → L ≤ xe → 1 ≤ f → 1 ≤ m →
    0 < b → 1 ≤ k → Real.log k ≤ L → 0 ≤ ws → ws ≤ 2 * f * b → 0 ≤ Se → k * Se * L ≤ m * b → 1 < Y →
    Real.log Y ≤ 2 * L → Y ≤ m * b → k ≤ X2 → bad ≤ Cb * (f * m * b * L) →
      2 * (C * (Real.log k * m * ws + f * k * Se) * Real.log Y + C * k * ws * (C / k) + C * (m * b) +
          2 * c * (C * k * ws) / X2 + c * Y) + bad + 12 * (f * m * b) ≤
        (4 * C ^ 2 + (14 + 10 * c) * C + Cb + 12) * xe * (f * m * b * L)

def ThetaLog4 : Prop :=
  ∀ (Y : ℝ), 0 ≤ Y → ∀ Q : Finset ℕ, (∀ p ∈ Q, p.Prime ∧ (p : ℝ) ≤ Y) →
    ∑ p ∈ Q, Real.log (p : ℝ) ≤ Real.log 4 * Y

def DepthSums (T Cth Cadd : ℝ) (th add : ℕ → ℝ) : Prop :=
  (∀ Q : Finset ℕ, (∀ p ∈ Q, p.Prime) → ∑ p ∈ Q, th p * Real.log (p : ℝ) ≤ Cth) ∧
    (∀ Q : Finset ℕ, (∀ p ∈ Q, p.Prime) → T * ∑ p ∈ Q, add p * Real.log (p : ℝ) ≤ Cadd)

end Formalism.EigenvalueLevelCeiling
