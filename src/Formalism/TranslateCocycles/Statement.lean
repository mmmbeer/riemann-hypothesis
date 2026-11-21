import Mathlib

noncomputable section

namespace Formalism.CG

open Finset

def BalanceG : Prop :=
  ∀ (J T P : Finset ℕ) (D del : ℝ), 0 < D → 0 < del →
    ∀ (colL colLb : ℝ) (aL aLb Dpi Dp Dm eta etab top : ℕ → ℝ) (k : ℝ) (w e1 e2 : ℕ → ℕ → ℝ)
      (Ecol CA rL rLb Etw : ℝ),
    -(∑ j ∈ J, Dpi j) - Ecol ≤ colL + colLb →
    ∑ j ∈ J, (aL j + aLb j) ≤ ∑ j ∈ J, (-2 * (Dp j + Dm j) * D + eta j + etab j)
        + 2 * (J.card : ℝ) * (CA * D + (rL + rLb) / del) + Etw →
    (∀ j ∈ J, Dpi j ≤ ∑ t ∈ T, top t + ∑ τ ∈ P, (k * w j τ + e1 j τ)) →
    (∀ j ∈ J, ∑ τ ∈ P, ((k - 1) * w j τ - e2 j τ) ≤ Dp j + Dm j) →
      -((J.card : ℝ) * ∑ t ∈ T, top t + ∑ j ∈ J, ∑ τ ∈ P, (w j τ + e1 j τ + e2 j τ)
          + ∑ j ∈ J, (eta j + etab j) / (2 * D))
        - Ecol - (J.card : ℝ) * (CA + (rL + rLb) / (del * D)) - Etw / (2 * D)
      ≤ (2 * colL + 2 * colLb) / 2 - (∑ j ∈ J, (aL j + aLb j) / D) / 2

end Formalism.CG
