import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.CBFiLower

noncomputable section

open Finset

namespace PI.ExpMinorLowWork

open Formalism.MainNotions.Ext.CutB

def RealStep : Prop :=
  ∀ (ι : Type) [Fintype ι] (w y : ι → ℝ) (V ρ : ℝ), (∀ s, 0 ≤ w s) → ∑ s, w s = 1 →
    ∑ s, w s * y s = 0 → ∑ s, w s * y s ^ 2 = V → (∀ s, |y s| ≤ ρ / 2) → ρ ≤ 1 →
    (1 - ρ) / 2 * V ≤ Real.log (∑ s, w s * Real.exp (y s))

def Rep : Prop :=
  ∀ (N : ℕ) (X : Matrix (Fin N) (Fin N) ℂ) (hX : X.IsHermitian), (∀ a, X a a = 0) →
    ∀ (i : ℕ) (hi : i ≤ N), ∃ w : Finset (Fin N) → ℝ, (∀ S, 0 ≤ w S) ∧ ∑ S, w S = 1 ∧
      ∑ S, w S * (∑ m ∈ S, hX.eigenvalues m) = 0 ∧
      ∑ S, w S * (∑ m ∈ S, hX.eigenvalues m) ^ 2 = cBV X i ∧
      (cBlead (NormedSpace.exp X) i hi).det =
        ((∑ S, w S * Real.exp (∑ m ∈ S, hX.eigenvalues m) : ℝ) : ℂ)

end PI.ExpMinorLowWork
