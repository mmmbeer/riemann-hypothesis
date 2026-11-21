import Mathlib

namespace Formalism.NuclearRankWeightBounds.Z

open Finset

def LatSum : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (f : ℕ) (La : AddSubgroup (Fin f → ℂ)) (x : Fin f → ℝ) (K : ℕ) (S : Finset (Fin f → ℂ)),
      (∀ o ∈ La, o ≠ 0 → 1 ≤ ∏ v, ‖o v‖) → (∀ v, 0 < x v) → ∏ v, x v < 1 → 3 ≤ K →
      (∀ o ∈ S, o ∈ La ∧ o ≠ 0) →
      ∑ o ∈ S, ∏ v, min 1 ((x v / ‖o v‖) ^ K)
        ≤ C ^ f * (∏ v, x v) ^ ((K : ℝ) - 5 / 2)

end Formalism.NuclearRankWeightBounds.Z
