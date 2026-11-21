import Mathlib

namespace Formalism.SL.CS

open Finset

def KernelBoundRel : Prop :=
  ∀ (ι : Type) [Fintype ι] (P : ι → ι → ℝ) (w : ι → ℂ) (ε₁ ε₂ : ℝ),
    (∀ i j, P i j = P j i) →
    (∀ i, |(∑ j, P i j) - 1| ≤ ε₁) →
    (∀ i, ‖∑ j, (P i j : ℂ) * w j‖ ≤ ε₂ * ‖w i‖) →
    ‖∑ i, w i‖ ≤ (ε₁ + ε₂) * ∑ i, ‖w i‖

end Formalism.SL.CS
