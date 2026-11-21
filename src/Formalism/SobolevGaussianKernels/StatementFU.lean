import Mathlib
import Formalism.CorankShare.StatementFR

noncomputable section

namespace Formalism.SL.FU

open Finset Module LinearMap Formalism.CorankShareLayerCake.FR

def FrameGram : Prop :=
  ∀ (ι : Type) [Fintype ι] (V : ι → Type) [∀ i, NormedAddCommGroup (V i)]
    [∀ i, InnerProductSpace ℂ (V i)] [∀ i, FiniteDimensional ℂ (V i)]
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (B : ∀ i, V i →ₗ[ℂ] H) (c : ι → ℝ),
    (LinearMap.trace ℂ H (frQ c B ∘ₗ frQ c B)).re
        = ∑ i, ∑ j, c i * c j * hs2 (LinearMap.adjoint (B i) ∘ₗ B j) ∧
    (LinearMap.trace ℂ H (frQ c B)).re
        = ∑ i, c i * (LinearMap.trace ℂ (V i) (LinearMap.adjoint (B i) ∘ₗ B i)).re

end Formalism.SL.FU
