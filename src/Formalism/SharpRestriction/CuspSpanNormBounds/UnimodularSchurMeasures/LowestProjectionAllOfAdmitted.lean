import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.IdempotentIntegrableOfCoeff
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.TraceConjMulEqHilbertSchmidt
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.SphericalL1StatementOfProjectors
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.SmoothVectorsTranslateUnitary

section
noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.CayleySignature

namespace BData

variable (X : BData)

def Exchange (B : X.H → X.Vp) : Prop :=
  ∀ χ, X.IsCut B χ →
    ∫ x, ⟪X.W' B (Matrix.of x), X.Wf B χ (Matrix.of x)⟫_ℂ ∂X.ν =
      ∫ x, ⟪rconv X.μG X.e (X.W' B) (Matrix.of x), X.Φ B χ (Matrix.of x)⟫_ℂ ∂X.ν

variable {X}

end BData

end Formalism.MainNotions.LeviCoordinates

end
end

section
noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.CayleySignature

namespace BData

variable {X : BData}

theorem meas_mul : Measurable fun p : Formalism.QuantumDeterminants.Mt X.k X.r × Formalism.QuantumDeterminants.Mt X.k X.r =>
    Formalism.QuantumDeterminants.lmulM (Matrix.of p.1) p.2 := by
  unfold Formalism.QuantumDeterminants.lmulM
  refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
  simp only [Matrix.mul_apply, Matrix.of_apply]
  refine Finset.measurable_sum _ fun l _ => ?_
  have h1 : Measurable fun p : Formalism.QuantumDeterminants.Mt X.k X.r × Formalism.QuantumDeterminants.Mt X.k X.r => p.1 i l := by fun_prop
  have h2 : Measurable fun p : Formalism.QuantumDeterminants.Mt X.k X.r × Formalism.QuantumDeterminants.Mt X.k X.r => p.2 l j := by fun_prop
  exact h1.mul h2

variable (X) in

def SquareIntegrabilityBound (B : X.H → X.Vp) : Prop := ∀ χ, X.IsCut B χ → l2SG X.ν (X.Wf B χ) < ⊤

end BData

end Formalism.MainNotions.LeviCoordinates

end
end
