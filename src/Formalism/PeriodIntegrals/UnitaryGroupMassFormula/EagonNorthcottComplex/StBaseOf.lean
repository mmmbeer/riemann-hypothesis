import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.EagonNorthcottComplex.StSpecOf

universe u

noncomputable section

namespace PIW.ENSpec

open PI.EagonNorthcott MvPolynomial TensorProduct

def phiS (R : Type u) [CommRing R] (D : ℕ) : R ⊗[ℤ] MvPolynomial (Fin D) ℤ ≃ₗ[ℤ] MvPolynomial (Fin D) R :=
  (MvPolynomial.algebraTensorAlgEquiv ℤ R).toLinearEquiv.restrictScalars ℤ

def phiV (R : Type u) [CommRing R] (D m : ℕ) :
    R ⊗[ℤ] (Fin m → MvPolynomial (Fin D) ℤ) ≃ₗ[ℤ] (Fin m → MvPolynomial (Fin D) R) :=
  (TensorProduct.piRight ℤ ℤ R (fun _ : Fin m => MvPolynomial (Fin D) ℤ)).trans
    (LinearEquiv.piCongrRight fun _ => phiS R D)

end PIW.ENSpec
