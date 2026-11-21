import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.UnitNorm

open MeasureTheory Matrix Filter Topology

noncomputable section

namespace PI.WUN

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions PI.UnitNorm

def bInt {k r : ℕ} (L : LocBessel k r) (F : Mx k r → (L.Wq →L[ℂ] L.Wp)) (g : Mx k r)
    (x : (Mt k r × Mt k r) × (Mt k r × Mt k r)) : L.Wq →L[ℂ] L.Wp :=
  (psi k r L.z L.c (Matrix.of x.1.2) * star (psi k r L.z' L.c (Matrix.of x.2.2))) •
    ((L.π (Matrix.of x.1.1)).comp
      ((F ((Matrix.of x.1.1)⁻¹ * (Matrix.of x.1.2)⁻¹ * g * Matrix.of x.2.2 * Matrix.of x.2.1)).comp
        (L.π' (Matrix.of x.2.1)⁻¹)))

def bMeas {k r : ℕ} (L : LocBessel k r) : Measure ((Mt k r × Mt k r) × (Mt k r × Mt k r)) :=
  (L.μW.prod L.μN).prod (L.μW'.prod L.μN)

theorem J_eq {k r : ℕ} (L : LocBessel k r) (F : Mx k r → (L.Wq →L[ℂ] L.Wp)) (g : Mx k r) :
    L.J F g = ∫ x, bInt L F g x ∂(bMeas L) := rfl

end PI.WUN
