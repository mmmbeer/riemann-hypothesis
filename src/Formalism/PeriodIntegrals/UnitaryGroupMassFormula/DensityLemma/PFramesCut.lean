import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DensityLemma.PTopDensCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne

section
open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace PI.UnitaryGroupMassFormula.DLm

section
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

def frVal (D : B.RealPlaceData k r Wp Wq) (μ0 μ0' : Measure (Mt k r)) (F : B.Mat k r → (Wq →L[ℂ] Wp))
    (L : B.Mat k r → (Wp ≃L[ℂ] Wp) × (Wq ≃L[ℂ] Wq)) (g : B.Mat k r) : Wq →L[ℂ] Wp :=
  ((L g).1 : Wp →L[ℂ] Wp).comp ((fibInt D μ0 μ0' F g).comp ((L g).2 : Wq →L[ℂ] Wq))

def IsFrameAlg (D : B.RealPlaceData k r Wp Wq) (μ0 μ0' : Measure (Mt k r))
    (L : B.Mat k r → (Wp ≃L[ℂ] Wp) × (Wq ≃L[ℂ] Wq)) : Prop :=
  (∀ g ∈ B.GV k r, 0 < Gf k r D.z D.z' g → ∀ n ∈ Nset k r, ∀ n' ∈ Nset k r,
      0 < Gf k r D.z D.z' (n⁻¹ * g * n') ∧ L (n⁻¹ * g * n') = L g) ∧
  (∀ (F : B.Mat k r → (Wq →L[ℂ] Wp)), ∀ g₁ ∈ B.GV k r, ∀ g₂ ∈ B.GV k r, 0 < Gf k r D.z D.z' g₁ →
      Zhat k r D.z D.z' g₁ = Zhat k r D.z D.z' g₂ → frVal D μ0 μ0' F L g₁ = frVal D μ0 μ0' F L g₂)

open Classical in

def phi0 (D : B.RealPlaceData k r Wp Wq) (μ0 μ0' : Measure (Mt k r)) (L : B.Mat k r → (Wp ≃L[ℂ] Wp) × (Wq ≃L[ℂ] Wq))
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) {p m' : ℕ} (hps : p + (m' + 1 + 1) = r + 1) :
    G.Mat (p + (m' + 1 + 1)) → (Wq →L[ℂ] Wp) := fun Z =>
  if h : ∃ g, g ∈ B.GV k r ∧ 0 < Gf k r D.z D.z' g ∧ castM hps.symm (Zhat k r D.z D.z' g) = Z then
    frVal D μ0 μ0' F L (Classical.choose h) else 0

end

end PI.UnitaryGroupMassFormula.DLm
end
end

section
open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace PI.UnitaryGroupMassFormula.DLm

section
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

def fdMaj (D : B.RealPlaceData k r Wp Wq) (μ0 μ0' : Measure (Mt k r)) (A : ℝ) (g : B.Mat k r) : ENNReal :=
  ∫⁻ x : B.SS k r, ENNReal.ofReal (B.gN (B.sgs x g) ^ (-A)) ∂((D.μW.prod μ0).prod (D.μW'.prod μ0'))

def FdLocal (D : B.RealPlaceData k r Wp Wq) (μ0 μ0' : Measure (Mt k r))
    (L : B.Mat k r → (Wp ≃L[ℂ] Wp) × (Wq ≃L[ℂ] Wq)) : Prop :=
  ∀ g₀ ∈ B.GV k r, 0 < Gf k r D.z D.z' g₀ → ∃ (O : Set (B.Mat k r)) (Λ₁ : B.Mat k r → (Wp →L[ℂ] Wp))
    (Λ₂ : B.Mat k r → (Wq →L[ℂ] Wq)), IsOpen O ∧ g₀ ∈ O ∧
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Λ₁ O ∧ ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Λ₂ O ∧
    ∀ g ∈ O, g ∈ B.GV k r → 0 < Gf k r D.z D.z' g → ∀ F : B.Mat k r → (Wq →L[ℂ] Wp),
      frVal D μ0 μ0' F L g = (Λ₁ g).comp ((fibInt D μ0 μ0' F g).comp (Λ₂ g))

end

def FdGram : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (μ0 μ0' : Measure (Mt k r)), 1 ≤ r → B.IsHaarOn (C2.N0set k r D.z) μ0 → B.IsHaarOn (C2.N0set k r D.z') μ0' →
    ∃ L : B.Mat k r → (Wp ≃L[ℂ] Wp) × (Wq ≃L[ℂ] Wq), IsFrameAlg D μ0 μ0' L ∧ FdLocal D μ0 μ0' L

end PI.UnitaryGroupMassFormula.DLm
end
end
