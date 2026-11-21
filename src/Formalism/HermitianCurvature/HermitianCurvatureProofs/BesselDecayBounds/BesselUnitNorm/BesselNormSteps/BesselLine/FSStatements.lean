import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.BesselLine.SfiniteMuN

open MeasureTheory Matrix Finset
open scoped InnerProductSpace

noncomputable section

namespace PI.WBL.FSW

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions PI.BesselLine PI.WBL

section Generic

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp]

def sM (p : Mt k r × Mt k r) : Mx k r := Matrix.of p.1 * Matrix.of p.2

def GHyp (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG ν : Measure (Mt k r))
    (σ : Mx k r → (H →L[ℂ] H)) : Prop :=
  (∃ (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ), IsHCParam lam ∧ IsDSHpk k r ε lam σ) ∧
    IsHaarOn (UH (Hpk k r)) μG ∧ (inWb k r z ∧ 0 < Tz k r z) ∧ (∃ u : Fin k → ℝ, IsHCTypeW k r z u π) ∧
    (IsHaarOn (UWset k r z) μW ∧ μW Set.univ = 1) ∧
    (∃ κ : ENNReal, 0 < κ ∧ κ ≠ ⊤ ∧ μN = haarLie (Nset k r) κ) ∧ IsQuotMeas μG (muSof μW μN) ν

def Aop (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN : Measure (Mt k r))
    (σ : Mx k r → (H →L[ℂ] H)) (w v : H) (y : Mx k r) : Wp →L[ℂ] Wp :=
  be z c π μW μN σ (σ y w) v

def SchurOn (μG : Measure (Mt k r)) (σ : Mx k r → (H →L[ℂ] H)) : Prop :=
  ∃ d : ℝ, 0 < d ∧ ∀ v w v' w' : H,
    Integrable (fun x : Mt k r => ⟪w, σ (Matrix.of x) v⟫_ℂ * star ⟪w', σ (Matrix.of x) v'⟫_ℂ) μG ∧
    ∫ x, ⟪w, σ (Matrix.of x) v⟫_ℂ * star ⟪w', σ (Matrix.of x) v'⟫_ℂ ∂μG = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ)

end Generic

def SchurH : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx k r → (H →L[ℂ] H)) (μG : Measure (Mt k r)),
    IsHCParam lam → IsDSHpk k r ε lam σ → IsHaarOn (UH (Hpk k r)) μG → SchurOn μG σ

def NuStep : Prop :=
  ∀ (k r : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp]
    (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG ν : Measure (Mt k r))
    (σ : Mx k r → (H →L[ℂ] H)), GHyp z π μW μN μG ν σ → ∀ᵐ x ∂ν, Matrix.of x ∈ UH (Hpk k r)

def WeilStep : Prop :=
  ∀ (k r : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp]
    (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG ν : Measure (Mt k r))
    (σ : Mx k r → (H →L[ℂ] H)), GHyp z π μW μN μG ν σ →
    ∀ F : Mx k r → ℂ, Integrable (fun x : Mt k r => F (Matrix.of x)) μG →
      (∀ᵐ x ∂ν, Integrable (fun p => F (sM p * Matrix.of x)) (μW.prod μN)) ∧
      Integrable (fun x : Mt k r => ∫ p, F (sM p * Matrix.of x) ∂(μW.prod μN)) ν ∧
      ∫ x, F (Matrix.of x) ∂μG = ∫ x, (∫ p, F (sM p * Matrix.of x) ∂(μW.prod μN)) ∂ν

section Assembly

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp]

end Assembly

end PI.WBL.FSW
