import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.EigLatBasis

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ExponentialEtaPeriod

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped UpperHalfPlane

def principalForm (Λ : Submodule ℤ ℂ) (z w : ℂ) : ℂ :=
  z * starRingEnd ℂ w / (ZLattice.covolume Λ : ℝ)

def sqLen (Λ : Submodule ℤ ℂ) (z : ℂ) : ℝ := Real.pi * (principalForm Λ z z).re

def IsExponential {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A] (D : epsR R ⟶ A) (φ : R →+* ℂ)
    (ex : ℂ → (Over.mk (spMap φ) ⟶ A)) (Λ : Submodule ℤ ℂ) : Prop :=
  (∀ z w, ex (z + w) = ex z * ex w) ∧ Function.Surjective ex ∧ (∀ z, ex z = 1 ↔ z ∈ Λ) ∧
    DiscreteTopology Λ ∧ Submodule.span ℝ (Λ : Set ℂ) = ⊤ ∧
    IsHolTo Set.univ (fun z => (ex z).left) ∧
    IsDerivAt0 (g := 1) (fun z => (ex (z 0)).left) (fun _ => 1)
      (spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR φ) ≫ D.left)

def IsClassPoint {K : Type} [Field K] [NumberField K] (io : K →+* ℂ) (C : ClassGroup (𝓞 K)) (τ : ℍ) : Prop :=
  ∃ (I : nonZeroDivisors (Ideal (𝓞 K))) (ω : ℂ), ClassGroup.mk0 I = C ∧ ω ≠ 0 ∧
    ∀ z : ℂ, (∃ a ∈ (I : Ideal (𝓞 K)), io (a : K) = z) ↔ ∃ m n : ℤ, z = ω * (m + n * (τ : ℂ))

def etaPeriod (τ : ℍ) : ℝ := 4 * Real.pi * τ.im * ‖ModularForm.eta (τ : ℂ)‖ ^ 4

end GlobalTheory.IndefiniteRowSideFullHecke.ExponentialEtaPeriod
