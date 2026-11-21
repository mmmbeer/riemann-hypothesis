import Mathlib
import Formalism.AlphaUniqueness.Statement
import Formalism.LatticeTheta.Statement
import Formalism.HermitianLattices.StatementLat

open Formalism.K

noncomputable section

namespace Formalism.HermitianLatticesTheory

section Defs

def weilT {D : Type*} (Q : D → ℂ) (f : D → ℂ) : D → ℂ := fun γ => Q γ * f γ

variable {K V : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (NumberField.RingOfIntegers K) V] [IsScalarTower (NumberField.RingOfIntegers K) K V]

def thetaL (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (NumberField.RingOfIntegers K) V) (γ : V)
    (τ : ℂ) : ℂ :=
  ∑' x : L, Complex.exp (Real.pi * Complex.I * τ *
    ((Algebra.trace ℚ K (h (γ + x) (γ + x)) : ℚ) : ℂ))

def thetaN (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (NumberField.RingOfIntegers K) V) (n : ℕ)
    (γ : Fin n → V) (τ : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  ∑' x : Fin n → L, Complex.exp (Real.pi * Complex.I * ∑ i, ∑ j,
    ((Algebra.trace ℚ K (h (γ i + x i) (γ j + x j)) : ℚ) : ℂ) * τ j i)

end Defs

def thetaE {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] (Λ : Submodule ℤ W) (γ : W)
    (τ : ℂ) : ℂ :=
  ∑' x : Λ, Complex.exp (Real.pi * Complex.I * τ * ((‖γ + (x : W)‖ ^ 2 : ℝ) : ℂ))

def ThetaBasic : Prop :=
  ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Module (NumberField.RingOfIntegers K) V] [IsScalarTower (NumberField.RingOfIntegers K) K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K), h.IsSymm →
    ∀ (L : Submodule (NumberField.RingOfIntegers K) V) (γ : V) (τ : ℂ),
      (∀ l ∈ L, thetaL h L (γ + l) τ = thetaL h L γ τ) ∧
      thetaL h L (-γ) τ = thetaL h L γ τ ∧
      (∀ g ∈ isom h, thetaL h (gmap g L) (g γ) τ = thetaL h L γ τ) ∧
      ((∀ x ∈ L, ∃ n : ℤ, Algebra.trace ℚ K (h x x) = 2 * n) →
        (∀ x ∈ L, ∃ n : ℤ, Algebra.trace ℚ K (h γ x) = n) →
        thetaL h L γ (τ + 1) =
          Complex.exp (Real.pi * Complex.I * ((Algebra.trace ℚ K (h γ γ) : ℚ) : ℂ)) *
            thetaL h L γ τ) ∧
      (∀ (n : ℕ) (γs : Fin n → V) (T : Matrix (Fin n) (Fin n) ℂ), ∀ g ∈ isom h,
        thetaN h (gmap g L) n (fun i => g (γs i)) T = thetaN h L n γs T) ∧
      (∀ T : Matrix (Fin 1) (Fin 1) ℂ, thetaN h L 1 (fun _ => γ) T = thetaL h L γ (T 0 0))

def ThetaSummable : Prop :=
  ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Module (NumberField.RingOfIntegers K) V]
    [IsScalarTower (NumberField.RingOfIntegers K) K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K), h.IsSymm →
    (∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x)) →
    ∀ L : Submodule (NumberField.RingOfIntegers K) V, Submodule.IsLattice K L →
    ∀ (γ : V) (τ : ℂ), 0 < τ.im →
      Summable (fun x : L => Complex.exp (Real.pi * Complex.I * τ *
        ((Algebra.trace ℚ K (h (γ + x) (γ + x)) : ℚ) : ℂ)))

end Formalism.HermitianLatticesTheory
