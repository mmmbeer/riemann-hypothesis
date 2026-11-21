import Mathlib
import Formalism.ThetaSupremumBounds.StatementE

open Finset
open scoped ComplexConjugate Real

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.TaylorCoefficientForms

open Formalism.DimensionVariation (mono mfact nsq liftBlock)

section Calculus

variable {E κ W : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [Fintype κ]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

def dirDeriv (v : E) (F : E → ℂ) : E → ℂ := fun z => fderiv ℂ F z v

def monoDeriv (v : κ → E) (e : κ → ℕ) (F : E → ℂ) : E → ℂ :=
  (univ : Finset κ).toList.foldr (fun x G => (dirDeriv (v x))^[e x] G) F

open Classical in

def coordVec (x : κ) : κ → ℂ := Pi.single x 1

def taylorCoeff (F : (κ → ℂ) → ℂ) (e : κ → ℕ) : ℂ :=
  monoDeriv coordVec e F 0 / (mfact e : ℂ)

end Calculus

def lineForm (ξ D D' : ℂ) : ℂ := 2 * (‖ξ‖ : ℂ) * (D * conj D')

def period (ξ D : ℂ) : ℝ := 1 / (π * (lineForm ξ D D).re)

section OnePlace

variable {A B : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [FiniteDimensional ℂ A]
  [NormedAddCommGroup B] [InnerProductSpace ℂ B] [FiniteDimensional ℂ B] {n₀ n₁ : ℕ}

end OnePlace

section AllPlaces

variable {Pl : Type} [Fintype Pl] {X₀ X₁ : Pl → Type}
  [∀ τ, NormedAddCommGroup (X₀ τ)] [∀ τ, InnerProductSpace ℂ (X₀ τ)] [∀ τ, FiniteDimensional ℂ (X₀ τ)]
  [∀ τ, NormedAddCommGroup (X₁ τ)] [∀ τ, InnerProductSpace ℂ (X₁ τ)] [∀ τ, FiniteDimensional ℂ (X₁ τ)]
  {n₀ n₁ : ℕ}

open Classical in

def letterTensor (τ : Pl) (D : ℂ) (x : X₀ τ →L[ℂ] X₁ τ) : ∀ σ, X₀ σ →L[ℂ] X₁ σ :=
  Pi.single (M := fun σ => X₀ σ →L[ℂ] X₁ σ) τ (D • x)

end AllPlaces

example (ξ D : ℂ) : period ξ D = 1 / (π * (2 * ‖ξ‖ * ‖D‖ ^ 2)) := by
  have : lineForm ξ D D = ((2 * ‖ξ‖ * ‖D‖ ^ 2 : ℝ) : ℂ) := by
    simp [lineForm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [period, this, Complex.ofReal_re]

example {E κ : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [Fintype κ] (v : κ → E) (F : E → ℂ) :
    monoDeriv v 0 F = F := by
  unfold monoDeriv
  induction (univ : Finset κ).toList with
  | nil => rfl
  | cons a l ih => simpa using ih

end GlobalTheory.IndefiniteRowSideFullHecke.TaylorCoefficientForms
