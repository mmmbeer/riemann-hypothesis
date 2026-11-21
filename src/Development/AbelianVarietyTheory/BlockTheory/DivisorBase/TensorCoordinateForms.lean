import Mathlib
import Formalism.ThetaSupremumBounds.StatementE

open Finset
open scoped ComplexConjugate Real

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.TensorCoordinateForms

def dirDeriv {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (v : V) (F : V → ℂ) : V → ℂ :=
  fun z => fderiv ℂ F z v

def wordDeriv {κ V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (v : κ → V) (w : List κ)
    (F : V → ℂ) : V → ℂ :=
  w.foldr (fun x G => dirDeriv (v x) G) F

def IsSpelling {κ : Type} [DecidableEq κ] (w : (κ → ℕ) → List κ) : Prop :=
  ∀ e x, (w e).count x = e x

def lineForm (a : ℝ) (D D' : ℂ) : ℂ := 2 * (a : ℂ) * (D * conj D')

def omega (a : ℝ) (D : ℂ) : ℝ := 1 / (π * (lineForm a D D).re)

section OnePlace

variable {X X' : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X]
  [NormedAddCommGroup X'] [InnerProductSpace ℂ X'] [FiniteDimensional ℂ X'] {n₀ n₁ : ℕ}

end OnePlace

section Places

variable {Pl : Type} [Fintype Pl] [DecidableEq Pl] {X X' : Pl → Type}
  [∀ τ, NormedAddCommGroup (X τ)] [∀ τ, InnerProductSpace ℂ (X τ)] [∀ τ, FiniteDimensional ℂ (X τ)]
  [∀ τ, NormedAddCommGroup (X' τ)] [∀ τ, InnerProductSpace ℂ (X' τ)] [∀ τ, FiniteDimensional ℂ (X' τ)]
  {n₀ n₁ : ℕ}

end Places

def coordVec {κ : Type} [DecidableEq κ] (p : κ) : κ → ℂ := Pi.single p 1

example : omega (1 / (2 * π)) 1 = 1 := by
  have h : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  have : lineForm (1 / (2 * π)) 1 1 = ((1 / π : ℝ) : ℂ) := by
    have h' : (π : ℂ) ≠ 0 := by exact_mod_cast h
    simp only [lineForm, map_one, mul_one]; push_cast; field_simp
  rw [omega, this, Complex.ofReal_re]; field_simp

end GlobalTheory.IndefiniteRowSideFullHecke.TensorCoordinateForms
