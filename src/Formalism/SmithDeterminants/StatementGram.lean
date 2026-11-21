import Mathlib

open Finset
open scoped ComplexOrder

noncomputable section

namespace Formalism.A

def mfact {σ : Type*} (g : σ →₀ ℕ) : ℕ := g.prod fun _ n => n.factorial

def fockZ {σ : Type*} (f g : MvPolynomial σ ℤ) : ℤ :=
  ∑ m ∈ f.support, f.coeff m * g.coeff m * (mfact m : ℤ)

def famZ {σ ι : Type*} (E : ι → MvPolynomial σ ℤ) (α : ι → (σ →₀ ℕ)) (a : ι) :
    MvPolynomial σ ℤ :=
  E a * MvPolynomial.monomial (α a) 1

def fockG {σ : Type*} (f g : MvPolynomial σ GaussianInt) : GaussianInt :=
  ∑ m ∈ f.support, f.coeff m * star (g.coeff m) * (mfact m : GaussianInt)

def gramG {σ ι : Type*} (f : ι → MvPolynomial σ GaussianInt) : Matrix ι ι GaussianInt :=
  fun a b => fockG (f a) (f b)

end Formalism.A
