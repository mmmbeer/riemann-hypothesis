import Formalism.HalfLinks.Statement

open Finset ArithmeticFunction

noncomputable section

namespace Formalism.WT

open Formalism Formalism.CMTypeGaloisData

def chiJ (d n : ℕ) : ℝ := (jacobiSym (n : ℤ) d : ℝ)

def DD (D z : ℝ) (M r : ℕ) : Finset ℕ :=
  (Icc ⌈D⌉₊ ⌊2 * D⌋₊).filter
    (fun d => d ≡ r [MOD 8 * M] ∧ Squarefree d ∧ ∀ p ∈ d.primeFactors, z < (p : ℝ))

def L1 {N : ℕ} (χ : DirichletCharacter ℂ N) : ℝ :=
  if h : N = 0 then 0 else
    haveI : NeZero N := ⟨h⟩; (DirichletCharacter.LFunction χ 1).re

def ell {N : ℕ} (χ : DirichletCharacter ℂ N) : ℝ :=
  if h : N = 0 then 0 else
    haveI : NeZero N := ⟨h⟩;
    (deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1).re

def GJ (d : ℕ) (χ : DirichletCharacter ℂ d) (y : ℝ) : ℝ := Gch (chiJ d) (ell χ) y

end Formalism.WT
