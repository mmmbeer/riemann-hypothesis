import Formalism.JacobiWeightFamilies.LFunctionOnePositive

open Finset ArithmeticFunction

noncomputable section

namespace Formalism.TwistFamilyExistence₂

open Formalism Formalism.CMTypeGaloisData Formalism.WT

def Lc {N : ℕ} (χ : DirichletCharacter ℂ N) : ℂ :=
  if h : N = 0 then 0 else
    haveI : NeZero N := ⟨h⟩; DirichletCharacter.LFunction χ 1

def chiT {q : ℕ} (d : ℕ) (ψ : DirichletCharacter ℂ q) (n : ℕ) : ℂ :=
  ((jacobiSym (n : ℤ) d : ℤ) : ℂ) * ψ (n : ZMod q)

def primesUpTo (y0 : ℝ) : Finset ℕ := (range (⌊y0⌋₊ + 1)).filter Nat.Prime

def Mo (χ : ℕ → ℂ) (y0 : ℝ) (K : ℕ) : ℂ :=
  ∑ S ∈ (primesUpTo y0).powerset.filter (fun S => S.card ≤ K),
    (-1 : ℂ) ^ S.card * χ (∏ p ∈ S, p) / (((∏ p ∈ S, p : ℕ) : ℝ) : ℂ)

def rho (A : ℕ) (D z : ℝ) : ℝ :=
  (Real.exp (-(Real.log D / (10 * Real.log z))) + Real.log D / z) * Real.log D ^ A

end Formalism.TwistFamilyExistence₂
