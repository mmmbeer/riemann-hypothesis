import Mathlib
import Formalism.ThetaLogCoordinates.JacobiPathWeights.StatementA
import Formalism.ThetaLogCoordinates.JacobiPathWeights.StatementE

noncomputable section

open scoped BigOperators
open Finset MvPolynomial

namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases

def ValuationProductsComponents : Prop :=
  ∀ (k : Type) [Field k] (n N i : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ) (μ : ℕ → Fin n → ℤ)
    (I : ℤ → Finset (Fin n)), IsPath n isVec B μ N → IsIndex (μ N) I → i ≤ N →
    (∀ m : Fin n, m.val + 1 = n →
      ((μ i m : ℤ) : WithTop ℤ) ≤
        valS (ζ := Empty) isVec {j : ℕ | j < i} (rename Sum.inl (psiPath k isVec μ N I))) ∧
    (∀ m : Fin n, m.val = 0 →
      lam1S (ζ := Empty) isVec {j : ℕ | j < i} (rename Sum.inl (psiPath k isVec μ N I)) ≤
        ((μ i m : ℤ) : WithBot ℤ))

def JacobiMinor : Prop :=
  ∀ (R : Type) [CommRing R] (n : ℕ) (m : (Matrix (Fin n) (Fin n) R)ˣ) (I J : Finset (Fin n)),
    I.card = J.card →
    (↑m : Matrix (Fin n) (Fin n) R).det * minorF (↑m⁻¹ : Matrix (Fin n) (Fin n) R).transpose I J =
      (-1) ^ (∑ a ∈ I, a.val + ∑ b ∈ J, b.val) * minorF (↑m : Matrix (Fin n) (Fin n) R) Iᶜ Jᶜ

end Formalism.InvariantFactorPaths.GelfandTsetlinBases
