import Formalism.JacobiWeightFamilies.Statement
import Formalism.LFunctionBounds.PositivityBound

open Finset ArithmeticFunction

noncomputable section

namespace Formalism.WT

open Formalism Formalism.CMTypeGaloisData

def wS (P : Finset ℕ) (t d : ℕ) : ℝ :=
  ∑ S ∈ ((P.filter (· ∣ d)).powerset).filter (fun S => S.card ≤ t), (-1 : ℝ) ^ S.card

def LFunctionOnePositive : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 → (∀ n : ℕ, (χ (n : ZMod N)).im = 0) →
    0 < (DirichletCharacter.LFunction χ 1).re

end Formalism.WT
