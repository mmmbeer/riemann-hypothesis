import Mathlib

namespace Formalism.L2.Props

open Matrix
open scoped ComplexOrder

def HermDefON : Prop :=
  ∀ (n : ℕ) (G : Matrix (Fin n) (Fin n) ℂ), G.PosDef → ∃ y : Matrix (Fin n) (Fin n) ℂ, IsUnit y.det ∧ yᴴ * G * y = 1

end Formalism.L2.Props
