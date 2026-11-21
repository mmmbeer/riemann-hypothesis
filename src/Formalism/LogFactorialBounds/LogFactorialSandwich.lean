import Mathlib

noncomputable section

namespace Formalism.LogFactorialBounds

open Finset Real

def ph (y : ℝ) : ℝ := y * Real.log y - y

def LogFactorialSandwich : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    ph n + Real.log (2 * π * n) / 2 ≤ Real.log (n.factorial : ℝ) ∧
      Real.log (n.factorial : ℝ) ≤ ph n + Real.log n / 2 + 1

end Formalism.LogFactorialBounds
