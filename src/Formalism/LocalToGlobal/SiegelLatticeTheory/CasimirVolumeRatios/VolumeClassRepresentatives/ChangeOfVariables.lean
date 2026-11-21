import Mathlib

noncomputable section

namespace Formalism.L2.S.S7.PositiveOrthantChangeOfVariables

open MeasureTheory Set
open scoped ENNReal

def posO (a : ℕ) : Set (Fin a → ℝ) := Set.univ.pi fun _ => Set.Ioi (0 : ℝ)

def chv {a : ℕ} (e : Fin a → ℝ) (t : Fin a → ℝ) : Fin a → ℝ := fun i => t i ^ (-(e i)⁻¹)

end Formalism.L2.S.S7.PositiveOrthantChangeOfVariables

end
