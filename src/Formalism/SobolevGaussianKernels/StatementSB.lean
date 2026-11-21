import Mathlib

namespace Formalism.SL.SB

open MeasureTheory
open scoped ContDiff

noncomputable def pd {n : ℕ} (i : Fin n) (g : (Fin n → ℝ) → ℂ) : (Fin n → ℝ) → ℂ :=
  fun y => fderiv ℝ g y (Pi.single i 1)

noncomputable def mixed {n : ℕ} (α : Finset (Fin n)) (g : (Fin n → ℝ) → ℂ) : (Fin n → ℝ) → ℂ :=
  (α.sort (· ≤ ·)).foldr pd g

def cube {n : ℕ} (a : Fin n → ℝ) (δ : ℝ) : Set (Fin n → ℝ) :=
  Set.pi Set.univ (fun i => Set.Icc (a i) (a i + δ))

end Formalism.SL.SB
