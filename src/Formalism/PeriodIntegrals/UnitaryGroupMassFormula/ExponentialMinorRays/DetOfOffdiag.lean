import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.CBFiLower

noncomputable section
open Matrix Finset

namespace PI.EMR

def dg {m : ℕ} (e : Fin m → ℝ) : Matrix (Fin m) (Fin m) ℂ := Matrix.diagonal (fun j => (e j : ℂ))

def ws {n m : ℕ} (B : Matrix (Fin n) (Fin m) ℂ) (e : Fin m → ℝ) (k : Fin n) : ℝ :=
  ∑ j, ‖B k j‖ ^ 2 * e j

def ex {m : ℕ} (y : Fin m → ℝ) (t : ℝ) : Fin m → ℝ := fun j => Real.exp (t * y j)

end PI.EMR
