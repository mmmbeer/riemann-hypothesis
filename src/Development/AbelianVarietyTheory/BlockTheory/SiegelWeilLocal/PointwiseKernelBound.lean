import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd

open NumberField Finset

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.PointwiseKernelBound

open Formalism.MainNotions.S GlobalTheory.Count

def decHS (q : ℕ) (h t : ℝ) : ℝ := Real.exp (-(h / 8) * min (t ^ 2) (t / Real.sqrt (2 * (q : ℝ))))

example (q : ℕ) (h : ℝ) : decHS q h 0 = 1 := by simp [decHS]

example (q : ℕ) (h t : ℝ) (hh : 0 ≤ h) (ht : 0 ≤ t) : decHS q h t ≤ 1 := by
  unfold decHS
  rw [Real.exp_le_one_iff]
  have : 0 ≤ min (t ^ 2) (t / Real.sqrt (2 * (q : ℝ))) := le_min (by positivity) (by positivity)
  nlinarith [mul_nonneg hh this]

end GlobalTheory.IndefiniteRowSideFullHecke.PointwiseKernelBound
