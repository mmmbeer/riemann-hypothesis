import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeightVectorExplicitFormula

noncomputable section

open MeasureTheory Matrix Complex

namespace Ad3.LR.DK

def Fr (k : ℕ) (s t : ℝ) : ℝ :=
  if 0 < t then (s * t) ^ (k - 2) * s⁻¹ ^ (1 / 2 : ℝ) *
    Real.exp (-2 * Real.pi * t - Real.pi * s - Real.pi * s * t ^ 2 - Real.pi / (s * t ^ 2) - Real.pi / s)
  else 0

end Ad3.LR.DK

namespace Ad3.LR

open DK

end Ad3.LR
