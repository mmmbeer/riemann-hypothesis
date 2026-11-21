import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeightVectorExplicitFormula

noncomputable section

open Ad3.LR Filter Topology

namespace GlobalTheory.CompanionTheory.RowPolarization

variable {f g : M22 → ℂ} {h e : M22} {d d' : ℂ}

def Bc (x : M22) : ℂ := (x 0 1 : ℂ) + (x 1 1 : ℂ) * Complex.I

end GlobalTheory.CompanionTheory.RowPolarization
