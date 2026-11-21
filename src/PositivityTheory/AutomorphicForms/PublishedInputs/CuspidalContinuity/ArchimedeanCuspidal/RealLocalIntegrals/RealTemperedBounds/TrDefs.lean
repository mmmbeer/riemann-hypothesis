import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealSharpBounds.MatrixMulApply
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegenerateTermsVanish

noncomputable section

open MeasureTheory Matrix

namespace Ad3.LR.DTr

def WeightVanishesNegDetSmoothPosDet : Prop := ∀ k : ℕ, 3 ≤ k →
  (∀ h : M22, (Matrix.of h).det < 0 → w0 k h = 0) ∧ ContDiffOn ℝ (⊤ : ℕ∞) (w0 k) {h : M22 | 0 < (Matrix.of h).det}

end Ad3.LR.DTr
