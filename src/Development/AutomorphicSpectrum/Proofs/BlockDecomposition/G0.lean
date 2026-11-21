import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.UnipotentTateFunctionalEquation
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.FunctionalEquationGL2GL1Complex

noncomputable section

open MeasureTheory
open Ad3 Ad3.LR Ad3.LR.C

namespace GlobalTheory.CompanionTheory.PuBnd

def V (k : ℕ) (σ T : ℝ) : ℝ := |T| ^ ((k : ℝ) - 1 - σ) * Real.exp (-(Real.pi * |T|))

def G0 (k : ℕ) (σ a b c d : ℝ) : ℝ :=
  |a| ^ (-2 - σ) / ((1 + |a|) ^ 2 * (1 + |b|) ^ 2) * V k σ ((d - c * b / a) / a)

end GlobalTheory.CompanionTheory.PuBnd
