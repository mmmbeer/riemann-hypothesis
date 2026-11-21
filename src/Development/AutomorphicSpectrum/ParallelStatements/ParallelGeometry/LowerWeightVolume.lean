import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ChartSpec

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory
open GlobalTheory.CompanionTheory.Ar.Deg (vdeg rootPair)
open scoped ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.IndefiniteRowSideFullHecke.LowerWeightVolume

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def volConst (X : Data E r) (x0 : Frame X.Ψ r) (FF : Set (V (nd X))) : ℝ :=
  ((nd X).factorial : ℝ) * (Real.pi ^ nd X)⁻¹ * (muF X x0 FF).toReal

def vol (X : Data E r) (x0 : Frame X.Ψ r) (FF : Set (V (nd X))) (v : X.Ψ → Fin r → ℝ) : ℝ :=
  volConst X x0 FF * vdeg X v

end GlobalTheory.CompanionTheory.IndefiniteRowSideFullHecke.LowerWeightVolume
