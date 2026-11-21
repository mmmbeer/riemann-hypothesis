import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.UnitaryHaarVolume
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.NonvanishingNearMaximum
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
import Formalism.LocalToGlobal.CMDeterminantIdeals.LambdaLowerBound

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.abelian₂

open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume
open scoped ENNReal

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def zNum (f r L d Om : ℝ) : ℝ := f * r + L + Real.log d + |Om|

def lamConst (C f r L d Om S : ℝ) : ℝ :=
  C * zNum f r L d Om ^ 2 * (1 + Real.log S) * S + C * (f * r * L) ^ 3

end GlobalTheory.CompanionTheory.Ar.abelian₂
