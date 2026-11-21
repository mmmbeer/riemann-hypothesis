import Mathlib
import ReciprocityTheory.SemistableReduction.SphereLogIntegrableStatement
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.SphereBlockLogMean

open MeasureTheory NumberField MvPolynomial

noncomputable section

namespace GlobalTheory.HeightZeroCompare

open ReciprocityTheory.MultiplicativeHeights GlobalTheory.IndefiniteRowSideFullHecke.UnitSphereMeasure

theorem gaussAbs_eq {K : Type} [Field K] [NumberField K] {ι : Type} (w : FinitePlace K)
    (f : MvPolynomial ι K) : gaussAbs w f = gaussAbsValue w f := rfl

end GlobalTheory.HeightZeroCompare
