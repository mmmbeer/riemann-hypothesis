import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.ProjectionStatementOfFinal
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.LeftTranslateSet
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.PjTrInnerPure
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.SchurRelationAddSecond
import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.UnitaryRepUnimodularOfFiniteVolume
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.KernelDiagonalOfAbsoluteConvergence

section
noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal


section Dens

variable {G : Type} [MeasurableSpace G] (μ : Measure G) {Hs : Type} [NormedAddCommGroup Hs]
  [InnerProductSpace ℂ Hs] (σ : G → (Hs →L[ℂ] Hs))




end Dens

end Formalism.MainNotions.LeviCoordinates

end
end

section
noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Matrix Finset
open scoped InnerProductSpace ComplexOrder ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma



end Formalism.MainNotions.LeviCoordinates

end
end

section
noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Set
open scoped InnerProductSpace ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

def cu.End (X : CData) : Prop :=
  cu.UnipFine X ∧ cu.LocGrowth X ∧ (∃ S : CSize X, S.Strata ∧ S.PackCount ∧ S.Inv ∧ S.Lip ∧ S.LowN) ∧ AbsKernelSquareIntegrable X ∧
    UnimodA X

def cu_StepsEnd (n₀ : ℕ) (A C : ℝ) : Prop :=
  ∀ X : CData, X.HypB n₀ A → X.GapAboveThreeHalvesPower → X.GapAboveSquareRootThreshold C → cu.End X


end Formalism.MainNotions.LeviCoordinates
end
end
