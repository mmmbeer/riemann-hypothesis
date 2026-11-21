import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.PlaceDegreeData
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.DefiniteGapThreshold
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsWeakIntegralOfStronglyContinuous
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CuspidalSubspaceClosedRightTranslationStable

open MeasureTheory NumberField Matrix
open scoped InnerProductSpace
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData GlobalTheory.IndefiniteRowSideFullHecke.IsotropicFlagConstantTerms

noncomputable section

namespace GlobalTheory.GlobalProjectorCompare

section Test

variable (I : AutInst) {H : InfinitePlace I.F → Type} [∀ v, NormedAddCommGroup (H v)]
  [∀ v, InnerProductSpace ℂ (H v)] (σ : ∀ v, Matrix (Fin I.n) (Fin I.n) ℂ → (H v →L[ℂ] H v)) (w : ∀ v, H v)

end Test

variable (I : AutInst)

end GlobalTheory.GlobalProjectorCompare
