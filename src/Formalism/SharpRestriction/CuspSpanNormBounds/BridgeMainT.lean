import Formalism.SharpRestriction.CuspSpanNormBounds.UniformConstantsAndStatements
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalBesselAndTopKernel
import Formalism.SharpRestriction.CuspSpanNormBounds.PExtra
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.LocalFormOfHypotheses

noncomputable section

namespace Formalism.MainNotions.S.MainBoundWithDegrees

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Formalism.MainNotions.UniformConstantsAndStatements ValuativeRel IsDedekindDomain NumberField
open scoped ENNReal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Family

variable {eps : ℝ} (Fm : FamP eps)

end Family

def NuTotIndep (D : D7) (u u' : D.what₂.Word) : Prop :=
  ∀ F0 : FlagG (VS D) D.R.rS ((Lat.Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u →
    ∀ what₂ rows' : Finset (Cnt.LatV D), IsRowReps D F0 what₂ → IsRowReps D F0 rows' →
      ∀ Z : Cnt.GramM D, nuTot D u u' F0 what₂ Z = nuTot D u u' F0 rows' Z

end Formalism.MainNotions.S.MainBoundWithDegrees
