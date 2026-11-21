import Formalism.MonomialMeanResidues.MonomialMean
import Mathlib
import Formalism.MonomialMeanResidues.FilteredDegree
import Formalism.MeanHeightDescent.DivisionInequalityWithCovolume
import Formalism.MonomialMeanResidues.MonomialMeanProofs.SubmoduleSlopeLowerOfFiltration
import Formalism.MonomialMeanResidues.MonomialMeanProofs.SpanEqTopAndRankOfLinearIndependent

section
open Module NumberField Finset

noncomputable section

namespace Formalism.HermiteSiegelSlopes

open Formalism.HN

def ZerosPerVariable : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [DecidableEq R] (q e : ℕ) (Cs : Finset R)
    (G : MvPolynomial (Fin q) R), G ≠ 0 → (∀ i, G.degreeOf i ≤ e) →
    ((Fintype.piFinset fun _ : Fin q => Cs).filter fun c => MvPolynomial.eval c G = 0).card
      ≤ q * e * Cs.card ^ (q - 1)

end Formalism.HermiteSiegelSlopes
end
end

section
namespace Formalism.HermiteSiegelSlopes

theorem baseChange : BaseChange := base_change_slope

end Formalism.HermiteSiegelSlopes
end
