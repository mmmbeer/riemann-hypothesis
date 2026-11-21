import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsCurrent
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.ImportsBis
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.GraphChartEventuallyEqSheet
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsLocalBranches
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

theorem LocalOrder.unfolding_form_of_matrix (hB : BranchesToGoodPosition.Statement)
    (h : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.LocalOrder.Statement) :
    GroundTheory.Heights₂.Heights.LocalOrder.Statement := by
  intro n d J W u p m γ ord hJ hdim hu hW hp hcov hsl hdisj hord
  obtain ⟨q, π, U, V, ρ, hg⟩ := hB n d J W u p m γ ord hJ hdim hu hW hp hcov hsl hdisj hord
  exact h n d J W u q π U V ρ _ ⟨hJ, hdim⟩ hu hW hg

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
