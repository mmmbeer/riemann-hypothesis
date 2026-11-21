import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.LemmaOneSevenOfFiniteOrder
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.CMFieldLemmas
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.PairwiseIndependenceComplementHolds
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FinOrdAd

namespace Formalism.MainNotions.Ext

theorem finOrdG_holds : FinOrdG := finite_order_adelic

end Formalism.MainNotions.Ext

namespace Formalism.MainNotions.UnusedSlot33

theorem division_rational_lattice (D : Formalism.BasicNotions.D7) : division_rows_rational_lattice D :=
  finiteModel_of_heckeEstimate D (finite_order_of_totally_real Formalism.MainNotions.Ext.finOrdG_holds D)

end Formalism.MainNotions.UnusedSlot33
