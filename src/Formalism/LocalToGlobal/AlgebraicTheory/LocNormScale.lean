import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.LogDerivativeJetsIntegral
import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.JetsInOfOneVariable
import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.UnitKer
import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.EtPower
import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.EtJets
import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.TensZEt
import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.TensorFourthPowerScaling
import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.ScalarConst
import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.DvdOfNormIntCastLt
import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.ColumnBoundOfPaths
import Formalism.LocalToGlobal.AlgebraicTheory.StatementKer
import ReciprocityTheory.ReductiveGroups.LatticeEmbeddings.IotaPlace
import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.XiConn
import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.EigenFrameDualOf
import ReciprocityTheory.EigenFrames.EigenPf
import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.CardTwoSidedQuotient
import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.KerHalf
import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.KerJet
import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.NormInter
import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.NormPow

section
noncomputable section
open scoped BigOperators ComplexConjugate
open NumberField IsDedekindDomain

namespace Formalism.L2.AlgTh

open Formalism.L2.Col (Fields Sp HomE homAt divLat)
open Formalism.L2.Ker (Amb DVar)

end Formalism.L2.AlgTh
end
end

section
namespace Formalism.L2.AlgTh

theorem logDerJets : LogDerJets := log_derivative_jets_integral
theorem powLogDer : PowLogDer := power_log_derivative_jets
theorem prodScaleJets : ProdScaleJets := product_scaling_jets
theorem linScale : LinScale := linear_scaling_jets
theorem unitKerInt : UnitKerInt := unit_kernel_integral_coords
theorem etPower : EtPower := etPower_of unitKerInt
theorem etJetsSigma : EtJetsSigma := etJetsSigma_of etPower logDerJets powLogDer
theorem etJetsTh0 : EtJetsTh0 := etJetsTh0_of etJetsSigma
theorem etThetaZ : EtThetaZ := etThetaZ_of etJetsTh0 prodScaleJets
theorem tensZEt : TensZEt := tensor_integral_torsion
theorem etLoc : EtLoc := etLoc_of tensZEt etThetaZ linScale
theorem scalarConst : ScalarConst := scalar_constant_value
theorem xiSwap : XiSwap := xi_swap
theorem xiEt : XiEt := xiEt_of etLoc

end Formalism.L2.AlgTh
end

section
namespace Formalism.L2.AlgTh

theorem xiConn : XiConn := xiConn_of etLoc scalarConst xiSwap
theorem split_place_scaled_bound : SelfDualLatticeThetaPadicIntegrality := split_bound_of_xi_lemmas xiEt xiConn
theorem eigenFrameDual : EigenFrameDual := eigenFrameDual_of ReciprocityTheory.EigenFramesTheory.eigenFrameDual
theorem kerFrame : KerFrame := kerFrame_of eigenFrameDual

end Formalism.L2.AlgTh
end

section
namespace Formalism.L2.AlgTh

theorem jetAtSplit : JetAtSplit :=
  jetAtSplit_of split_place_scaled_bound kernel_index_form representatives_split level_kills_half_lattice chosen_lift_killed_level p_torsion_represents_quotient card_two_sided_quotient index_product_formula
    taylor_jet_expansion linear_substitution_diagonal

end Formalism.L2.AlgTh
end
