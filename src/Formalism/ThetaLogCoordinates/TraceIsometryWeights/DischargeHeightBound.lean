import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.InvInv
import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.InvInt
import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.HomRelationHolds
import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.SchurTraceOfHomInv
import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.TypeInt
import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.LatticeBasisPolynomial
import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.OrthogonalIsomorphismHolds
import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.CommProjectionHolds
import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.PolLeISupIsoW
import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.Discharge
import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.WeylInt
import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.ZpClosedToAddSubgroup
import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.CompEqZeroOfNotDle

section
namespace Formalism.InvariantFactorPaths.PW.Top

theorem invInv : InvInv := invariant_inverse_holds
theorem invNat : InvNat := invariant_natural_holds
theorem homInv : HomInv := homInv_of invInv
theorem schurTrace : SchurTrace := schurTrace_of invInv
theorem typeInt : TypeInt := typeInt_of invNat homInv schurTrace
theorem divInt : DivInt := divided_integral_holds
theorem latBasisPol : LatBasisPol := lattice_basis_polynomial
theorem projP : ProjP := projection_lattice_holds
theorem commP : CommP := comm_projection_holds
theorem intP : IntP := intP_of typeInt latBasisPol
theorem dischargeP : DischargeP := dischargeP_of projP commP intP

end Formalism.InvariantFactorPaths.PW.Top
end

section
namespace Formalism.InvariantFactorPaths.PW.Top

theorem weylInt : WeylInt := weyl_integral_holds
theorem weylP : WeylP := weylP_of weylInt lattice_basis_polynomial

private theorem intP_statement : IntP := by
  have hInv : InvInv := invariant_inverse_holds
  exact intP_of (typeInt_of invariant_natural_holds (homInv_of hInv) (schurTrace_of hInv)) lattice_basis_polynomial

theorem extP : ExtP := extP_of intP_statement
theorem dischargeW : DischargeW := dischargeW_of weylP
theorem dischargeE : DischargeE := dischargeE_of extP

end Formalism.InvariantFactorPaths.PW.Top
end
