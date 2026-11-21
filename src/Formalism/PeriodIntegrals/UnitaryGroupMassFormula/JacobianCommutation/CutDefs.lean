import Formalism.HermitianCurvature.BigCellVanishingOfCommute
import Formalism.HermitianCurvature.StatementJF
import Formalism.FormalDegreeBessel.FinalBF

section
open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace PI.UnitaryGroupMassFormula.JCC

end PI.UnitaryGroupMassFormula.JCC
end
end

section
open MeasureTheory Filter Topology Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace PI.UnitaryGroupMassFormula.JCC

def kap {k r : ℕ} (p : B.SS k r) : ℝ :=
  max 1 (((2 * r + k + 1 : ℕ) : ℝ) * B.gN (JF.sR p) * B.gN (JF.sR p)⁻¹)

end PI.UnitaryGroupMassFormula.JCC
end
end
