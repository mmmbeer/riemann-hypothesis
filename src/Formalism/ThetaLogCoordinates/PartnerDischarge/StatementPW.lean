import Formalism.ThetaLogCoordinates.TraceIsometryWeights.StatementG

namespace Formalism.InvariantFactorPaths.OddLevelGainBounds

open MvPolynomial Finset Formalism.GM.M Formalism.GM Formalism.InvariantFactorPaths.PW

noncomputable def logEightAPlusR (p : ℕ) (a : ℝ) (r : ℕ) : ℝ := Real.logb p (8 * a + r) + 1

end Formalism.InvariantFactorPaths.OddLevelGainBounds
