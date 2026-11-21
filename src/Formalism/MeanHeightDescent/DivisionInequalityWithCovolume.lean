import Formalism.MeanHeightDescent.AverageDegreeBounds.Assembly
import Formalism.MeanHeightDescent.AverageDegreeBounds.DescentCut
import Formalism.MeanHeightDescent.AverageDegreeBounds.DescentSlope
import Mathlib
import Formalism.MeanHeightDescent.StatementJ
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.TheoremDivIneq
import Formalism.MeanHeightDescent.AverageDegreeBounds.CovolumeFullAssemblyHolds
import Formalism.MeanHeightDescent.AverageDegreeBounds.GoodBadCut
import Formalism.MeanHeightDescent.AverageDegreeBounds.MuMaxMinkowski
import Formalism.LogFactorialBounds.DepthIIExponent
import Formalism.MeanHeightDescent.AverageDegreeBounds.SpanMuMin
import Formalism.MeanHeightDescent.AverageDegreeBounds.TwistLower

section
noncomputable section

namespace Formalism.ExtensionFiltration

def BadCount : Prop :=
  ∀ db db1 db2 sh1 sh2 d d' H ε δ : ℝ,
    0 < H → 0 ≤ d' → d' ≤ H * d → 0 ≤ ε → ε ≤ 1 / 2 → 0 ≤ sh1 → 0 ≤ sh2 → sh1 + sh2 ≤ δ →
    db1 ≤ (1 + ε) * sh1 * d' / H → db2 ≤ (1 + ε) * sh2 * d' / H → db ≤ db1 + db2 →
    db ≤ 3 * δ * d

end Formalism.ExtensionFiltration
end
end

section
namespace Formalism.ExtensionFiltration

theorem lcvMu : LcvMu := log_covolume_slope_mu
theorem descentSlope : DescentSlope := descent_slope
theorem spanMuMin : SpanMuMin := span_min_slope
theorem goodBadCut : GoodBadCut := good_bad_split
theorem twistLower : TwistLower := twist_lower_bound
theorem muMaxMinkowski : MuMaxMinkowski := max_slope_minkowski
theorem mean_height_sum_bound : CombinedAverageDegreeBound := mean_height_sum_bound_holds

end Formalism.ExtensionFiltration
end
