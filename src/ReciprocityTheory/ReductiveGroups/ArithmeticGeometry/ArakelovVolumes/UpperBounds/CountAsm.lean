import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.CountRhoPArithStatement

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

open Classical in

def onDom {r : ℕ} (X : Data E r) (f : Frame X.Ψ r → ℂ) : Frame X.Ψ r → ℂ :=
  fun x => if x ∈ X.dom then f x else 0

end

end ReciprocityTheory.ChartRestriction.G.AR.Up
