import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TorusAt

section
namespace GlobalTheory.CompanionTheory.Ar.ThA

open scoped Matrix ComplexConjugate

noncomputable section

end

end GlobalTheory.CompanionTheory.Ar.ThA
end

section
namespace GlobalTheory.CompanionTheory.Ar.ThA

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory
open scoped ENNReal ComplexConjugate ContDiff

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def nrm2 (X : Data E r) (x0 : Frame X.Ψ r) (FF : Set (V (nd X))) (la : Wt X.Ψ r)
    (P : Frame X.Ψ r → ℂ) : ℝ :=
  (∫ z in FF, X.pnorm la P (cpt X x0 z) ^ 2 ∂muF X x0) / (muF X x0 FF).toReal

def BergLB (X : Data E r) (x0 : Frame X.Ψ r) (FF : Set (V (nd X))) (la : Wt X.Ψ r)
    (x : Frame X.Ψ r) (t : ℝ) : Prop :=
  ∃ P ∈ X.SS la, 0 < nrm2 X x0 FF la P ∧ t * nrm2 X x0 FF la P ≤ X.pnorm la P x ^ 2

end

end GlobalTheory.CompanionTheory.Ar.ThA
end
