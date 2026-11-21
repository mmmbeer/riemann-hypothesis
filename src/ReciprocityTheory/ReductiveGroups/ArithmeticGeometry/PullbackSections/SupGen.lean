import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TorusAtData

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2

def SupSecSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (X : PT E), ∀ s ∈ X.Sec 1 1, ∀ v,
    X.ptN2 1 s v ≤ 2 * (1 + 4 * Real.sqrt (2 * Fintype.card (Idx X.dim)) / (Real.sqrt Real.pi * X.la1)) ^
      (2 * Fintype.card (Idx X.dim)) * X.l2 1 s

end ReciprocityTheory.ChartRestriction.G.PullbackSections
