import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature

namespace GlobalTheory.IndefiniteRowSideFullHecke.TorusMarkingPhase

open NumberField ReciprocityTheory.ChartRestriction.G

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def phAt (X : FD.Data E r) (θ : ℝ) (x : FD.Frame X.Ψ r) : ℝ :=
  if X.la1 x < θ then 2 * (I2.PT.f E : ℝ) / (I2.PT.rd E ^ 2 * X.la1 x ^ 2) else 0

def ph (X : FD.Data E r) (q : ℕ) (R0 : ℝ) (x : FD.Frame X.Ψ r) : ℝ :=
  phAt X (I2.th (E := E) q R0) x

end

end GlobalTheory.IndefiniteRowSideFullHecke.TorusMarkingPhase
