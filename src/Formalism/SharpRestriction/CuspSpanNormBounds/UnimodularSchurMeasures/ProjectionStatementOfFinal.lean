import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.CuspidalRangeOfReproUnipotent
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RightRegularIsometricMultiplicative
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RrkbLeOneAddSq
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RrkpCoefCont
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.CndTauSLeHalf

section
noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Set
open scoped InnerProductSpace ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma






def cu.Core (X : CData) : Prop :=
  cu.UnipFine X ∧ cu.HaarGrowth X ∧ cu.SizeStep X ∧ X.KernelDiag ∧ UnimodA X


end Formalism.MainNotions.LeviCoordinates
end
end

section
noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Set
open scoped InnerProductSpace ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

def CSize.Inv {X : CData} (S : CSize X) : Prop := ∀ γ ∈ X.I.GFset, ∀ y, S.tau1 (γ * y) = S.tau1 y

def CSize.Lip {X : CData} (S : CSize X) : Prop :=
  ∀ y g, X.φ g ≠ 0 →
    S.tau1 y * Real.exp (-(1 / (X.I.f : ℝ)) * ∑ v, cartanDistance (X.I.ε v) (g.1 v)) ≤ S.tau1 (y * g)

def CSize.LowN {X : CData} (S : CSize X) : Prop :=
  ∀ W : Submodule X.I.E (Fin X.I.n → X.I.E), X.I.IsIsot W → ∀ x, ∃ c : ℝ, 0 < c ∧ ∀ m ∈ X.I.NA W, c ≤ S.tau1 (m * x)



end Formalism.MainNotions.LeviCoordinates
end
end

section
noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Set
open scoped InnerProductSpace ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

def cu.LocGrowth (X : CData) : Prop :=
  ∀ (v : InfinitePlace X.I.F) (s : ℝ), 0 ≤ s →
    (1 ≤ q0At X.I v →
      2 * (X.I.n : ℝ) * Real.sqrt (2 * (q0At X.I v : ℝ)) + s < X.h / 8 / Real.sqrt (2 * (q0At X.I v : ℝ))) →
    Integrable (fun g : Formalism.REAL.UJ (X.I.ε v) =>
      ‖coefOn (X.σ v) (X.w v) (X.w v) g‖ * Real.exp (s * cartanDistance (X.I.ε v) g)) (Formalism.REAL.muG (X.I.ε v))


def cu.Last (X : CData) : Prop :=
  cu.UnipFine X ∧ cu.LocGrowth X ∧ (∃ S : CSize X, S.Strata ∧ S.PackCount ∧ S.Inv ∧ S.Lip ∧ S.LowN) ∧ X.KernelDiag ∧
    UnimodA X


end Formalism.MainNotions.LeviCoordinates
end
end
