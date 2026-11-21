import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.MainNotions

namespace GlobalTheory.CompanionTheory.Ar.HS

open NumberField

def RankBound : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyComplex F] (D N n δ T : ℕ)
    (X : ChowData F D N n δ) (Z : HSData X T) (J : ℝ), 2 ≤ D → D + 1 ≤ T → Z.ResBound J →
    (T - 1).choose D * δ ≤ Z.d T

end GlobalTheory.CompanionTheory.Ar.HS
