import Mathlib
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.CyclicPowerClassOfExpEquiv
import Formalism.GaussJetBounds.StatementI

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.G7

open Formalism.DworkPowerSeriesWeights (Integral mvExp jetPair)

def atPlace {K Pl : Type} [Field K] {ι : Pl → Type} (v : Pl) (f : MvPowerSeries (ι v) K) :
    MvPowerSeries (Σ v, ι v) K :=
  MvPowerSeries.subst (fun i : ι v => (MvPowerSeries.X ⟨v, i⟩ : MvPowerSeries (Σ v, ι v) K)) f

end Formalism.InvariantFactorPaths.G7
