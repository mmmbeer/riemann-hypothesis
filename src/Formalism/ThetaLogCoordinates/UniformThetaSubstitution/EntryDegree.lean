import Mathlib
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.StatementE

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.G7

open Formalism.DworkPowerSeriesWeights (Integral jetPair mfact)

def EntryDegree : Prop :=
  ∀ (K : Type) [Field K] (ν r0 r1 C : ℕ) [NeZero ν] (ξ : ZMod (2 * ν) → Fin r0 → K)
    (e : TpV ν r1 → ℕ) (l : Fin C → ℕ) (sf : Fin C → ZMod (2 * ν))
    (T : ∀ c, Fin (l c) → Fin r0 → K) (I : ∀ c, Fin (l c) → Fin r1),
    (entryOp ξ e l sf T I).IsHomogeneous (∑ s, (alN e s + lsN l sf s))

end Formalism.InvariantFactorPaths.G7
