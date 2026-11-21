import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFormalFibresRegular
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def DerivationAdicCompletion.Statement : Prop :=
  ∀ (R : Type) [CommRing R] (I : Ideal R) (D : Derivation ℤ R R),
    ∃ D' : Derivation ℤ (AdicCompletion I R) (AdicCompletion I R),
      ∀ r : R, D' (algebraMap R (AdicCompletion I R) r) = algebraMap R (AdicCompletion I R) (D r)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
