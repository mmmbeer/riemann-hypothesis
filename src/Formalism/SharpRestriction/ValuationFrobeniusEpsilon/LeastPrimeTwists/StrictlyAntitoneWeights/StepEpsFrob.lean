import Mathlib
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.StrictlyAntitoneWeights.GaussianCaseFreeExponents

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TV NumberField IsDedekindDomain Polynomial

namespace Formalism.MainNotions.V.Pf.V3

variable {D : D7} (V : VData D)

def StepEpsFrob : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K] (p : ℕ), p.Prime → p ≠ l →
    ∀ Fr : FrobAt K p, ((epsL l (Fr.φ : GQ) : (QbarL l)ˣ) : QbarL l) = ((Fr.q : ℕ) : QbarL l)⁻¹

end Formalism.MainNotions.V.Pf.V3
