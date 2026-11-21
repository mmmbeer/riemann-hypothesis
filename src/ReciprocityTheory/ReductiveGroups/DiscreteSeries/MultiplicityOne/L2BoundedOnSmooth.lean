import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StDiagExists
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleySignature

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.MainNotions.S

def L2BoundedOnSmooth {k r : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {Wp : Type*}
    [NormedAddCommGroup Wp] (ν : Measure (Mt k r)) (σ : Mat k r → (H →L[ℂ] H)) (B : H → Wp) : Prop :=
  ∃ C : ℝ≥0, ∀ v ∈ smoothVecs (k := k) (r := r) σ,
    l2SG (k := k) (r := r) ν (fun g => B (σ g v)) ≤ (C : ℝ≥0∞) * (‖v‖₊ : ℝ≥0∞) ^ 2

end ReciprocityTheory.ChartRestriction.DS.Mult1
