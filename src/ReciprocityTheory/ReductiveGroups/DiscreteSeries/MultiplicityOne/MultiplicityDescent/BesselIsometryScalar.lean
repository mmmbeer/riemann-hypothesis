import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.L2BoundedOnSmooth
import Mathlib.Analysis.InnerProductSpace.TensorProduct

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal ComplexConjugate TensorProduct

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.Down

open ReciprocityTheory.ChartRestriction.DS.Mult1 Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

def KFin : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp) (X : SigData k r), IsDiag D → SqIntG D X →
    aM k r ≤ X.a → ∀ l : X.Hs → Wp, IsMultOneMap D X l → (∃ v ∈ Vfl X, l v ≠ 0) →
      ∃ v₀ ∈ Vfl X, Formalism.MainNotions.S.IsKFinHpk (k := k) (r := r) X.σ v₀ ∧ l v₀ ≠ 0

def BesselIsometryScalar : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp) (X : SigData k r), IsDiag D → SqIntG D X →
    aM k r ≤ X.a → ∀ l : X.Hs → Wp, IsMultOneMap D X l → ∀ d : ℝ, IsFdegG D X d →
      ∀ (E : Submodule ℂ X.Hs) (B : X.Hs →ₗ[ℂ] Wp) (ν : Measure (Mt k r)),
        Formalism.MainNotions.S.IsQuotMeas D.μG (muS D) ν → Dense (E : Set X.Hs) → X.w ∈ E →
        (∀ g ∈ GV k r, ∀ v ∈ E, X.σ g v ∈ E) →
        (∀ h ∈ UWset k r D.z, ∀ m ∈ Nset k r, ∀ v ∈ E, B (X.σ (m * h) v) = psiD D m • D.π h (B v)) →
        (∀ v ∈ E, ContinuousOn (fun g => B (X.σ g v)) (GV k r)) →
        (∀ v ∈ E, ∫⁻ x : Mt k r, ‖B (X.σ (Matrix.of x) v)‖ₑ ^ 2 ∂ν = ENNReal.ofReal (‖v‖ ^ 2)) →
        (∃ v ∈ Vfl X, l v ≠ 0) ∧ ∃ c : ℂ, ‖c‖ ^ 2 = d ∧ ∀ v ∈ E, v ∈ Vfl X → B v = c • l v

end ReciprocityTheory.ChartRestriction.DS.Mult1.Down
