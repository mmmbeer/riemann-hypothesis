import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.FrameTransport

noncomputable section

namespace PI.GaugeGap

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

def IsQuadInv {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) : Prop :=
  Module.finrank F E = 2 ∧ ∀ a : E, σ a = a ↔ a ∈ (algebraMap F E).range

def Target : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsQuadInv σ → ∃ G : GaugeFam F E σ, G.IsGauge

def CharAF : Prop :=
  ∀ (F : Type) [Field F] [NumberField F], ∃ ψ : AddChar (AF F) ℂ, IsCharAF F ψ

def Unimod : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsQuadInv σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ μ : Measure (HA (AF F) σ J), IsHaarH F E σ M J μ →
    ∀ g : HA (AF F) σ J, μ.map (fun h => h * g) = μ

end PI.GaugeGap
