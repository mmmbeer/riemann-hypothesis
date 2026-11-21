import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramFibrationFormulas.IsGoodV

section
open scoped TensorProduct ENNReal
open MeasureTheory NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

noncomputable section

namespace PI.GramFibrationFormulas

end PI.GramFibrationFormulas
end
end

section
open scoped TensorProduct ENNReal
open MeasureTheory NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

noncomputable section

namespace PI.GramFibrationFormulas
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def FinVolH (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) : Prop :=
  ∀ μ : Measure (HA (AF F) σ J), μ.IsHaarMeasure →
    ∃ 𝓕, IsFundamentalDomain (HFinIn (AF F) σ J) 𝓕 μ ∧ μ 𝓕 < ⊤

def AnisotropicOrbitSurjective : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ (x : Fin 1 → Fin M → E) (β : F), β ≠ 0 → hE σ J (x 0) (x 0) = algebraMap F E β →
      let X := {y : Fin 1 → Fin M → AF F ⊗[F] E | qR (AF F) σ J (y 0) = algebraMap F (AF F) β}
      (∀ y ∈ X, ∃ g : HA (AF F) σ J, g • ratTup (F := F) (AF F) x = y) ∧
      Continuous (fun g : HA (AF F) σ J => g • ratTup (F := F) (AF F) x) ∧
      ∀ U : Set (HA (AF F) σ J), IsOpen U →
        ∃ O, IsOpen O ∧ (fun g : HA (AF F) σ J => g • ratTup (F := F) (AF F) x) '' U = O ∩ X

end PI.GramFibrationFormulas
end
end
