import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramFibrationFormulas.AnisotropicOrbitSurjective
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

def IsQFib (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (v : HeightOneSpectrum (𝓞 F))
    (μ : Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)) (ν : Measure (Fv F v))
    (fq : Fv F v → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)) : Prop :=
  IsFibreFamily μ (fun X => qR (Fv F v) σ J (X 0)) id {X | X 0 ≠ 0} ν Set.univ fq

end PI.GramFibrationFormulas
end
end

section
open scoped TensorProduct ENNReal
open MeasureTheory NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

noncomputable section

namespace PI.GramFibrationFormulas

def IsotropicLatticeCount : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (d M : ℕ) (b : Module.Basis (Fin d) F E) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    3 ≤ M → ∀ L' : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin 1 → Fin M → Fv F v ⊗[F] E),
    (∀ v, IsCompact (L' v) ∧ IsOpen (L' v) ∧ 0 ∈ L' v ∧ (∀ x ∈ L' v, ∀ y ∈ L' v, x + y ∈ L' v) ∧
      ∀ x ∈ L' v, -x ∈ L' v) →
    (∀ᶠ v in Filter.cofinite, L' v = latV b v) →
    ∀ (μ : Measure (HA (AF F) σ J)) 𝓕, μ.IsHaarMeasure → IsFundamentalDomain (HFinIn (AF F) σ J) 𝓕 μ →
      let N := fun R : ℝ => ∫⁻ h in 𝓕, ∑' x : (Fin 1 → Fin M → E),
        {x : Fin 1 → Fin M → E | x 0 ≠ 0 ∧
          (∀ v, projV v (projFin (h⁻¹ • ratTup (F := F) (AF F) x)) ∈ L' v) ∧
          sizeTup b (projInf (h⁻¹ • ratTup (F := F) (AF F) x)) ≤ R}.indicator 1 x ∂μ
      let dF := Module.finrank ℚ F
      (∀ R, N R < ⊤) ∧
      (∀ r R : ℝ, 0 < r → r ≤ R → N R ≤ ENNReal.ofReal ((5 * R / r) ^ (2 * M * dF)) * (μ 𝓕 + N r)) ∧
      ∃ r₀ C : ℝ, 0 < r₀ ∧ ∀ R : ℝ, 0 < R → R ≤ r₀ → N R ≤ ENNReal.ofReal (C * R ^ ((2 * M - 2) * dF))

end PI.GramFibrationFormulas
end
end

section
open scoped TensorProduct ENNReal
open MeasureTheory NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

noncomputable section

namespace PI.GramFibrationFormulas

def RationalPointsLattice : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    Countable (HFinIn (AF F) σ J) ∧ DiscreteTopology (HFinIn (AF F) σ J) ∧
    (∀ n : ℕ, DiscreteTopology (Set.range (ratTup (F := F) (AF F) : (Fin n → Fin M → E) → _)) ∧
      ∃ K : Set (Fin n → Fin M → AF F ⊗[F] E), IsCompact K ∧
        ∀ Y, ∃ X : Fin n → Fin M → E, Y - ratTup (F := F) (AF F) X ∈ K) ∧
    (∃ μ : Measure (HA (AF F) σ J), μ.IsHaarMeasure) ∧
    ∀ μ : Measure (HA (AF F) σ J), μ.IsHaarMeasure → ∃ 𝓕, IsFundamentalDomain (HFinIn (AF F) σ J) 𝓕 μ

end PI.GramFibrationFormulas
end
end

section
open scoped TensorProduct ENNReal
open MeasureTheory NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

noncomputable section

namespace PI.GramFibrationFormulas
section Fin

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def B1 (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (v : HeightOneSpectrum (𝓞 F))
    (x y : Fin M → Fv F v ⊗[F] E) : Fv F v :=
  Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (hR (Fv F v) σ J x y)

end Fin

end PI.GramFibrationFormulas
end
end

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

def FinVolAll : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → FinVolH σ J

def SiegelWeilFibrationFormula : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → Formalism.MainNotions.StandardLattice.SW1a1 F E σ M J

def TgtSW1a2 : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → Formalism.MainNotions.StandardLattice.SW1a2 F E σ M J

def SiegelWeilFiniteVolumeCase : Prop := FinVolAll → RationalPointsLattice → IsotropicLatticeCount → SiegelWeilFibrationFormula ∧ TgtSW1a2

end PI.GramFibrationFormulas
end
end
