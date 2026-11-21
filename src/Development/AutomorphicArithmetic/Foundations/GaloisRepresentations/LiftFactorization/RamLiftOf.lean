import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.ThreeApartOf
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.RamDefs
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp

section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp GlobalTheory.GalCut GlobalTheory.RealGal GlobalTheory.UnitaryBC UpperTheory.V.Published UpperTheory.Gal.UnramifiedFromSplittingCriterion UpperTheory.ConvolutionTheory.Sph

namespace UpperTheory.Gal.AbelianGaloisNormality

def FieldOK (l : ℕ) (E : Type) [Field E] [NumberField E] [IsCMField E] : Prop :=
  (∃ x : E, ∃ d : ℕ, 0 < d ∧ x ^ 2 = -(d : E)) ∧ Even (Module.finrank ℚ (maximalRealSubfield E)) ∧
    (∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) ∧
    (∀ w : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → IsSplitAt w) ∧
    ∃ w₁ w₂ w₃ : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ w₁.asIdeal ∧ ((l : ℕ) : 𝓞 E) ∈ w₂.asIdeal ∧
      ((l : ℕ) : 𝓞 E) ∈ w₃.asIdeal ∧ GlobalTheory.Cong.Apart w₁ w₂ ∧ GlobalTheory.Cong.Apart w₁ w₃ ∧ GlobalTheory.Cong.Apart w₂ w₃

inductive Layers (Ω : Type) [Field Ω] (E : Type) [Field E] [NumberField E] [Algebra E Ω] :
    ∀ (M : Type) [Field M] [NumberField M] [Algebra M Ω] [Algebra E M], Prop
  | refl : Layers Ω E E
  | step (X Y : Type) [Field X] [NumberField X] [Algebra X Ω] [Algebra E X] [Field Y] [NumberField Y] [IsCMField Y] [Algebra Y Ω]
      [Algebra E Y] [Algebra X Y] [IsScalarTower E X Y] [IsScalarTower X Y Ω] :
      Layers Ω E X → IsGalois X Y → (Module.finrank X Y).Prime → Layers Ω E Y

abbrev Rel (a : ℕ) : Type 1 :=
  ∀ (K M : Type) [Field K] [NumberField K] [IsCMField K] [Field M] [NumberField M] [IsCMField M] [Algebra K M],
    CuspSub K a → CuspSub M a → Prop

structure Rel.Tower {a : ℕ} (R : Rel a) : Prop where
  refl : ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] (π : CuspSub K a), R K K π π
  layer : ∀ (K M : Type) [Field K] [NumberField K] [IsCMField K] [Field M] [NumberField M] [IsCMField M] [Algebra K M]
    [IsGalois K M], (Module.finrank K M).Prime → ∀ (π : CuspSub K a) (P : CuspSub M a), IsLiftUnr π P → R K M π P
  trans : ∀ (K M L : Type) [Field K] [NumberField K] [IsCMField K] [Field M] [NumberField M] [IsCMField M] [Field L] [NumberField L]
    [IsCMField L] [Algebra K M] [Algebra M L] [Algebra K L] [IsScalarTower K M L] (π : CuspSub K a) (P : CuspSub M a)
    (U : CuspSub L a), R K M π P → R M L P U → R K L π U

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a l : ℕ} {π : CuspSub E a}

end

end UpperTheory.Gal.AbelianGaloisNormality
end
end

section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp GlobalTheory.GalCut GlobalTheory.RealGal GlobalTheory.UnitaryBC UpperTheory.V.Published UpperTheory.Gal.UnramifiedFromSplittingCriterion UpperTheory.ConvolutionTheory.Sph

namespace UpperTheory.Gal.AbelianGaloisNormality

def StrongOf : Prop := LiftUnr → RamSph → GlobalTheory.Published.ArthurClozelStrongTC

end UpperTheory.Gal.AbelianGaloisNormality
end
end
