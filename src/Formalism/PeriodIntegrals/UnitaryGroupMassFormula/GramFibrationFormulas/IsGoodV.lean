import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice

open scoped TensorProduct ENNReal
open MeasureTheory NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

noncomputable section

namespace PI.GramFibrationFormulas
section Loc

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

def FreeT {M n : ℕ} (X : Fin n → Fin M → R ⊗[F] E) : Prop := LinearIndependent (R ⊗[F] E) X

def latE {d : ℕ} [NumberField F] (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) :
    Set (Fv F v ⊗[F] E) :=
  {z | ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr z k ∈ v.adicCompletionIntegers F}

def latW {d M : ℕ} [NumberField F] (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) :
    Set (Fin M → Fv F v ⊗[F] E) :=
  {y | ∀ i, y i ∈ latE b v}

def IsGoodV {d M : ℕ} [NumberField F] (b : Module.Basis (Fin d) F E) (σ : E →ₐ[F] E)
    (J : Matrix (Fin M) (Fin M) E) (v : HeightOneSpectrum (𝓞 F)) (χ : Fv F v → ℂ) : Prop :=
  Valued.v (2 : Fv F v) = 1 ∧
  (∀ x ∈ v.adicCompletionIntegers F, χ x = 1) ∧
  (∀ y : Fv F v, (∀ x ∈ v.adicCompletionIntegers F, χ (y * x) = 1) → y ∈ v.adicCompletionIntegers F) ∧
  (1 ∈ latE b v ∧ (∀ z ∈ latE b v, ∀ w ∈ latE b v, z * w ∈ latE b v) ∧
    ∀ z ∈ latE b v, sigR (Fv F v) σ z ∈ latE b v) ∧
  (∀ y : Fv F v ⊗[F] E, (∀ z ∈ latE b v, Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (y * z) ∈
      v.adicCompletionIntegers F) → y ∈ latE b v) ∧
  ∀ y : Fin M → Fv F v ⊗[F] E, (∀ x ∈ latW (M := M) b v, hR (Fv F v) σ J x y ∈ latE b v) ↔ y ∈ latW b v

end Loc

end PI.GramFibrationFormulas
