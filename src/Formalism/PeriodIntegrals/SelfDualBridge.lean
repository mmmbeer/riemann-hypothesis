import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

noncomputable section

namespace PI.SelfDualBridge

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct Classical

section Meas

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F))

def IsStdChar (ψ : AddChar (AF F) ℂ) : Prop :=
  ∀ x : Ainf F, psiInf F ψ x =
    Complex.exp (2 * Real.pi * Complex.I *
      ((∑ w : NumberField.InfinitePlace F, (NumberField.InfinitePlace.Completion.extensionEmbedding w (x w)).re : ℝ) : ℂ))

def StdHyp : Prop := IsCMExt F E σ ∧ IsHermND σ J ∧ IsCharAF F ψ ∧ IsStdChar ψ

def SdExists (a : ℕ) (ι : Type) [Fintype ι] : Prop :=
  StdHyp σ J ψ → (∃ μ, SdW F E σ n J (Fv F v) (psiV F ψ v) a μ) ∧ (∃ ν, SdHerm F E σ (Fv F v) (psiV F ψ v) a ν) ∧
  ∃ μ : Measure (ι → Fv F v ⊗[F] E), SelfDual μ
      (fun x y => psiV F ψ v (∑ i, Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (x i * y i)))

end Meas

end PI.SelfDualBridge
