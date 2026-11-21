import Mathlib

noncomputable section

open NumberField IsDedekindDomain

namespace HeckeCharacterZeroLocus.ThmBIn

variable {K : Type} [Field K] [NumberField K]

def Kmax (w : HeightOneSpectrum (𝓞 K)) (n : ℕ) : Set (GL (Fin n) (w.adicCompletion K)) :=
  {g | ∀ i j, (g : Matrix (Fin n) (Fin n) (w.adicCompletion K)) i j ∈ w.adicCompletionIntegers K ∧
    ((g⁻¹ : GL (Fin n) (w.adicCompletion K)) : Matrix (Fin n) (Fin n) (w.adicCompletion K)) i j ∈
      w.adicCompletionIntegers K}

def IsCosetRep {G : Type} [Group G] (Kset : Set G) (α : G) (R : Finset G) : Prop :=
  (∀ γ ∈ R, ∃ k₁ ∈ Kset, ∃ k₂ ∈ Kset, γ = k₁ * α * k₂) ∧
    ∀ x : G, (∃ k₁ ∈ Kset, ∃ k₂ ∈ Kset, x = k₁ * α * k₂) → ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ Kset

end HeckeCharacterZeroLocus.ThmBIn

end
