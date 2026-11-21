import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne

noncomputable section

namespace PositivityTheory.Lbc

open Module

section Alg

variable {Λ : Type*} [CommGroup Λ] {W : Type*} [AddCommGroup W] [Module ℂ W]

def genEig (ρ : Representation ℂ Λ W) (χ : Λ →* ℂ) : Submodule ℂ W :=
  ⨅ l : Λ, Module.End.maxGenEigenspace (ρ l) (χ l)

open Classical in

def trOn (B : W →ₗ[ℂ] W) (p : Submodule ℂ W) : ℂ :=
  if h : ∀ x ∈ p, B x ∈ p then LinearMap.trace ℂ p (B.restrict h) else 0

end Alg

def ExponentSeparation : Prop :=
  ∀ (Λ : Type) [CommGroup Λ] (ι : Type) [Fintype ι] (W : ι → Type) [∀ i, AddCommGroup (W i)]
    [∀ i, Module ℂ (W i)] [∀ i, FiniteDimensional ℂ (W i)]
    (ρ : ∀ i, Representation ℂ Λ (W i)) (B : ∀ i, W i →ₗ[ℂ] W i),
    (∀ i l, B i ∘ₗ ρ i l = ρ i l ∘ₗ B i) →
    ∀ (C : Submonoid Λ), (∀ l : Λ, ∃ a ∈ C, ∃ b ∈ C, l = a * b⁻¹) →
    ∀ l₀ : Λ, (∀ c ∈ C, ∑ i, LinearMap.trace ℂ (W i) (B i ∘ₗ ρ i (l₀ * c)) = 0) →
    ∀ χ : Λ →* ℂ, ∑ i, trOn (B i) (genEig (ρ i) χ) = 0

open Classical in

def TwistedTrace : Prop :=
  ∀ (Λ : Type) [CommGroup Λ] (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ Λ W) (θ : Λ ≃* Λ) (A : W →ₗ[ℂ] W),
    (∀ l, A ∘ₗ ρ l = ρ (θ l) ∘ₗ A) →
    ∀ S : Finset (Λ →* ℂ), (∀ χ, genEig ρ χ ≠ ⊥ → χ ∈ S) →
    ∀ l : Λ, LinearMap.trace ℂ W (A ∘ₗ ρ l) =
      ∑ χ ∈ S with χ.comp θ.toMonoidHom = χ, χ l * trOn A (genEig ρ χ)

open GlobalTheory.LocGL

end PositivityTheory.Lbc
