import ReciprocityTheory.GaloisValuations.ContinuousConstSMulQuotient

noncomputable section

open Representation ReciprocityTheory.Gal

namespace Formalism.GaloisCohomology

def DevTorsion : Prop := ∀ (R : Type) [CommRing R] (A B C : Type) [AddCommGroup A] [Module R A]
  [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C] (f : A →ₗ[R] B) (g : B →ₗ[R] C)
  (ϖ : R) (c' c'' : ℕ), Function.Exact f g →
  (∀ a, f a = 0 → ∃ k : ℕ, ϖ ^ k • a = 0) →
  (∀ a : A, (∃ k : ℕ, ϖ ^ k • a = 0) → ϖ ^ c' • a = 0) →
  (∀ c : C, (∃ k : ℕ, ϖ ^ k • c = 0) → ϖ ^ c'' • c = 0) →
  ∀ b : B, (∃ k : ℕ, ϖ ^ k • b = 0) → ϖ ^ (c' + c'') • b = 0

end Formalism.GaloisCohomology
