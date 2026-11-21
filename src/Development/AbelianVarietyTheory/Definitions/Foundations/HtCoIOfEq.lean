import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsEqSubOfMemCob

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2

namespace GlobalTheory.LambdaValuationPowers

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

def FixIc (c : Coef l) (a : Qbar l) : Prop :=
  ∀ σ : Qbar l ≃ₐ[ℚ_[l]] Qbar l, (∀ b ∈ c.O, σ b = b) → (∀ x : Qbar l, ‖x‖ ≤ 1 → ‖σ x - x‖ < 1) → σ a = a

end GlobalTheory.LambdaValuationPowers
