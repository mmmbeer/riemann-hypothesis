import Mathlib
import Formalism.PeriodIntegrals.RayBoundIQ

open NumberField

namespace PI.RayBoundIQW

def rayRel (K0 : Type) [Field K0] [NumberField K0] (qq : Ideal (𝓞 K0))
    (I J : {I : Ideal (𝓞 K0) // I ≠ ⊥ ∧ I ⊔ qq = ⊤}) : Prop :=
  ∃ a b : 𝓞 K0, a ≠ 0 ∧ b ≠ 0 ∧ a - 1 ∈ qq ∧ b - 1 ∈ qq ∧
    (∀ σ : K0 →+* ℝ, 0 < σ (a : K0) ∧ 0 < σ (b : K0)) ∧
    Ideal.span {a} * I.1 = Ideal.span {b} * J.1

end PI.RayBoundIQW
