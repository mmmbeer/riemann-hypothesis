import Mathlib

open NumberField

namespace KStar.Choice

def SplitsCompletely (E : Type*) [Field E] [NumberField E] (p : ℕ) : Prop :=
  ∀ P : Ideal (𝓞 E), P.IsPrime → P.LiesOver (Ideal.span {(p : ℤ)}) →
    P.ramificationIdx ℤ = 1 ∧ P.inertiaDeg ℤ = 1










end KStar.Choice
