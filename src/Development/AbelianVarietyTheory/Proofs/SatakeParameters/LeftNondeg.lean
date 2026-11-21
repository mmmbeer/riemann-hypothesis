import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition

noncomputable section
open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.PD
open GlobalTheory.EtC

def LeftNondeg (q : ℕ) (E : Spc) (d : ℕ) (n i : ℤ) : Prop :=
  ∀ a : Ht q E n i, a ≠ 0 → ∃ b : Ht q E (2 * d - n) (d - i), cup q a b ≠ 0

end GlobalTheory.PD

end
