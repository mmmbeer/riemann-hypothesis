import Mathlib
import Formalism.PeriodIntegrals.ClassNumImQ

open NumberField

namespace PI.ClassNumImQ.ZetaNonvanishing₂

noncomputable def cnt (K : Type) [Field K] [NumberField K] (n : ℕ) : ℕ :=
  Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n}

def CntMul : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (m n : ℕ), m.Coprime n →
    cnt K (m * n) = cnt K m * cnt K n

end PI.ClassNumImQ.ZetaNonvanishing₂
