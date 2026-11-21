import Formalism.MahlerMeasure.Statement

namespace Formalism.GM

open Finset Polynomial

def MahlerDisc : Prop :=
  ∀ (p k i : ℕ) (t₀ : ℤ), p.Prime → i ≤ p ^ k →
    ∀ n : ℕ, padicNorm p
      ((Polynomial.C ((i.factorial : ℚ)⁻¹) *
        (descPochhammer ℚ i).comp (Polynomial.C ((p : ℚ) ^ k) * X + Polynomial.C (t₀ : ℚ))).coeff n) ≤ 1

end Formalism.GM
