import Mathlib

namespace Formalism.SL.LF

open scoped NumberField
open NumberField InfinitePlace Finset

def PrimesOver : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (p : ℕ), p.Prime →
    {P : Ideal (𝓞 K) | P.IsPrime ∧ ((p : ℤ) : 𝓞 K) ∈ P}.Finite ∧
    {P : Ideal (𝓞 K) | P.IsPrime ∧ ((p : ℤ) : 𝓞 K) ∈ P}.ncard ≤ Module.finrank ℚ K

end Formalism.SL.LF
