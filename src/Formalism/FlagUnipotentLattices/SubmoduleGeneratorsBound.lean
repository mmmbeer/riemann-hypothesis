import Formalism.FlagUnipotentLattices.CardSubmodulesAndLinearEquivBounds

open Module Matrix
open scoped BigOperators ComplexConjugate

noncomputable section

namespace Formalism.HermitianLatticeCounting.LatticeSumBounds

def SubmoduleGeneratorsBound : Prop :=
  ∀ (R M : Type) [CommRing R] [IsDedekindDomain R] [AddCommGroup M] [Module R M] [Finite M] (e : ℕ)
    (v : Fin e → M), Submodule.span R (Set.range v) = ⊤ →
    ∀ N : Submodule R M, ∃ t : Fin e → M, Submodule.span R (Set.range t) = N

def CoveringO' : Prop :=
  ∀ (E : Type) [Field E] [NumberField E], (∀ w : NumberField.InfinitePlace E, w.IsComplex) →
    ∀ x : NumberField.InfinitePlace E → ℂ, ∃ a : NumberField.RingOfIntegers E,
      ∀ w, ‖x w - w.embedding (a : E)‖ ≤
        Real.sqrt ((finrank ℚ E : ℝ) / 2) / 2 * |(NumberField.discr E : ℝ)| ^ (1 / (finrank ℚ E : ℝ))

def RhoBound : Prop :=
  ∀ (f : ℕ) (rd b : ℝ), 1 ≤ b → (f : ℝ) ≤ b → 0 ≤ rd → rd ≤ b →
    max 1 (Real.sqrt f * rd / 2) ≤ b ^ 2

end Formalism.HermitianLatticeCounting.LatticeSumBounds
