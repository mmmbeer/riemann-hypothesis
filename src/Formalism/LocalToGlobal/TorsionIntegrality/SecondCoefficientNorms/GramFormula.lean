import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.IsotropicVanish

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.C

def GramFormula : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (l linv ph : PowerSeries K),
    Frame R l linv ph →
    ∀ (O : Type) [CommRing O] [StarRing O] (τ : O →+* K),
    (∀ α, EndInt R l linv (τ α)) →
    (∀ z : O, star z = z → IsBinomScalar R (τ z)) →
    F1 R l linv ph →
    (∀ α : O, PhNormAt R l linv ph (τ α) (τ (star α))) →
    (∀ α : O, AdjAt R l linv ph (τ α) (τ (star α))) →
    ∀ (n : Type) [Fintype n] (k : ℕ) (A : n → Fin k → O)
      (σ : Type) (u : Fin k → MvPowerSeries σ K), (∀ j, IsPt R (u j)) →
      Cong R (∑ i, PowerSeries.subst (flin l linv (fun j => τ (A i j)) u) ph)
        ((∑ j, τ (∑ i, star (A i j) * A i j) • PowerSeries.subst (u j) ph) +
          ∑ j, ∑ j' ∈ Finset.univ.filter (fun j' => j < j'),
            be0 l linv ph (fmul l linv (τ (∑ i, star (A i j') * A i j)) (u j)) (u j'))

end Formalism.L2.Th1.C
