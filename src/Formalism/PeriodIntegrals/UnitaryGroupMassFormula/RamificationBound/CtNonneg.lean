import Mathlib
import Formalism.PeriodIntegrals.RamBound

open Finset MvPolynomial PI.RamBound

noncomputable section

namespace PI.RamBoundW

abbrev Fr (nH r0 : ℕ) : Type := MvPolynomial (FrV nH r0) ℤ

def CtNonneg : Prop :=
  ∀ (nH r0 rb : ℕ) (TT : Finset (Fin nH)) (nu : Wt nH),
    (∀ t, IsPart r0 (nu t)) → r0 ≤ rb → ∀ t, 0 ≤ ct rb TT nu t

end PI.RamBoundW
